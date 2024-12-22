#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include <iostream>
#include <map>
#include <memory>
#include <sstream>
#include <vector>
using namespace std;
using namespace llvm;
// #define _T_
static unique_ptr<LLVMContext> TheContext;
static unique_ptr<IRBuilder<>> Builder;
static unique_ptr<Module> TheModule;
static map<string, Value *> NamedValues;

enum
{
    tok_eof = -1,
    tok_def = -2,
    tok_extern = -3,
    tok_identifier = -4,
    tok_number = -5,
};

static string IdentifierStr;
static double NumVal;

const char DebugGetChar()
{
#ifndef _T_
    return getchar();
#else
    return cin.get();
#endif
}

static int gettok()
{
    static char LastChar = ' ';
    while (isspace(LastChar))
        LastChar = DebugGetChar();
    if (isalpha(LastChar))
    {
        IdentifierStr = LastChar;
        while (isalnum(LastChar = DebugGetChar()))
        {
            IdentifierStr += LastChar;
        }
#ifdef _T_
        fprintf(stderr, "IdentifierStr=%s\n", IdentifierStr.c_str());
#endif
        if (IdentifierStr == "def")
            return tok_def;
        if (IdentifierStr == "extern")
            return tok_extern;
        return tok_identifier;
    }

    if (isdigit(LastChar) || LastChar == '.')
    {
        string NumStr;
        do
        {
            NumStr += LastChar;
            LastChar = DebugGetChar();
        } while (isdigit(LastChar) || LastChar == '.');
        NumVal = strtod(NumStr.c_str(), 0);
#ifdef _T_
        fprintf(stderr, "NumVal=%lf\n", NumVal);
#endif
        return tok_number;
    }

    if (LastChar == '#')
    {
#ifdef _T_
        fprintf(stderr, "Now reading comments...\n");
#endif
        do
        {
            LastChar = DebugGetChar();
        } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');
        if (LastChar != EOF)
        {
            return gettok();
        }
    }
    if (LastChar == EOF)
        return tok_eof;
    int ThisChar = LastChar;
    LastChar = DebugGetChar();
#ifdef _T_
    fprintf(stderr, "ThisChar=%c\n", ThisChar);
#endif
    return ThisChar;
}

Value *LogErrorV(const char *Str);

namespace
{
class ExprAST
{
  public:
    virtual ~ExprAST() = default;
    virtual Value *codegen() = 0;
};

class NumberExprAST : public ExprAST
{
    double Val;

  public:
    NumberExprAST(double val) : Val(val) {};
    Value *codegen()
    {
        return ConstantFP::get(*TheContext, APFloat(Val));
    };
};

class VariableExprAST : public ExprAST
{
    string Name;

  public:
    VariableExprAST(const string &name) : Name(name) {};
    Value *codegen()
    {
        Value *V = NamedValues[Name];
        if (!V)
            LogErrorV("Unknown variable name");
        return V;
    }
};

class BinaryExprAST : public ExprAST
{
    char Op;
    unique_ptr<ExprAST> LHS, RHS;

  public:
    BinaryExprAST(char op, unique_ptr<ExprAST> lhs, unique_ptr<ExprAST> rhs)
        : Op(op), LHS(std::move(lhs)), RHS(std::move(rhs)) {};
    Value *codegen()
    {
        Value *L = LHS->codegen();
        Value *R = RHS->codegen();
        if (!L || !R)
            return nullptr;
        switch (Op)
        {
        case '+':
            return Builder->CreateFAdd(L, R, "addtmp");
        case '-':
            return Builder->CreateFSub(L, R, "subtmp");
        case '*':
            return Builder->CreateFMul(L, R, "multmp");
        case '<':
            L = Builder->CreateFCmpULT(L, R, "cmptmp");
            return Builder->CreateUIToFP(L, Type::getDoubleTy(*TheContext), "booltmp");
        default:
            return LogErrorV("invalid binary operator");
        }
    }
};

class CallExprAST : public ExprAST
{
    string Callee;
    vector<unique_ptr<ExprAST>> Args;

  public:
    CallExprAST(const string &callee, vector<unique_ptr<ExprAST>> args) : Callee(callee), Args(std::move(args)) {};
    Value *codegen()
    {
        Function *CalleeF = TheModule->getFunction(Callee);
        if (!CalleeF)
            return LogErrorV("Unknown function referenced");
        if (CalleeF->arg_size() != Args.size())
            return LogErrorV("Incorrect # arguments passed");
        vector<Value *> ArgsV;
        for (unsigned i = 0, e = Args.size(); i != e; i++)
        {
            ArgsV.push_back(Args[i]->codegen());
            if (!ArgsV.back())
                return nullptr;
        }
        return Builder->CreateCall(CalleeF, ArgsV, "calltmp");
    }
};

class PrototypeAST : public ExprAST
{
    string Name;
    vector<string> Args;
    vector<llvm::Type *> ArgsType;

  public:
    PrototypeAST(const string &name, vector<string> args) : Name(name), Args(args) {};
    const string &getName() const
    {
        return Name;
    }
    const vector<string> &getArgs() const
    {
        return Args;
    }
    // This getType() function is reserved cause I can't solve this for now!!! - 20241221
    llvm::Type *getType(const int index) const
    {
        return ArgsType[index];
    }
    Function *codegen()
    {
        vector<Type *> Doubles(Args.size(), Type::getDoubleTy(*TheContext));
        FunctionType *FT = FunctionType::get(Type::getDoubleTy(*TheContext), Doubles, false);
        Function *F = Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());
        unsigned Idx = 0;
        for (auto &Arg : F->args())
            Arg.setName(Args[Idx++]);
        return F;
    }
};

class FunctionExprAST : public ExprAST
{
    unique_ptr<PrototypeAST> Proto;
    unique_ptr<ExprAST> Body;

  public:
    FunctionExprAST(unique_ptr<PrototypeAST> proto, unique_ptr<ExprAST> body)
        : Proto(std::move(proto)), Body(std::move(body)) {};
    Function *codegen()
    {
        Function *TheFunction = TheModule->getFunction(Proto->getName());
        if (!TheFunction)
        {
            TheFunction = Proto->codegen();
        }
        else
        {
            if (TheFunction->arg_size() != Proto->getArgs().size())
            {
                cerr << "Error: Function " << Proto->getName() << " argument mismatch!\n";
                return nullptr;
            }
            // Reserved Part, cause all arguments are in Double type!
            // else
            // {
            //     for (unsigned i = 0; i < TheFunction->arg_size(); i++)
            //     {
            //         if (TheFunction->getArg(i)->getType() != Proto->getType(i))
            //         {
            //             cerr << "Error: Function " << Proto->getName() << " argument mismatch at position " << i
            //                  << "!\n";
            //             return nullptr;
            //         }
            //     }
            // }
        }

        if (!TheFunction)
            return nullptr;
        if (!TheFunction->empty())
            return (Function *)LogErrorV("Function cannot be redefined.");
        BasicBlock *BB = BasicBlock::Create(*TheContext, "entry", TheFunction);
        Builder->SetInsertPoint(BB);
        NamedValues.clear();
        for (auto &Arg : TheFunction->args())
            NamedValues[string(Arg.getName())] = &Arg;
        if (Value *RetVal = Body->codegen())
        {
            Builder->CreateRet(RetVal);
            verifyFunction(*TheFunction);

            return TheFunction;
        }
        TheFunction->eraseFromParent();
        return nullptr;
    }
};
}; // namespace

static int CurTok;

unique_ptr<const char *> TokName()
{
    switch (CurTok)
    {
    case tok_eof:
        return make_unique<const char *>("tok_eof");
    case tok_def:
        return make_unique<const char *>("tok_def");
    case tok_extern:
        return make_unique<const char *>("tok_extern");
    case tok_identifier:
        return make_unique<const char *>("tok_idenifier");
    case tok_number:
        return make_unique<const char *>("tok_number");
    default:
        return make_unique<const char *>("tok_operator");
    }
    return nullptr;
}

static int getNextToken()
{
    CurTok = gettok();
#ifdef _T_
    fprintf(stderr, "CurTok=%s\n", *TokName());
    fprintf(stderr, "*========================*\n");
#endif
    return CurTok;
}

static map<char, int> BinopPrecedence;

static int GetTokPrecedence()
{
    if (!isascii(CurTok))
        return -1;
    int TokPrec = BinopPrecedence[CurTok];
    if (TokPrec <= 0)
        return -1;
    return TokPrec;
}

unique_ptr<ExprAST> LogError(const char *Str)
{
    fprintf(stderr, "Error: %s\n", Str);
    return nullptr;
}

unique_ptr<PrototypeAST> LogErrorP(const char *Str)
{
    LogError(Str);
    return nullptr;
}

Value *LogErrorV(const char *Str)
{
    LogError(Str);
    return nullptr;
}

static unique_ptr<ExprAST> ParseExpression();

static unique_ptr<ExprAST> ParseNumberExpr()
{
    auto Result = make_unique<NumberExprAST>(NumVal);
    getNextToken();
    return std::move(Result);
}

static unique_ptr<ExprAST> ParseParenExpr()
{
    getNextToken();
    auto V = ParseExpression();
    if (!V)
        return nullptr;
    if (CurTok != ')')
        return LogError("expected ')'");
    getNextToken();
    return V;
}

static unique_ptr<ExprAST> ParseIdentifierExpr()
{
    string IdName = IdentifierStr;
    getNextToken();
    if (CurTok != '(')
        return make_unique<VariableExprAST>(IdName);

    getNextToken();
    vector<unique_ptr<ExprAST>> Args;
    if (CurTok != ')')
    {
        while (1)
        {
            if (auto Arg = ParseExpression())
                Args.emplace_back(std::move(Arg));
            else
                return nullptr;

            if (CurTok == ')')
                break;
            if (CurTok != ',')
                return LogError("Expected ')' or ',' in argument list");
            getNextToken();
        }
    }
    getNextToken();
    return make_unique<CallExprAST>(IdName, std::move(Args));
}

static unique_ptr<ExprAST> ParsePrimary()
{
    switch (CurTok)
    {
    default:
        return LogError("Unknown token when expectinng an expression");
    case tok_identifier:
        return ParseIdentifierExpr();
    case tok_number:
        return ParseNumberExpr();
    case '(':
        return ParseParenExpr();
    }
}

static unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec, unique_ptr<ExprAST> LHS)
{
    while (1)
    {
        int TokPrec = GetTokPrecedence();
        if (TokPrec < ExprPrec)
            return LHS;
        int BinOp = CurTok;
        getNextToken();

        auto RHS = ParsePrimary();
        if (!RHS)
            return nullptr;
        int NextPrec = GetTokPrecedence();
        if (TokPrec < NextPrec)
        {
            RHS = ParseBinOpRHS(TokPrec + 1, std::move(RHS));
            if (!RHS)
                return nullptr;
        }
        LHS = make_unique<BinaryExprAST>(BinOp, std::move(LHS), std::move(RHS));
    }
}

static unique_ptr<ExprAST> ParseExpression()
{
    auto LHS = ParsePrimary();
    if (!LHS)
        return nullptr;
    return ParseBinOpRHS(0, std::move(LHS));
};

static unique_ptr<PrototypeAST> ParsePrototype()
{
    if (CurTok != tok_identifier)
        return LogErrorP("Expected function name in prototype");
    string FnName = IdentifierStr;
    getNextToken();

    if (CurTok != '(')
        return LogErrorP("Expected '(' in prototype");
    vector<string> ArgNames;
    while (getNextToken() == tok_identifier)
        ArgNames.emplace_back(IdentifierStr);
    if (CurTok != ')')
        return LogErrorP("Expected ')' in prototype");
    getNextToken();
    return make_unique<PrototypeAST>(FnName, std::move(ArgNames));
}

static unique_ptr<FunctionExprAST> ParseDefinition()
{
    getNextToken();
    auto Proto = ParsePrototype();
    if (!Proto)
        return nullptr;
    if (auto E = ParseExpression())
        return make_unique<FunctionExprAST>(std::move(Proto), std::move(E));
    return nullptr;
}

static unique_ptr<PrototypeAST> ParseExtern()
{
    getNextToken();
    return ParsePrototype();
}

static unique_ptr<FunctionExprAST> ParseTopLevelExpr()
{
    if (auto E = ParseExpression())
    {
        auto Proto = make_unique<PrototypeAST>("", vector<string>());
        return make_unique<FunctionExprAST>(std::move(Proto), std::move(E));
    }
    return nullptr;
}

static void InitializeModule()
{
    TheContext = make_unique<LLVMContext>();
    TheModule = make_unique<Module>("my cool jit", *TheContext);
    Builder = make_unique<IRBuilder<>>(*TheContext);
}

static void HandleDefinition()
{
    if (auto FnAST = ParseDefinition())
    {
        if (auto *FnIR = FnAST->codegen())
        {
            fprintf(stderr, "Read function definition:\n");
            FnIR->print(errs());
            fprintf(stderr, "\n");
        }
    }
    else
        getNextToken();
}

static void HandleExtern()
{
    if (auto ProtoAST = ParseExtern())
    {
        if (auto *FnIR = ProtoAST->codegen())
        {
            fprintf(stderr, "Read extern:\n");
            FnIR->print(errs());
            fprintf(stderr, "\n");
        }
    }
    else
        getNextToken();
}

static void HandleTopLevelExpression()
{
    if (auto FnAST = ParseTopLevelExpr())
    {
        if (auto *FnIR = FnAST->codegen())
        {
            fprintf(stderr, "Read top-level expression:\n");
            FnIR->print(errs());
            fprintf(stderr, "\n");

            FnIR->eraseFromParent();
        }
    }
    else
        getNextToken();
}

static void MainLoop()
{
    while (1)
    {
        fprintf(stderr, "ready> ");
        switch (CurTok)
        {
        case tok_eof:
            return;
        case ';':
            getNextToken();
            break;
        case tok_def:
            HandleDefinition();
            break;
        case tok_extern:
            HandleExtern();
            break;
        default:
            HandleTopLevelExpression();
            break;
        }
    }
}

int main(int argc, char const *argv[])
{
    BinopPrecedence['<'] = 10;
    BinopPrecedence['+'] = 20;
    BinopPrecedence['-'] = 20;
    BinopPrecedence['*'] = 40;
    fprintf(stderr, "ready> ");
#ifdef _T_
    stringstream testInput("4+5*a-(6-b);");
    cin.rdbuf(testInput.rdbuf());
#endif
    getNextToken();
    InitializeModule();
    MainLoop();
    TheModule->print(errs(), nullptr);
    return 0;
}
