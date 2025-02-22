#include "../include/KaleidoscopeJIT.h"
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
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/StandardInstrumentations.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/Reassociate.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include <iostream>
#include <map>
#include <memory>
#include <sstream>
#include <vector>
using namespace std;
using namespace llvm;
using namespace llvm::orc;
// #define _T_

static unique_ptr<LLVMContext> TheContext;
static unique_ptr<IRBuilder<>> Builder;
static unique_ptr<Module> TheModule;
static map<string, AllocaInst *> NamedValues;
static unique_ptr<KaleidoscopeJIT> TheJIT;
static unique_ptr<FunctionPassManager> TheFPM;
static unique_ptr<LoopAnalysisManager> TheLAM;
static unique_ptr<FunctionAnalysisManager> TheFAM;
static unique_ptr<CGSCCAnalysisManager> TheCGAM;
static unique_ptr<ModuleAnalysisManager> TheMAM;
static unique_ptr<PassInstrumentationCallbacks> ThePIC;
static unique_ptr<StandardInstrumentations> TheSI;
static ExitOnError ExitOnErr;

enum
{
    tok_eof = -1,
    tok_def = -2,
    tok_extern = -3,
    tok_identifier = -4,
    tok_number = -5,
    tok_if = -6,
    tok_then = -7,
    tok_else = -8,
    tok_for = -9,
    tok_in = -10,
    tok_binary = -11,
    tok_unary = -12,
    tok_var = -13,
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
        if (IdentifierStr == "if")
            return tok_if;
        if (IdentifierStr == "then")
            return tok_then;
        if (IdentifierStr == "else")
            return tok_else;
        if (IdentifierStr == "for")
            return tok_for;
        if (IdentifierStr == "in")
            return tok_in;
        if (IdentifierStr == "binary")
            return tok_binary;
        if (IdentifierStr == "unary")
            return tok_unary;
        if (IdentifierStr == "var")
            return tok_var;
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
Function *getFunction(string Name);
static map<char, int> BinopPrecedence;
static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction, StringRef VarName)
{
    IRBuilder<> TmpB(&TheFunction->getEntryBlock(), TheFunction->getEntryBlock().begin());
    return TmpB.CreateAlloca(Type::getDoubleTy(*TheContext), nullptr, VarName);
}

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
        AllocaInst *A = NamedValues[Name];
        if (!A)
            LogErrorV("Unknown variable name");
        return Builder->CreateLoad(A->getAllocatedType(), A, Name.c_str());
    }
    const string &getName() const
    {
        return Name;
    }
};

class UnaryExprAST : public ExprAST
{
    char Opcode;
    unique_ptr<ExprAST> Operand;

  public:
    UnaryExprAST(char _Opcode, unique_ptr<ExprAST> _Operand) : Opcode(_Opcode), Operand(std::move(_Operand))
    {
    }
    Value *codegen()
    {
        Value *OperandV = Operand->codegen();
        if (!OperandV)
            return nullptr;
        Function *F = getFunction(string("unary") + Opcode);
        if (!F)
            return LogErrorV("Unknown unary operator");
        return Builder->CreateCall(F, OperandV, "unop");
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
        if (Op == '=')
        {
            VariableExprAST *LHSE = static_cast<VariableExprAST *>(LHS.get());
            if (!LHSE)
                return LogErrorV("destination of '=' must be a variable");
            Value *Val = RHS->codegen();
            if (!Val)
                return nullptr;
            Value *Variable = NamedValues[LHSE->getName()];
            if (!Variable)
                return LogErrorV("Unknown variable name");

            Builder->CreateStore(Val, Variable);
            return Val;
        }
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
            // return LogErrorV("invalid binary operator");
            break;
        }
        Function *F = getFunction(string("binary") + Op);
        assert(F && "binary operator not found!");

        Value *Ops[2] = {L, R};
        return Builder->CreateCall(F, Ops, "binop");
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
        Function *CalleeF = getFunction(Callee);
        if (!CalleeF)
            return LogErrorV("Unknown function referenced");
        if (CalleeF->arg_size() != Args.size())
            return LogErrorV("Incorrect # arguments passed");
        vector<Value *> ArgsV;
        for (unsigned i = 0, e = Args.size(); i != e; i++)
        {
            ArgsV.emplace_back(Args[i]->codegen());
            if (!ArgsV.back())
                return nullptr;
        }
        return Builder->CreateCall(CalleeF, ArgsV, "calltmp");
    }
};

class IfExprAST : public ExprAST
{
    unique_ptr<ExprAST> Cond, Then, Else;

  public:
    IfExprAST(unique_ptr<ExprAST> cond, unique_ptr<ExprAST> then, unique_ptr<ExprAST> ELse)
        : Cond(std::move(cond)), Then(std::move(then)), Else(std::move(ELse)) {};
    Value *codegen()
    {
        Value *CondV = Cond->codegen();
        if (!CondV)
            return nullptr;
        CondV = Builder->CreateFCmpONE(CondV, ConstantFP::get(*TheContext, APFloat(0.0)), "ifcond");

        Function *TheFunction = Builder->GetInsertBlock()->getParent();
        BasicBlock *ThenBB = BasicBlock::Create(*TheContext, "then", TheFunction);
        BasicBlock *ELseBB = BasicBlock::Create(*TheContext, "else");
        BasicBlock *MergeBB = BasicBlock::Create(*TheContext, "ifcont");
        Builder->CreateCondBr(CondV, ThenBB, ELseBB);

        Builder->SetInsertPoint(ThenBB);
        Value *ThenV = Then->codegen();
        if (!ThenV)
            return nullptr;
        Builder->CreateBr(MergeBB);
        ThenBB = Builder->GetInsertBlock();
        TheFunction->insert(TheFunction->end(), ELseBB);
        Builder->SetInsertPoint(ELseBB);

        Value *ELseV = Else->codegen();
        if (!ELseV)
            return nullptr;
        Builder->CreateBr(MergeBB);
        ELseBB = Builder->GetInsertBlock();

        TheFunction->insert(TheFunction->end(), MergeBB);
        Builder->SetInsertPoint(MergeBB);
        PHINode *PN = Builder->CreatePHI(Type::getDoubleTy(*TheContext), 2, "iftmp");
        PN->addIncoming(ThenV, ThenBB);
        PN->addIncoming(ELseV, ELseBB);
        return PN;
    }
};

class ForExprAST : public ExprAST
{
    string VarName;
    unique_ptr<ExprAST> Start, End, Step, Body;

  public:
    ForExprAST(const string &VarName, unique_ptr<ExprAST> Start, unique_ptr<ExprAST> End, unique_ptr<ExprAST> Step,
               unique_ptr<ExprAST> Body)
        : VarName(VarName), Start(std::move(Start)), End(std::move(End)), Step(std::move(Step)), Body(std::move(Body))
    {
    }
    Value *codegen()
    {
        Function *TheFunction = Builder->GetInsertBlock()->getParent();
        AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, VarName);

        Value *StartVal = Start->codegen();
        if (!StartVal)
            return nullptr;

        Builder->CreateStore(StartVal, Alloca);
        BasicBlock *LoopBB = BasicBlock::Create(*TheContext, "loop", TheFunction);

        Builder->CreateBr(LoopBB);
        Builder->SetInsertPoint(LoopBB);

        AllocaInst *OldVal = NamedValues[VarName];
        NamedValues[VarName] = Alloca;

        if (!Body->codegen())
            return nullptr;

        Value *StepVal = nullptr;
        if (Step)
        {
            StepVal = Step->codegen();
            if (!StepVal)
                return nullptr;
        }
        else
        {
            StepVal = ConstantFP::get(*TheContext, APFloat(1.0));
        }
        Value *EndCond = End->codegen();
        if (!EndCond)
            return nullptr;

        Value *CurVar = Builder->CreateLoad(Alloca->getAllocatedType(), Alloca, VarName.c_str());
        Value *NextVar = Builder->CreateFAdd(CurVar, StepVal, "nextvar");
        Builder->CreateStore(NextVar, Alloca);

        EndCond = Builder->CreateFCmpONE(EndCond, ConstantFP::get(*TheContext, APFloat(0.0)), "loopcond");

        BasicBlock *LoopEndBB = Builder->GetInsertBlock();
        BasicBlock *AfterBB = BasicBlock::Create(*TheContext, "after loop", TheFunction);

        Builder->CreateCondBr(EndCond, LoopBB, AfterBB);
        Builder->SetInsertPoint(AfterBB);

        if (OldVal)
            NamedValues[VarName] = OldVal;
        else
            NamedValues.erase(VarName);

        return ConstantFP::getNullValue(Type::getDoubleTy(*TheContext));
    }
};

class VarExprAST : public ExprAST
{
    vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames;
    unique_ptr<ExprAST> Body;

  public:
    VarExprAST(vector<pair<string, unique_ptr<ExprAST>>> VarNames, unique_ptr<ExprAST> Body)
        : VarNames(std::move(VarNames)), Body(std::move(Body))
    {
    }
    Value *codegen()
    {
        vector<AllocaInst *> OldBindings;
        Function *TheFunction = Builder->GetInsertBlock()->getParent();

        for (unsigned i = 0, e = VarNames.size(); i != e; i++)
        {
            const string &VarName = VarNames[i].first;
            ExprAST *Init = VarNames[i].second.get();
            Value *InitVal;
            if (Init)
            {
                InitVal = Init->codegen();
                if (InitVal)
                    return nullptr;
            }
            else
                InitVal = ConstantFP::get(*TheContext, APFloat(0.0f));

            AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, VarName);
            Builder->CreateStore(InitVal, Alloca);

            OldBindings.emplace_back(NamedValues[VarName]);
            NamedValues[VarName] = Alloca;
        }

        Value *BodyVal = Body->codegen();
        if (!BodyVal)
            return nullptr;
        for (unsigned i = 0, e = VarNames.size(); i != e; ++i)
            NamedValues[VarNames[i].first] = OldBindings[i];
        return BodyVal;
    }
};

class PrototypeAST
{
    string Name;
    vector<string> Args;
    vector<llvm::Type *> ArgsType;
    bool IsOperator;
    unsigned Precedence;

  public:
    PrototypeAST(const string &name, vector<string> args, bool IsOperator = false, unsigned Prec = 0)
        : Name(name), Args(args), IsOperator(IsOperator), Precedence(Prec) {};
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
    bool isUnaryOp() const
    {
        return IsOperator && Args.size() == 1;
    }
    bool isBinaryOp() const
    {
        return IsOperator && Args.size() == 2;
    }
    char getOperatorName() const
    {
        assert(isUnaryOp() || isBinaryOp());
        return Name[Name.size() - 1];
    }
    unsigned getBinaryPrecedence() const
    {
        return Precedence;
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

class FunctionAST
{
    unique_ptr<PrototypeAST> Proto;
    unique_ptr<ExprAST> Body;

  public:
    FunctionAST(unique_ptr<PrototypeAST> proto, unique_ptr<ExprAST> body)
        : Proto(std::move(proto)), Body(std::move(body)) {};
    Function *codegen();
};

}; // namespace

static int CurTok;
static map<string, unique_ptr<PrototypeAST>> FunctionProtos;

Function *getFunction(string Name)
{
    if (auto *F = TheModule->getFunction(Name))
        return F;
    auto FI = FunctionProtos.find(Name);
    if (FI != FunctionProtos.end())
        return FI->second->codegen();
    return nullptr;
}

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

static unique_ptr<ExprAST> ParseIfExpr();
static unique_ptr<ExprAST> ParseForExpr();

static unique_ptr<ExprAST> ParseVarExpr()
{
    getNextToken();
    vector<pair<string, unique_ptr<ExprAST>>> VarNames;

    if (CurTok != tok_identifier)
        return LogError("expected identifier after var");

    while (1)
    {
        string Name = IdentifierStr;
        getNextToken();
        unique_ptr<ExprAST> Init = nullptr;
        if (CurTok == '=')
        {
            getNextToken();
            Init = ParseExpression();
            if (!Init)
                return nullptr;
        }
        VarNames.emplace_back(make_pair(Name, std::move(Init)));
        if (CurTok != ',')
            break;
        getNextToken();
        if (CurTok != tok_identifier)
            return LogError("expected identifier list after var");
    }
    if (CurTok != tok_in)
        return LogError("expected 'in' keyword after 'var'");
    getNextToken();
    auto Body = ParseExpression();
    if (!Body)
        return nullptr;
    return make_unique<VarExprAST>(std::move(VarNames), std::move(Body));
}

static unique_ptr<ExprAST> ParsePrimary()
{
    switch (CurTok)
    {
        cerr << "ParsePrimary while ct=" << CurTok << endl;
    default:
        return LogError("Unknown token when expectinng an expression");
    case tok_identifier:
        return ParseIdentifierExpr();
    case tok_number:
        return ParseNumberExpr();
    case '(':
        return ParseParenExpr();
    case tok_if:
        return ParseIfExpr();
    case tok_for:
        return ParseForExpr();
    case tok_var:
        return ParseVarExpr();
    }
}

static unique_ptr<ExprAST> ParseUnary()
{
    if (!isascii(CurTok) || CurTok == '(' || CurTok == ',')
        return ParsePrimary();
    int Opc = CurTok;
    getNextToken();
    if (auto Operand = ParseUnary())
        return make_unique<UnaryExprAST>(Opc, std::move(Operand));
    return nullptr;
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

        auto RHS = ParseUnary();
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
    auto LHS = ParseUnary();
    if (!LHS)
        return nullptr;
    return ParseBinOpRHS(0, std::move(LHS));
};

static unique_ptr<PrototypeAST> ParsePrototype()
{
    string FnName;
    unsigned Kind = 0, BinaryPrecedence = 30;

    switch (CurTok)
    {
    default:
        return LogErrorP("Expected function name in prototype");
    case tok_identifier:
        FnName = IdentifierStr;
        Kind = 0;
        getNextToken();
        break;
    case tok_unary:
        getNextToken();
        if (!isascii(CurTok))
            return LogErrorP("Expected unary operator");
        FnName = "unary";
        FnName += (char)CurTok;
        Kind = 1;
        getNextToken();
        break;
    case tok_binary:
        getNextToken();
        if (!isascii(CurTok))
            return LogErrorP("Expected binary operator");
        FnName = "binary";
        FnName += (char)CurTok;
        Kind = 2;
        getNextToken();
        if (CurTok == tok_number)
        {
            if (NumVal < 1 || NumVal > 100)
                return LogErrorP("Invalid precedence: must be 1..100");
            BinaryPrecedence = (unsigned)NumVal;
            getNextToken();
        }
        break;
    }

    if (CurTok != '(')
        return LogErrorP("Expected '(' in prototype");
    vector<string> ArgNames;
    while (getNextToken() == tok_identifier)
        ArgNames.emplace_back(IdentifierStr);
    if (CurTok != ')')
        return LogErrorP("Expected ')' in prototype");
    getNextToken();
    if (Kind && ArgNames.size() != Kind)
        return LogErrorP("Invalid number of operands for operator");
    return make_unique<PrototypeAST>(FnName, std::move(ArgNames), Kind != 0, BinaryPrecedence);
}

static unique_ptr<FunctionAST> ParseDefinition()
{
    getNextToken();
    auto Proto = ParsePrototype();
    if (!Proto)
        return nullptr;
    if (auto E = ParseExpression())
        return make_unique<FunctionAST>(std::move(Proto), std::move(E));
    return nullptr;
}

static unique_ptr<PrototypeAST> ParseExtern()
{
    getNextToken();
    return ParsePrototype();
}

static unique_ptr<FunctionAST> ParseTopLevelExpr()
{
    if (auto E = ParseExpression())
    {
        auto Proto = make_unique<PrototypeAST>("__anon_expr", vector<string>());
        return make_unique<FunctionAST>(std::move(Proto), std::move(E));
    }
    return nullptr;
}

static unique_ptr<ExprAST> ParseIfExpr()
{
    getNextToken();
    auto Cond = ParseExpression();
    if (!Cond)
        return nullptr;
    if (CurTok != tok_then)
    {
        cerr << "CURTOK=" << CurTok << " identistr=" << IdentifierStr << endl;
        return LogError("expected then");
    }
    getNextToken();
    auto Then = ParseExpression();
    if (!Then)
        return nullptr;
    if (CurTok != tok_else)
        return LogError("expected else");
    getNextToken();
    auto ELse = ParseExpression();
    if (!ELse)
        return nullptr;
    return make_unique<IfExprAST>(std::move(Cond), std::move(Then), std::move(ELse));
}

static unique_ptr<ExprAST> ParseForExpr()
{
    getNextToken();
    if (CurTok != tok_identifier)
        return LogError("expected identifier after for");
    string IdName = IdentifierStr;
    getNextToken();
    if (CurTok != '=')
        return LogError("expected '=' after for");
    getNextToken();

    auto Start = ParseExpression();
    if (!Start)
        return nullptr;
    if (CurTok != ',')
        return LogError("expected ',' after for start value");
    getNextToken();

    auto End = ParseExpression();
    if (!End)
        return nullptr;

    unique_ptr<ExprAST> Step;
    if (CurTok == ',')
    {
        getNextToken();
        Step = ParseExpression();
        if (!Step)
            return nullptr;
    }
    if (CurTok != tok_in)
        return LogError("expected 'in' after for");
    getNextToken();
    auto Body = ParseExpression();
    if (!Body)
        return nullptr;
    return make_unique<ForExprAST>(IdName, std::move(Start), std::move(End), std::move(Step), std::move(Body));
}

Function *FunctionAST::codegen()
{
    auto &P = *Proto;
    FunctionProtos[Proto->getName()] = std::move(Proto);
    Function *TheFunction = getFunction(P.getName());
    if (!TheFunction)
        return nullptr;
    if (P.isBinaryOp())
        BinopPrecedence[P.getOperatorName()] = P.getBinaryPrecedence();
    BasicBlock *BB = BasicBlock::Create(*TheContext, "entry", TheFunction);
    Builder->SetInsertPoint(BB);

    NamedValues.clear();
    for (auto &Arg : TheFunction->args())
    {
        AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, Arg.getName());
        Builder->CreateStore(&Arg, Alloca);
        NamedValues[std::string(Arg.getName())] = Alloca;
    }

    if (Value *RetVal = Body->codegen())
    {
        Builder->CreateRet(RetVal);
        verifyFunction(*TheFunction);
        TheFPM->run(*TheFunction, *TheFAM);

        return TheFunction;
    }

    TheFunction->eraseFromParent();

    if (P.isBinaryOp())
        BinopPrecedence.erase(P.getOperatorName());
    return nullptr;
};

static void InitializeModule()
{
    TheContext = make_unique<LLVMContext>();
    TheModule = make_unique<Module>("my cool jit", *TheContext);
    Builder = make_unique<IRBuilder<>>(*TheContext);
}

void InitializeModuleAndManagers()
{
    TheContext = make_unique<LLVMContext>();
    TheModule = make_unique<Module>("KaleidoscopeJIT", *TheContext);
    TheModule->setDataLayout(TheJIT->getDataLayout());
    Builder = make_unique<IRBuilder<>>(*TheContext);

    TheFPM = make_unique<FunctionPassManager>();
    TheLAM = make_unique<LoopAnalysisManager>();
    TheFAM = make_unique<FunctionAnalysisManager>();
    TheCGAM = make_unique<CGSCCAnalysisManager>();
    TheMAM = make_unique<ModuleAnalysisManager>();
    ThePIC = make_unique<PassInstrumentationCallbacks>();
    TheSI = make_unique<StandardInstrumentations>(*TheContext, true);
    TheSI->registerCallbacks(*ThePIC, TheMAM.get());

    TheFPM->addPass(InstCombinePass());
    TheFPM->addPass(ReassociatePass());
    TheFPM->addPass(GVNPass());
    TheFPM->addPass(SimplifyCFGPass());

    PassBuilder PB;
    PB.registerModuleAnalyses(*TheMAM);
    PB.registerFunctionAnalyses(*TheFAM);
    PB.crossRegisterProxies(*TheLAM, *TheFAM, *TheCGAM, *TheMAM);
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
            ExitOnErr(TheJIT->addModule(ThreadSafeModule(std::move(TheModule), std::move(TheContext))));
            InitializeModuleAndManagers();
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
            FunctionProtos[ProtoAST->getName()] = std::move(ProtoAST);
        }
    }
    else
        getNextToken();
}

static void HandleTopLevelExpression()
{
    if (auto FnAST = ParseTopLevelExpr())
    {
        if (FnAST->codegen())
        {
            auto RT = TheJIT->getMainJITDylib().createResourceTracker();
            auto TSM = ThreadSafeModule(std::move(TheModule), std::move(TheContext));
            ExitOnErr(TheJIT->addModule(std::move(TSM), RT));
            InitializeModuleAndManagers();

            auto ExprSymbol = ExitOnErr(TheJIT->lookup("__anon_expr"));
            double (*FP)() = ExprSymbol.getAddress().toPtr<double (*)()>();
            fprintf(stderr, "Evaluated to %f\n", FP());
            ExitOnErr(RT->remove());
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

#ifdef _WIN32
#define DLLEXPORT __declspec(dllexport)
#else
#define DLLEXPORT
#endif

extern "C" DLLEXPORT double putchard(double X)
{
    fputc((char)X, stderr);
    return 0;
}

extern "C" DLLEXPORT double printd(double X)
{
    fprintf(stderr, "%f\b", X);
    return 0;
}

int main(int argc, char const *argv[])
{
    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    InitializeNativeTargetAsmParser();

    BinopPrecedence['='] = 2;
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
    TheJIT = ExitOnErr(KaleidoscopeJIT::Create());
    InitializeModuleAndManagers();
    // InitializeModule();
    MainLoop();
    // TheModule->print(errs(), nullptr);
    return 0;
}
