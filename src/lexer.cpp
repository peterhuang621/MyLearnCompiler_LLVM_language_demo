#include <iostream>
#include <memory>
#include <vector>
using namespace std;

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

static int gettok()
{
    static int LastChar = ' ';
    while (isspace(LastChar))
        LastChar = getchar();
    if (isalpha(LastChar))
    {
        IdentifierStr = LastChar;
        while (isalnum(LastChar = getchar()))
        {
            IdentifierStr += LastChar;
        }
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
            LastChar = getchar();
        } while (isdigit(LastChar) || LastChar == '.');
        NumVal = strtod(NumStr.c_str(), 0);
        return tok_number;
    }

    if (LastChar == '#')
    {
        do
        {
            LastChar = getchar();
        } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');
        if (LastChar != EOF)
        {
            return gettok();
        }
    }
    if (LastChar == EOF)
        return tok_eof;
    int ThisChar = LastChar;
    LastChar = getchar();
    return ThisChar;
}

static int CurTok;
static int getNextToken()
{
    return CurTok = gettok();
}

class ExprAST
{
  public:
    virtual ~ExprAST() = default;
};

class NumberExprAST : public ExprAST
{
    double Val;

  public:
    NumberExprAST(double val) : Val(val) {};
};

class VariableExprAST : public ExprAST
{
    string Name;

  public:
    VariableExprAST(const string &name) : Name(name) {};
};

class BinaryExprAST : public ExprAST
{
    char Op;
    unique_ptr<ExprAST> LHS, RHS;

  public:
    BinaryExprAST(char op, unique_ptr<ExprAST> lhs, unique_ptr<ExprAST> rhs)
        : Op(op), LHS(std::move(lhs)), RHS(std::move(rhs)) {};
};

class CallExprAST : public ExprAST
{
    string Callee;
    vector<unique_ptr<ExprAST>> Args;

  public:
    CallExprAST(const string &callee, vector<unique_ptr<ExprAST>> args) : Callee(callee), Args(std::move(args)) {};
};

class PrototypeAST : public ExprAST
{
    string Name;
    vector<string> Args;

  public:
    PrototypeAST(const string &name, vector<string> args) : Name(name), Args(args) {};
    const string &getName() const
    {
        return Name;
    }
};

class FunctionExprAST : public ExprAST
{
    unique_ptr<PrototypeAST> Proto;
    unique_ptr<ExprAST> Body;

  public:
    FunctionExprAST(unique_ptr<PrototypeAST> proto, unique_ptr<ExprAST> body)
        : Proto(std::move(proto)), Body(std::move(body)) {};
};

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

static unique_ptr<ExprAST> ParseNumberExpr()
{
    auto Result = make_unique<NumberExprAST>(NumVal);
    getNextToken();
    return std::move(Result);
}

static unique_ptr<ExprAST> ParseExpression();

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

static unique_ptr<ExprAST> parseIdentifierExpr()
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

int main(int argc, char const *argv[])
{

    return 0;
}
