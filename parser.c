/* parser.c - Recursive-descent parser + evaluator with AST
   Extends the given starter:
   - Adds tokens: ASSIGN '=', POWER '**', INC '++', DEC '--'
   - Grammar:
       statement  -> IDENT '=' expr | expr
       expr       -> term {('+'|'-') term}*
       term       -> power {('*'|'/') power}*
       power      -> unary ['**' power]           // right-assoc
       unary      -> '++' unary | '--' unary | postfix
       postfix    -> primary { '++' | '--' }*
       primary    -> INT | IDENT | '(' expr ')'
   - Evaluates and prints AST. On syntax error, prints tokens up to error and an informative message.
*/

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>
#include <stdarg.h>

/* ---------- Config ---------- */
#define MAX_LEXEME 128
#define MAX_LINE   4096

/* ---------- Token & Lexer ---------- */
typedef enum {
    T_EOF = 0,
    T_INT = 256,
    T_IDENT,
    T_ASSIGN,     // =
    T_PLUS,       // +
    T_MINUS,      // -
    T_TIMES,      // *
    T_DIVIDE,     // /
    T_LPAREN,     // (
    T_RPAREN,     // )
    T_POWER,      // **
    T_INC,        // ++
    T_DEC         // --
} TokenKind;

typedef struct {
    TokenKind kind;
    char lexeme[MAX_LEXEME];
    int  int_val;  // for integers
    int  pos;      // byte offset in line for error caret
} Token;

typedef struct {
    const char* src;
    int len;
    int i;
    Token cur;
    int had_error;
    int printed_error;
} Lexer;

/* Forward decls for parser error printing */
static void syntax_error_at(Lexer* L, const char* fmt, ...);

/* Helpers */
static int peek(Lexer* L) { return (L->i < L->len) ? L->src[L->i] : EOF; }
static int peek2(Lexer* L) { return (L->i+1 < L->len) ? L->src[L->i+1] : EOF; }
static int getc_lex(Lexer* L) { return (L->i < L->len) ? L->src[L->i++] : EOF; }

static void skip_ws(Lexer* L) {
    int c;
    while ((c = peek(L)) != EOF && isspace(c)) L->i++;
}

static void set_token(Lexer* L, TokenKind k, const char* start, int n, int pos) {
    L->cur.kind = k;
    int m = (n < MAX_LEXEME-1) ? n : (MAX_LEXEME-1);
    memcpy(L->cur.lexeme, start, m);
    L->cur.lexeme[m] = '\\0';
    L->cur.pos = pos;
}

/* Advance lexer to next token */
static void next_token(Lexer* L) {
    skip_ws(L);
    int start_pos = L->i;
    int c = peek(L);
    if (c == EOF) { set_token(L, T_EOF, "EOF", 3, start_pos); return; }

    /* Ident (letters+digits) */
    if (isalpha(c) || c == '_') {
        int j = L->i;
        getc_lex(L);
        while (isalnum(peek(L)) || peek(L) == '_') getc_lex(L);
        set_token(L, T_IDENT, L->src + j, L->i - j, j);
        return;
    }

    /* Integer */
    if (isdigit(c)) {
        int j = L->i;
        long v = 0;
        while (isdigit(peek(L))) {
            int d = getc_lex(L) - '0';
            v = v*10 + d;
        }
        set_token(L, T_INT, L->src + j, L->i - j, j);
        L->cur.int_val = (int)v;
        return;
    }

    /* Two-char operators: **, ++, -- */
    int c1 = c, c2 = peek2(L);
    if (c1 == '*' && c2 == '*') {
        getc_lex(L); getc_lex(L);
        set_token(L, T_POWER, "**", 2, start_pos);
        return;
    }
    if (c1 == '+' && c2 == '+') {
        getc_lex(L); getc_lex(L);
        set_token(L, T_INC, "++", 2, start_pos);
        return;
    }
    if (c1 == '-' && c2 == '-') {
        getc_lex(L); getc_lex(L);
        set_token(L, T_DEC, "--", 2, start_pos);
        return;
    }

    /* Single-char tokens */
    getc_lex(L);
    switch (c1) {
        case '=': set_token(L, T_ASSIGN, "=", 1, start_pos); return;
        case '+': set_token(L, T_PLUS, "+", 1, start_pos); return;
        case '-': set_token(L, T_MINUS, "-", 1, start_pos); return;
        case '*': set_token(L, T_TIMES, "*", 1, start_pos); return;
        case '/': set_token(L, T_DIVIDE, "/", 1, start_pos); return;
        case '(': set_token(L, T_LPAREN, "(", 1, start_pos); return;
        case ')': set_token(L, T_RPAREN, ")", 1, start_pos); return;
        default: {
            char buf[2] = {(char)c1, 0};
            set_token(L, T_EOF, buf, 1, start_pos);
            syntax_error_at(L, "Unknown character '%c'", c1);
            return;
        }
    }
}

/* Pretty category for the required token listing */
static const char* token_category(TokenKind k) {
    switch (k) {
        case T_INT:   return "integer";
        case T_IDENT: return "identifier";
        case T_PLUS: case T_MINUS: case T_TIMES: case T_DIVIDE:
        case T_POWER: case T_ASSIGN: case T_INC: case T_DEC:
            return "operator";
        case T_LPAREN: case T_RPAREN: return "paren";
        case T_EOF:   return "eof";
        default:      return "unknown";
    }
}

/* Print one line "lexeme,category" */
static void print_token_line(const Token* t) {
    printf("%s,%s\\n", t->lexeme, token_category(t->kind));
}

/* ---------- AST ---------- */
typedef enum {
    N_INT, N_IDENT,
    N_ADD, N_SUB, N_MUL, N_DIV, N_POW,
    N_PRE_INC, N_PRE_DEC, N_POST_INC, N_POST_DEC,
    N_ASSIGN
} NodeKind;

typedef struct Node {
    NodeKind kind;
    char ident[MAX_LEXEME]; // for N_IDENT / N_ASSIGN lhs
    int value;              // for N_INT literal
    struct Node* a;         // left/only child
    struct Node* b;         // right child (binary)
} Node;

static Node* new_node(NodeKind k, Node* a, Node* b) {
    Node* n = (Node*)malloc(sizeof(Node));
    if (!n) { fprintf(stderr, "Out of memory\\n"); exit(1); }
    n->kind = k; n->a = a; n->b = b; n->value = 0; n->ident[0] = '\\0';
    return n;
}
static Node* new_int(int v) { Node* n = new_node(N_INT, NULL, NULL); n->value = v; return n; }
static Node* new_ident(const char* name) { Node* n = new_node(N_IDENT, NULL, NULL); strncpy(n->ident,name,MAX_LEXEME-1); n->ident[MAX_LEXEME-1]=0; return n; }

/* ---------- Parser ---------- */
typedef struct {
    Lexer* L;
    /* For token printout behavior: emit as we consume */
    int token_printing_enabled;
    /* Symbol table: simple A,B,C,... -> int; 52 slots for letters */
    int sym[52];
} Parser;

/* Map IDENT name first char to index [0..51] (A..Z,a..z). Others bucket to 51. */
static int sym_index(const char* s) {
    if (!s || !s[0]) return 51;
    char c = s[0];
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= 'a' && c <= 'z') return 26 + (c - 'a');
    return 51;
}

static void advance(Parser* P) {
    if (P->token_printing_enabled) print_token_line(&P->L->cur);
    next_token(P->L);
}
static int accept(Parser* P, TokenKind k) {
    if (P->L->cur.kind == k) { advance(P); return 1; }
    return 0;
}
static void expect(Parser* P, TokenKind k, const char* msg) {
    if (!accept(P,k)) {
        syntax_error_at(P->L, "Expected %s%s%s",
            msg ? "'" : "", msg ? msg : "", msg ? "'" : "");
    }
}

/* Forward decls */
static Node* parse_statement(Parser* P);
static Node* parse_expr(Parser* P);
static Node* parse_term(Parser* P);
static Node* parse_power(Parser* P);
static Node* parse_unary(Parser* P);
static Node* parse_postfix(Parser* P);
static Node* parse_primary(Parser* P);

/* Error reporting */
static void vreport_at(const char* line, int line_len, int pos, const char* fmt, va_list ap) {
    fprintf(stderr, "Syntax error: ");
    vfprintf(stderr, fmt, ap);
    fprintf(stderr, "\\n");
    if (line && line_len >= 0) {
        fprintf(stderr, "%.*s\\n", line_len, line);
        for (int i = 0; i < pos; ++i) fputc(line[i]=='\\t' ? '\\t' : ' ', stderr);
        fprintf(stderr, "^\\n");
    }
}
static void syntax_error_at(Lexer* L, const char* fmt, ...) {
    L->had_error = 1;
    if (L->printed_error) return;
    L->printed_error = 1;
    va_list ap; va_start(ap, fmt);
    vreport_at(L->src, L->len, L->cur.pos, fmt, ap);
    va_end(ap);
}

/* statement -> IDENT '=' expr | expr */
static Node* parse_statement(Parser* P) {
    if (P->L->cur.kind == T_IDENT) {
        /* Lookahead for assignment */
        Token saved = P->L->cur;
        advance(P);
        if (P->L->cur.kind == T_ASSIGN) {
            advance(P); // '='
            Node* rhs = parse_expr(P);
            Node* lhs = new_ident(saved.lexeme);
            Node* n = new_node(N_ASSIGN, lhs, rhs);
            strncpy(n->ident, saved.lexeme, MAX_LEXEME-1);
            n->ident[MAX_LEXEME-1] = 0;
            return n;
        } else {
            /* Rewind to treat as an expression starting from IDENT */
            P->L->i = saved.pos;
            P->L->had_error = 0; P->L->printed_error = 0;
            next_token(P->L);
            return parse_expr(P);
        }
    } else {
        return parse_expr(P);
    }
}

/* expr -> term {('+'|'-') term}* */
static Node* parse_expr(Parser* P) {
    Node* n = parse_term(P);
    while (P->L->cur.kind == T_PLUS || P->L->cur.kind == T_MINUS) {
        TokenKind op = P->L->cur.kind;
        advance(P);
        Node* rhs = parse_term(P);
        n = new_node(op == T_PLUS ? N_ADD : N_SUB, n, rhs);
    }
    return n;
}

/* term -> power {('*'|'/') power}* */
static Node* parse_term(Parser* P) {
    Node* n = parse_power(P);
    while (P->L->cur.kind == T_TIMES || P->L->cur.kind == T_DIVIDE) {
        TokenKind op = P->L->cur.kind;
        advance(P);
        Node* rhs = parse_power(P);
        n = new_node(op == T_TIMES ? N_MUL : N_DIV, n, rhs);
    }
    return n;
}

/* power -> unary ['**' power]   (right-assoc) */
static Node* parse_power(Parser* P) {
    Node* left = parse_unary(P);
    if (P->L->cur.kind == T_POWER) {
        advance(P);
        Node* right = parse_power(P);
        return new_node(N_POW, left, right);
    }
    return left;
}

/* unary -> '++' unary | '--' unary | postfix */
static Node* parse_unary(Parser* P) {
    if (P->L->cur.kind == T_INC) { advance(P); return new_node(N_PRE_INC, parse_unary(P), NULL); }
    if (P->L->cur.kind == T_DEC) { advance(P); return new_node(N_PRE_DEC, parse_unary(P), NULL); }
    return parse_postfix(P);
}

/* postfix -> primary { '++' | '--' }* */
static Node* parse_postfix(Parser* P) {
    Node* n = parse_primary(P);
    for (;;) {
        if (P->L->cur.kind == T_INC) { advance(P); n = new_node(N_POST_INC, n, NULL); }
        else if (P->L->cur.kind == T_DEC) { advance(P); n = new_node(N_POST_DEC, n, NULL); }
        else break;
    }
    return n;
}

/* primary -> INT | IDENT | '(' expr ')' */
static Node* parse_primary(Parser* P) {
    if (P->L->cur.kind == T_INT) {
        int v = P->L->cur.int_val;
        advance(P);
        return new_int(v);
    }
    if (P->L->cur.kind == T_IDENT) {
        char name[MAX_LEXEME]; strncpy(name, P->L->cur.lexeme, MAX_LEXEME-1); name[MAX_LEXEME-1]=0;
        advance(P);
        return new_ident(name);
    }
    if (P->L->cur.kind == T_LPAREN) {
        advance(P);
        Node* n = parse_expr(P);
        expect(P, T_RPAREN, ")");
        return n;
    }
    syntax_error_at(P->L, "Unexpected token '%s'", P->L->cur.lexeme);
    return new_int(0);
}

/* ---------- AST Printing ---------- */
static void print_indent(int n) { while (n--) printf("    "); }

static const char* op_label(NodeKind k) {
    switch (k) {
        case N_ADD: return "+ (Add)";
        case N_SUB: return "- (Minus)";
        case N_MUL: return "*(Multiply)";
        case N_DIV: return "/ (Divide)";
        case N_POW: return "**(Power)";
        case N_PRE_INC:  return "++ (PreInc)";
        case N_PRE_DEC:  return "-- (PreDec)";
        case N_POST_INC: return "++ (PostInc)";
        case N_POST_DEC: return "-- (PostDec)";
        case N_ASSIGN:   return "= (Assign)";
        default: return "?";
    }
}

static void print_ast(Node* n, int depth) {
    if (!n) return;
    if (n->kind == N_INT) {
        print_indent(depth); printf("%d (int)\\n", n->value);
        return;
    }
    if (n->kind == N_IDENT) {
        print_indent(depth); printf("%s (id)\\n", n->ident);
        return;
    }
    /* binary or unary forms */
    print_indent(depth);
    if (n->kind == N_ASSIGN || n->kind == N_ADD || n->kind == N_SUB ||
        n->kind == N_MUL || n->kind == N_DIV || n->kind == N_POW) {
        printf("%s\\n", op_label(n->kind));
        print_ast(n->a, depth+1);
        print_ast(n->b, depth+1);
    } else if (n->kind == N_PRE_INC || n->kind == N_PRE_DEC ||
               n->kind == N_POST_INC || n->kind == N_POST_DEC) {
        printf("%s\\n", op_label(n->kind));
        print_ast(n->a, depth+1);
    }
}

/* ---------- Evaluator ---------- */
/* Side-effecting ++/-- require lvalues; enforce that for identifiers only. */
typedef struct {
    int* sym; // shared table
    int had_runtime_error;
} EvalCtx;

static int* lvalue_ptr(EvalCtx* E, Node* n) {
    if (n->kind == N_IDENT) {
        int idx = sym_index(n->ident);
        return &E->sym[idx];
    }
    return NULL;
}

static int eval(EvalCtx* E, Node* n) {
    if (!n) return 0;
    switch (n->kind) {
        case N_INT: return n->value;
        case N_IDENT: {
            int idx = sym_index(n->ident);
            return E->sym[idx];
        }
        case N_ADD: return eval(E, n->a) + eval(E, n->b);
        case N_SUB: return eval(E, n->a) - eval(E, n->b);
        case N_MUL: return eval(E, n->a) * eval(E, n->b);
        case N_DIV: {
            int r = eval(E, n->b);
            if (r == 0) { fprintf(stderr, "Runtime error: division by zero\\n"); E->had_runtime_error = 1; return 0; }
            return eval(E, n->a) / r;
        }
        case N_POW: {
            int base = eval(E, n->a);
            int exp  = eval(E, n->b);
            if (exp < 0) { fprintf(stderr, "Runtime error: negative exponent not supported (integers)\\n"); E->had_runtime_error = 1; return 0; }
            long res = 1;
            for (int i=0;i<exp;i++) res *= base;
            return (int)res;
        }
        case N_PRE_INC: {
            int* p = lvalue_ptr(E, n->a);
            if (!p) { fprintf(stderr, "Runtime error: '++' requires an identifier lvalue\\n"); E->had_runtime_error = 1; return 0; }
            ++(*p);
            return *p;
        }
        case N_PRE_DEC: {
            int* p = lvalue_ptr(E, n->a);
            if (!p) { fprintf(stderr, "Runtime error: '--' requires an identifier lvalue\\n"); E->had_runtime_error = 1; return 0; }
            --(*p);
            return *p;
        }
        case N_POST_INC: {
            int* p = lvalue_ptr(E, n->a);
            if (!p) { fprintf(stderr, "Runtime error: 'x++' requires an identifier lvalue\\n"); E->had_runtime_error = 1; return 0; }
            int old = *p; (*p)++;
            return old;
        }
        case N_POST_DEC: {
            int* p = lvalue_ptr(E, n->a);
            if (!p) { fprintf(stderr, "Runtime error: 'x--' requires an identifier lvalue\\n"); E->had_runtime_error = 1; return 0; }
            int old = *p; (*p)--;
            return old;
        }
        case N_ASSIGN: {
            int* p = lvalue_ptr(E, n->a);
            if (!p) { fprintf(stderr, "Runtime error: assignment LHS must be identifier\\n"); E->had_runtime_error = 1; return 0; }
            int v = eval(E, n->b);
            *p = v;
            return v;
        }
        default: return 0;
    }
}

/* ---------- Utility ---------- */
static void free_ast(Node* n) {
    if (!n) return;
    free_ast(n->a); free_ast(n->b); free(n);
}

static void init_parser(Parser* P, Lexer* L) {
    memset(P, 0, sizeof(*P));
    P->L = L;
    P->token_printing_enabled = 1;
    for (int i=0;i<52;i++) P->sym[i] = 0;
}

/* Print header for AST to match sample */
static void print_ast_header(void) {
    printf("Abstract Syntax Tree:\\n");
}

/* ---------- Driver: process one input line ---------- */
static void process_line(const char* line, Parser* P) {
    if (!line) return;
    Lexer L = {0};
    L.src = line;
    L.len = (int)strlen(line);
    L.i   = 0;
    L.had_error = 0;
    L.printed_error = 0;

    P->L = &L;

    next_token(P->L);

    /* Parse one statement or expression */
    Node* root = parse_statement(P);

    /* If error occurred: stop after printing tokens up to error, then error msg already shown */
    if (L.had_error) {
        return;
    }

    /* Require that the whole line is consumed (ignoring trailing spaces) */
    while (P->L->cur.kind != T_EOF) {
        syntax_error_at(P->L, "Unexpected token '%s' after complete parse", P->L->cur.lexeme);
        free_ast(root);
        return;
    }

    /* Print AST and evaluated value */
    print_ast_header();
    print_ast(root, 0);

    EvalCtx E = { .sym = P->sym, .had_runtime_error = 0 };
    int value = eval(&E, root);
    if (!E.had_runtime_error) {
        printf("Value: %d\\n", value);
    }
    free_ast(root);
}

/* ---------- Main ---------- */
static void usage(const char* prog) {
    fprintf(stderr, "Usage:\\n");
    fprintf(stderr, "  %s               # read a single line from stdin\\n", prog);
    fprintf(stderr, "  %s -f FILE       # read and process each non-empty line from FILE\\n", prog);
}

int main(int argc, char** argv) {
    Parser P; Lexer L; init_parser(&P, &L);

    if (argc == 1) {
        /* Read one line from stdin */
        char buf[MAX_LINE];
        if (!fgets(buf, sizeof(buf), stdin)) return 0;
        process_line(buf, &P);
        return 0;
    }
    if (argc == 3 && strcmp(argv[1], "-f") == 0) {
        const char* path = argv[2];
        FILE* fp = fopen(path, "r");
        if (!fp) { fprintf(stderr, "ERROR: cannot open %s\\n", path); return 1; }
        char buf[MAX_LINE];
        while (fgets(buf, sizeof(buf), fp)) {
            int allspace = 1;
            for (char* p = buf; *p; ++p) if (!isspace((unsigned char)*p)) { allspace = 0; break; }
            if (allspace) continue;
            process_line(buf, &P);
            printf("----\\n");
        }
        fclose(fp);
        return 0;
    }
    usage(argv[0]);
    return 1;
}
