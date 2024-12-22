#include <assert.h>
#include <elf.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

/*******************************************************************************
 * Libray **********************************************************************
 ******************************************************************************/

// Some parts taken from https://nullprogram.com/blog/2023/10/08/.

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int8_t i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;

typedef uint8_t bool;
#define true 1
#define false 0

typedef struct {
    u8 *buf;
    size_t len;
} Str;

#define countof(a) (sizeof(a) / sizeof(*(a)))
#define lengthof(s) (countof(s) - 1)

// Make a proper string from a string literal.
#define Str(s)                                                                 \
    (Str) { (u8 *)s, lengthof(s) }

char *str_as_cstr(Str s) {
    char *buf = malloc(s.len + 1);
    memcpy(buf, s.buf, s.len);
    buf[s.len] = '\0';
    return buf;
}

void hexdump(Str s) {
    for (u64 i = 0; i < s.len; i += 1) {
        if (i % 0x10 == 0 && i != 0) {
            putchar('\n');
        }
        if (i % 0x10 == 0) {
            printf("0x%010lx: ", i);
        }
        if (i % 0x08 == 0) {
            putchar(' ');
        }
        printf("%02x ", s.buf[i]);
    }
    putchar('\n');
}

#define LIST_REVERSE(TYPE, head)                                               \
    do {                                                                       \
        TYPE *cur = head, *prev = NULL, *next;                                 \
        while (cur != NULL) {                                                  \
            next = cur->next;                                                  \
            cur->next = prev;                                                  \
            prev = cur;                                                        \
            cur = next;                                                        \
        }                                                                      \
        head = prev;                                                           \
    } while (0)

/*******************************************************************************
 * Lexing **********************************************************************
 ******************************************************************************/

// Our calculator only supports i64 numbers.
typedef i64 Num;

typedef enum {
    TokenWhiteSpaceT,
    TokenNumT,
    TokenPlusT,
    TokenMinusT,
    TokenMultT,
    TokenDivT,
    TokenLParenT,
    TokenRParenT,
} TokenType;

typedef struct {
    TokenType type;
    union {
        Num numval;
    } as;
} Token;

void print_token(Token *t) {
    switch (t->type) {
    case TokenWhiteSpaceT: printf("TokenWhiteSpace\n"); break;
    case TokenNumT: printf("TokenNum %ld\n", t->as.numval); break;
    case TokenPlusT: printf("TokenPlus\n"); break;
    case TokenMinusT: printf("TokenMinus\n"); break;
    case TokenMultT: printf("TokenMult\n"); break;
    case TokenDivT: printf("TokenDiv\n"); break;
    case TokenLParenT: printf("TokenLParen\n"); break;
    case TokenRParenT: printf("TokenRParen\n"); break;
    default: assert(false && "Invalid token type");
    }
}

typedef struct TokenList TokenList;
struct TokenList {
    Token *token;
    TokenList *next;
};

void print_token_list(TokenList *tokens) {
    for (TokenList *i = tokens; i != NULL; i = i->next) {
        print_token(i->token);
    }
}

TokenList *prepend_to_token_list(TokenList *head, Token *token) {
    TokenList *new_head = malloc(sizeof(TokenList));
    new_head->token = token;
    new_head->next = head;
    return new_head;
}

bool is_digit(u8 c) { return '0' <= c && c <= '9'; }

typedef enum {
    LexErrUnexpectedChar = 0x0101,
} LexErrType;

// Emulate "Option<T>".
typedef struct {
    bool is_ok;
    union {
        struct {
            TokenList *tokens;
        } ok;
        struct LexErr {
            LexErrType type;
            u64 byte_pos;
            u8 chr;
        } err;
    };
} LexRetRes;

void print_lex_error(struct LexErr err) {
    fprintf(stderr,
            "Error lexing: error type 0x%04x at input byte position %ld, char "
            "'%c'\n",
            err.type, err.byte_pos, err.chr);
}

// Tokenize a string.
LexRetRes lex(Str s) {
    TokenList *list = NULL;

    for (u64 i = 0; i < s.len;) {
        if (s.buf[i] == ' ') {
            // Don't emit any token; simply ignore whitespace.
            while (i < s.len && s.buf[i] == ' ') {
                i += 1;
            }
        }

        else if (is_digit(s.buf[i])) {
            Token *token = malloc(sizeof(*token));
            token->type = TokenNumT;
            token->as.numval = 0;
            while (is_digit(s.buf[i])) {
                token->as.numval *= 10;
                token->as.numval += s.buf[i] - '0';
                i += 1;
            }
            list = prepend_to_token_list(list, token);
        }

        else if (s.buf[i] == '+') {
            Token *token = malloc(sizeof(*token));
            token->type = TokenPlusT;
            token->as.numval = 0;
            list = prepend_to_token_list(list, token);
            i += 1;
        }

        else if (s.buf[i] == '-') {
            Token *token = malloc(sizeof(*token));
            token->type = TokenMinusT;
            token->as.numval = 0;
            list = prepend_to_token_list(list, token);
            i += 1;
        }

        else if (s.buf[i] == '*') {
            Token *token = malloc(sizeof(*token));
            token->type = TokenMultT;
            token->as.numval = 0;
            list = prepend_to_token_list(list, token);
            i += 1;
        }

        else if (s.buf[i] == '/') {
            Token *token = malloc(sizeof(*token));
            token->type = TokenDivT;
            token->as.numval = 0;
            list = prepend_to_token_list(list, token);
            i += 1;
        }

        else if (s.buf[i] == '(') {
            Token *token = malloc(sizeof(*token));
            token->type = TokenLParenT;
            token->as.numval = 0;
            list = prepend_to_token_list(list, token);
            i += 1;
        }

        else if (s.buf[i] == ')') {
            Token *token = malloc(sizeof(*token));
            token->type = TokenRParenT;
            token->as.numval = 0;
            list = prepend_to_token_list(list, token);
            i += 1;
        }

        else {
            return (LexRetRes){
                .is_ok = false,
                .err = {LexErrUnexpectedChar, i, s.buf[i]},
            };
        }
    }

    LIST_REVERSE(TokenList, list);
    return (LexRetRes){true, .ok = {list}};
}

/*******************************************************************************
 * Parsing (recursive descent, with expected operator precedence) **************
 ******************************************************************************/

typedef enum {
    SymbolNumT,
    SymbolBinopT,
} SymbolType;

typedef enum {
    SymbolBinopPlusT,
    SymbolBinopMinusT,
    SymbolBinopMultT,
    SymbolBinopDivT,
} SymbolBinopType;

typedef struct Ast Ast;

typedef struct {
    SymbolBinopType type;
    Ast *operand1;
    Ast *operand2;
} SymbolBinop;

struct Ast {
    SymbolType type;
    union {
        u64 numval;
        SymbolBinop binop;
    } as;
};

// Pre-order traversal of the AST.
void print_ast_(Ast *ast) {
    switch (ast->type) {
    case SymbolNumT: printf("%ld", ast->as.numval); break;

    case SymbolBinopT:
        putchar('(');
        switch (ast->as.binop.type) {
        case SymbolBinopPlusT: putchar('+'); break;
        case SymbolBinopMinusT: putchar('-'); break;
        case SymbolBinopMultT: putchar('*'); break;
        case SymbolBinopDivT: putchar('/'); break;
        default: assert(false && "Invalid binary operation type");
        }
        putchar(' ');
        print_ast_(ast->as.binop.operand1);
        putchar(' ');
        print_ast_(ast->as.binop.operand2);
        putchar(')');
        break;

    default: assert(false && "Invalid symbol type");
    }
}

// Print AST as s-expression.
void print_ast(Ast *ast) {
    if (ast == NULL) {
        return;
    }
    print_ast_(ast);
    putchar('\n');
}

typedef struct {
    TokenList *rest;
    Ast *ast;
} ParseRet;

typedef enum {
    ParseErrUnbalancedParanthesis = 0x0201,
    ParseErrUnexpectedFactor = 0x0202,
    ParseErrUnconsumedInput = 0x0203,
    ParseErrNoNumAfterUnaryMinus = 0x0204,
    ParseErrUnexpectedEOF = 0x0205,
} ParseErrType;

// Emulate "Result<T>".
typedef struct {
    bool is_ok;
    union {
        ParseRet ok;
        ParseErrType err;
    };
} ParseRetRes;

void print_parse_error(ParseErrType err) {
    fprintf(stderr, "Error parsing: error type 0x%04x\n", err);
}

ParseRetRes parse_expr(TokenList *tokens);

// Parse number / unary minus / parenthesis groupings.
ParseRetRes parse_factor(TokenList *tokens) {
    if (tokens == NULL) {
        // Note that this makes sure that `parse` never simultaneously returns
        // `is_ok` and a NULL-pointer for the AST.
        return (ParseRetRes){false, .err = ParseErrUnexpectedEOF};
    }

    else if (tokens->token->type == TokenNumT ||
             tokens->token->type == TokenMinusT) {
        Ast *res = malloc(sizeof(*res));
        res->type = SymbolNumT;
        res->as.numval = 1;

        while (tokens != NULL && tokens->token->type == TokenMinusT) {
            res->as.numval *= -1;
            tokens = tokens->next;
        }

        if (tokens == NULL || tokens->token->type != TokenNumT) {
            return (ParseRetRes){false, .err = ParseErrNoNumAfterUnaryMinus};
        }

        res->as.numval *= tokens->token->as.numval;
        tokens = tokens->next;
        return (ParseRetRes){true, .ok = {.rest = tokens, .ast = res}};
    }

    else if (tokens->token->type == TokenLParenT) {
        tokens = tokens->next;
        ParseRetRes r = parse_expr(tokens);
        if (!r.is_ok) {
            return r;
        }
        tokens = r.ok.rest;

        if (tokens == NULL || tokens->token->type != TokenRParenT) {
            return (ParseRetRes){false, .err = ParseErrUnbalancedParanthesis};
        }
        tokens = tokens->next;

        return (ParseRetRes){true, .ok = {.rest = tokens, .ast = r.ok.ast}};
    }

    else {
        return (ParseRetRes){false, .err = ParseErrUnexpectedFactor};
    }
}

// Parse multiplications / divisions.
ParseRetRes parse_term(TokenList *tokens) {
    ParseRetRes op1 = parse_factor(tokens);
    if (!op1.is_ok) {
        return op1;
    }

    tokens = op1.ok.rest;
    Ast *res = op1.ok.ast;

    while (tokens != NULL && (tokens->token->type == TokenMultT ||
                              tokens->token->type == TokenDivT)) {
        SymbolBinop binop = {0};
        binop.type = (tokens->token->type == TokenMultT) ? SymbolBinopMultT
                                                         : SymbolBinopDivT;
        binop.operand1 = res;

        tokens = tokens->next;
        ParseRetRes op2 = parse_factor(tokens);
        if (!op2.is_ok) {
            return op2;
        }
        binop.operand2 = op2.ok.ast;
        tokens = op2.ok.rest;

        Ast *newres = malloc(sizeof(*newres));
        newres->type = SymbolBinopT;
        newres->as.binop = binop;
        res = newres;
    }

    return (ParseRetRes){true, .ok = {.rest = tokens, .ast = res}};
}

// Parse additions / subtractions.
ParseRetRes parse_expr(TokenList *tokens) {
    ParseRetRes op1 = parse_term(tokens);
    if (!op1.is_ok) {
        return op1;
    }

    tokens = op1.ok.rest;
    Ast *res = op1.ok.ast;

    while (tokens != NULL && (tokens->token->type == TokenPlusT ||
                              tokens->token->type == TokenMinusT)) {
        SymbolBinop binop = {0};
        binop.type = (tokens->token->type == TokenPlusT) ? SymbolBinopPlusT
                                                         : SymbolBinopMinusT;
        binop.operand1 = res;

        tokens = tokens->next;
        ParseRetRes op2 = parse_term(tokens);
        if (!op2.is_ok) {
            return op2;
        }
        binop.operand2 = op2.ok.ast;
        tokens = op2.ok.rest;

        Ast *newres = malloc(sizeof(*newres));
        newres->type = SymbolBinopT;
        newres->as.binop = binop;
        res = newres;
    }

    return (ParseRetRes){true, .ok = {.rest = tokens, .ast = res}};
}

// Parse a list of tokens.
ParseRetRes parse(TokenList *tokens) {
    ParseRetRes res = parse_expr(tokens);
    assert(!(res.is_ok && res.ok.ast == NULL) &&
           "Error parsing: `parse` should never return is_ok and a NULL "
           "pointer for the AST");
    if (res.is_ok && res.ok.rest != NULL) {
        return (ParseRetRes){false, .err = ParseErrUnconsumedInput};
    }
    return res;
}

/*******************************************************************************
 * Mode: interpret AST. ********************************************************
 ******************************************************************************/

// Post-order traversal of the AST.
Num interpret_ast_(Ast *ast) {
    switch (ast->type) {
    case SymbolNumT: return ast->as.numval; break;

    case SymbolBinopT: {
        Num op1 = interpret_ast_(ast->as.binop.operand1);
        Num op2 = interpret_ast_(ast->as.binop.operand2);
        switch (ast->as.binop.type) {
        case SymbolBinopPlusT: return op1 + op2; break;
        case SymbolBinopMinusT: return op1 - op2; break;
        case SymbolBinopMultT: return op1 * op2; break;
        case SymbolBinopDivT: return op1 / op2; break;
        default: assert(false && "Invalid binary operation type");
        }
    } break;

    default: assert(false && "Invalid symbol type");
    }
}

Num mode_interpret_ast(Ast *ast) {
    printf("[+] Interpreting AST\n");
    Num res = interpret_ast_(ast);
    printf("    Result: %ld\n", res);
    return res;
}

/*******************************************************************************
 * Mode: compile AST to custom byte code and then run (interpret) the bytecode *
 * in a custom VM. *************************************************************
 * Good *reference: https://www.jmeiners.com/lc3-vm/ ***************************
 ******************************************************************************/

typedef enum {
    OpAdd = 0,
    OpSub,
    OpMul,
    OpDiv,
    OpPush,
    OpPop,
    OpExit,
} OpCode;

#define VM_MEM_SIZE 0x1FFF
#define VM_STACK_SIZE VM_MEM_SIZE / 8
typedef struct {
    // Memory Layout:
    // 0x1FFF   Stack (growing downwards, in units of Num)
    //  ...
    // 0x0000   Code (in units of u8)
    u8 mem[VM_MEM_SIZE];
    u64 ip; // Instruction pointer (points to next unexecuted instruction).
    u64 sp; // Stack pointer (points to top currently free stack slot).
} VM;

VM vm_new() {
    return (VM){
        .mem = {0},
        .ip = 0,
        .sp = VM_MEM_SIZE - sizeof(Num),
    };
}

void vm_stack_push(VM *vm, Num num) {
    assert(VM_MEM_SIZE - vm->sp < VM_STACK_SIZE &&
           "Stack upper bound exceeded");
    *((Num *)&vm->mem[vm->sp]) = num;
    vm->sp -= sizeof(Num);
}

Num vm_stack_pop(VM *vm) {
    assert(VM_MEM_SIZE - sizeof(Num) > vm->sp && "Stack lower bound exceeded");
    vm->sp += sizeof(Num);
    Num res = *((Num *)&vm->mem[vm->sp]);
    return res;
}

// Post-order traversal of the AST.
void vm_bytecode_compile_ast_(VM *vm, Ast *ast) {
    switch (ast->type) {
    case SymbolNumT:
        vm->mem[vm->ip++] = OpPush;
        *((Num *)&vm->mem[vm->ip]) = ast->as.numval;
        vm->ip += sizeof(ast->as.numval);
        break;

    case SymbolBinopT: {
        vm_bytecode_compile_ast_(vm, ast->as.binop.operand1);
        vm_bytecode_compile_ast_(vm, ast->as.binop.operand2);
        switch (ast->as.binop.type) {
        case SymbolBinopPlusT: vm->mem[vm->ip++] = OpAdd; break;
        case SymbolBinopMinusT: vm->mem[vm->ip++] = OpSub; break;
        case SymbolBinopMultT: vm->mem[vm->ip++] = OpMul; break;
        case SymbolBinopDivT: vm->mem[vm->ip++] = OpDiv; break;
        default: assert(false && "Invalid binary operation type");
        }
    } break;

    default: assert(false && "Invalid symbol type");
    }
}

void vm_bytecode_compile_ast(VM *vm, Ast *ast) {
    vm_bytecode_compile_ast_(vm, ast);
    // Prevent execution of garbage after the actual code.
    vm->mem[vm->ip++] = OpExit;
    vm->ip = 0; // Reset instruction pointer back to entry-point.
}

Num vm_run(VM *vm) {
    while (vm->ip < VM_MEM_SIZE - VM_STACK_SIZE) {
        // "Fetch".
        u8 opcode = vm->mem[vm->ip];
        vm->ip += 1;
        // "Decode" and "Execute".
        switch (opcode) {
        case OpAdd:
        case OpSub:
        case OpMul:
        case OpDiv: {
            Num op2 = vm_stack_pop(vm);
            Num op1 = vm_stack_pop(vm);
            switch (opcode) {
            case OpAdd: vm_stack_push(vm, op1 + op2); break;
            case OpSub: vm_stack_push(vm, op1 - op2); break;
            case OpMul: vm_stack_push(vm, op1 * op2); break;
            case OpDiv: vm_stack_push(vm, op1 / op2); break;
            }
        } break;
        case OpPush:
            vm_stack_push(vm, *((Num *)&vm->mem[vm->ip]));
            vm->ip += sizeof(Num);
            break;
        case OpPop: vm_stack_pop(vm); break;
        case OpExit: goto end_while;
        default: assert(false && "Invalid opcode");
        }
    }

end_while:

    assert(vm->sp == VM_MEM_SIZE - sizeof(Num) - sizeof(Num) &&
           "Not exactly one element on stack");
    return vm_stack_pop(vm);
}

void vm_disassemble_program(VM *vm) {
    for (u64 i = 0; i < VM_MEM_SIZE - VM_STACK_SIZE;) {
        printf("         ");
        switch (vm->mem[i++]) {
        case OpAdd: printf("OpAdd\n"); break;
        case OpSub: printf("OpSub\n"); break;
        case OpMul: printf("OpMul\n"); break;
        case OpDiv: printf("OpDiv\n"); break;
        case OpPush: {
            Num num = *((Num *)&vm->mem[i]);
            i += sizeof(Num);
            printf("OpPush %ld\n", num);
        } break;
        case OpPop: printf("OpPop\n"); break;
        case OpExit: printf("OpExit\n"); return;
        }
    }
}

Num mode_vm_ast(Ast *ast) {
    printf("[+] Running VM\n");
    VM vm = vm_new();
    vm_bytecode_compile_ast(&vm, ast);
    printf("    VM instruction stream:\n");
    vm_disassemble_program(&vm);
    Num res = vm_run(&vm);
    printf("    Result: %ld\n", res);
    return res;
}

/*******************************************************************************
 * Mode: jit AST and then run the jitted code. *********************************
 * Good reference: https://github.com/spencertipping/jit-tutorial **************
 ******************************************************************************/

typedef struct {
    u8 *mem; // Code memory.
    u64 n;   // Size of memory.
    u64 i;   // Current position (only needed during jitting of the code).
} Jit;

typedef Num (*Jitfn)();

// Extend the jit's code with given bytes.
void jit_push(Jit *jit, int n, ...) {
    va_list bytes;
    va_start(bytes, n);
    for (u8 i = 0; i < n; i++) {
        assert(jit->i < jit->n && "Error: JIT code size exceeded");
        jit->mem[jit->i++] = (u8)va_arg(bytes, int);
    }
    va_end(bytes);
}

// Push a number to the stack at runtime via rax.
void jit_stack_push(Jit *jit, Num n) {
    jit_push(jit, 2, 0x48, 0xb8);                   // mov  rax, n
    jit_push(jit, 1, (((u64)n) >> (0 * 8)) & 0xff); //     n in little endian
    jit_push(jit, 1, (((u64)n) >> (1 * 8)) & 0xff); //     n in little endian
    jit_push(jit, 1, (((u64)n) >> (2 * 8)) & 0xff); //     n in little endian
    jit_push(jit, 1, (((u64)n) >> (3 * 8)) & 0xff); //     n in little endian
    jit_push(jit, 1, (((u64)n) >> (4 * 8)) & 0xff); //     n in little endian
    jit_push(jit, 1, (((u64)n) >> (5 * 8)) & 0xff); //     n in little endian
    jit_push(jit, 1, (((u64)n) >> (6 * 8)) & 0xff); //     n in little endian
    jit_push(jit, 1, (((u64)n) >> (7 * 8)) & 0xff); //     n in little endian
    jit_push(jit, 1, 0x50);                         // push rax
}

// Post-order traversal of the AST.
void jit_ast_(Ast *ast, Jit *jit) {
    switch (ast->type) {
    case SymbolNumT: jit_stack_push(jit, ast->as.numval); break;

    case SymbolBinopT: {
        jit_ast_(ast->as.binop.operand1, jit);
        jit_ast_(ast->as.binop.operand2, jit);
        jit_push(jit, 1, 0x5b); // pop rbx
        jit_push(jit, 1, 0x58); // pop rax
        switch (ast->as.binop.type) {
        case SymbolBinopPlusT:
            jit_push(jit, 3, 0x48, 0x01, 0xd8); // add  rax, rbx
            break;
        case SymbolBinopMinusT:
            jit_push(jit, 3, 0x48, 0x29, 0xd8); // sub  rax, rbx
            break;
        case SymbolBinopMultT:
            jit_push(jit, 3, 0x48, 0xf7, 0xeb); // imul rbx
            break;
        case SymbolBinopDivT:
            jit_push(jit, 5, 0x48, 0x99, 0x48, 0xf7,
                     0xfb); // cqo (sign extend); idiv rbx
            break;
        default: assert(false && "Invalid binary operation type");
        }
        jit_push(jit, 1, 0x50); // push rax
    } break;

    default: assert(false && "Invalid symbol type");
    }
}

#define JIT_MAX_SIZE 0x1000
// Compile an AST to native x86_64 machine code.
Str jit_ast(Ast *ast) {
    Jit jit = {0};
    jit.n = JIT_MAX_SIZE;
    jit.i = 0;
    jit.mem = mmap(NULL, jit.n, PROT_READ | PROT_WRITE | PROT_EXEC,
                   MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (jit.mem == MAP_FAILED) {
        fprintf(stderr, "Error mmap: Failed to allocate memory");
        exit(1);
    }

    // Function prologue.
    jit_push(&jit, 1, 0x55);             // push rbp
    jit_push(&jit, 3, 0x48, 0x89, 0xe5); // mov  rbp, rsp
    jit_push(&jit, 1, 0x53);             // push rbx (save modified registers)

    jit_ast_(ast, &jit);
    jit_push(&jit, 1, 0x58); //             pop rax (final computed result)

    // Function epilogue.
    jit_push(&jit, 1, 0x5b); //             pop rbx
    jit_push(&jit, 1, 0x5d); //             pop rbp
    jit_push(&jit, 1, 0xc3); //             ret

    Str code = {jit.mem, jit.i};
    return code;
}

Num mode_jit_ast(Ast *ast) {
    printf("[+] Running JIT compiler\n");
    Str code = jit_ast(ast);

    printf("    Hexdump of JIT program\n");
    hexdump(code);

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
    Jitfn fn = (Jitfn)code.buf;
#pragma GCC diagnostic pop
    // __asm__ volatile("int3"); // Debug break.
    Num res = fn();

    munmap(code.buf, code.len);

    printf("    Result: %ld\n", res);
    return res;
}

/*******************************************************************************
 * Mode: compile the AST into a native ELF, write it out to the file system, ***
 * and then run it. ************************************************************
 ******************************************************************************/

void write_program_to_file(Str s, Str outpath) {
    char *p = str_as_cstr(outpath);

    FILE *file = fopen(p, "w");
    if (file == NULL) {
        fprintf(stderr, "Error fopen: file %.*s\n", (int)outpath.len,
                outpath.buf);
        exit(1);
    }

    size_t nb = fwrite(s.buf, 1, s.len, file);
    if (nb != s.len) {
        fprintf(stderr, "Error fwrite: file %.*s\n", (int)outpath.len,
                outpath.buf);
        exit(1);
    }

    fclose(file);

    if (chmod(p, S_IRUSR | S_IXUSR | S_IWUSR) == -1) {
        fprintf(stderr, "Error chmod: file %.*s\n", (int)outpath.len,
                outpath.buf);
        exit(1);
    }
}

// Wrap native x86_64 machine instructions into a runnable ELF file.
// `code_` is a function with the signature `() -> i64`. The final elf calls
// this function and writes the resulting 8 bytes to stdout.
// Reference: man 5 elf. Also very helpful: https://formats.kaitai.io/elf/ and
// https://github.com/kaitai-io/kaitai_struct_visualizer.
// Compile a minimal hello world program statically with:
//
//      nasm -f elf64 hello.asm -o hello.o
//      ld hello.o -o hello
//      objdump -D hello
//
// ksv hello elf.ksy
//
// AI was also useful.
Str build_elf(Str code_) {
    u64 base_addr = 0x400000;

    // Wrap function in `code_` into a call. Also see
    // https://blog.rchapman.org/posts/Linux_System_Call_Table_for_x86_64/.

    // Example of resulting assembly including wrapping code for return the
    // result:
    // $ ./calc compile /tmp/out "4+ 5"
    // ...
    // $ gdb /tmp/out
    // (gdb) starti
    // Starting program: /tmp/out
    //
    // Program stopped.
    // 0x0000000000400078 in ?? ()
    // (gdb) disassemble/r $rip, +75
    // Dump of assembler code from 0x400078 to 0x4000c3:
    // => 0x0000000000400078:  e8 21 00 00 00          call   0x40009e
    //    0x000000000040007d:  50                      push   rax
    //    0x000000000040007e:  b8 01 00 00 00          mov    eax,0x1
    //    0x0000000000400083:  bf 01 00 00 00          mov    edi,0x1
    //    0x0000000000400088:  48 89 e6                mov    rsi,rsp
    //    0x000000000040008b:  ba 08 00 00 00          mov    edx,0x8
    //    0x0000000000400090:  0f 05                   syscall
    //    0x0000000000400092:  b8 3c 00 00 00          mov    eax,0x3c
    //    0x0000000000400097:  bf 00 00 00 00          mov    edi,0x0
    //    0x000000000040009c:  0f 05                   syscall
    //    0x000000000040009e:  55                      push   rbp
    //    0x000000000040009f:  48 89 e5                mov    rbp,rsp
    //    0x00000000004000a2:  53                      push   rbx
    //    0x00000000004000a3:  48 b8 04 00 00 00 00 00 00 00   movabs rax,0x4
    //    0x00000000004000ad:  50                      push   rax
    //    0x00000000004000ae:  48 b8 05 00 00 00 00 00 00 00   movabs rax,0x5
    //    0x00000000004000b8:  50                      push   rax
    //    0x00000000004000b9:  5b                      pop    rbx
    //    0x00000000004000ba:  58                      pop    rax
    //    0x00000000004000bb:  48 01 d8                add    rax,rbx
    //    0x00000000004000be:  50                      push   rax
    //    0x00000000004000bf:  58                      pop    rax
    //    0x00000000004000c0:  5b                      pop    rbx
    //    0x00000000004000c1:  5d                      pop    rbp
    //    0x00000000004000c2:  c3                      ret
    // End of assembler dump.

    u8 call[] = {
        // 0xcc,                      // int3 (debug break)
        0xe8, 0x21, 0x00, 0x00, 0x00, // call 0x40009e
        0x50,                         // push rax
        0xb8, 0x01, 0x00, 0x00, 0x00, // mov  eax, 1 (write syscall)
        0xbf, 0x01, 0x00, 0x00, 0x00, // mov  edi, 1 (fd: stdout)
        0x48, 0x89, 0xe6,             // mov  rsi, rsp (buf: rax value on stack)
        0xba, 0x08, 0x00, 0x00, 0x00, // mov  edx, 8 (count: sizeof(i64))
        0x0f, 0x05,                   // syscall
        0xb8, 0x3c, 0x00, 0x00, 0x00, // mov  eax, 0x3c (exit syscall)
        0xbf, 0x00, 0x00, 0x00, 0x00, // mov  rdi, 0 (EXIT_SUCCESS)
        0x0f, 0x05,                   // syscall
    };
    Str code = {0};
    code.len = countof(call) + code_.len;
    code.buf = malloc(code.len);
    memcpy(code.buf, call, countof(call));
    memcpy(code.buf + countof(call), code_.buf, code_.len);

    // Then wrap the native code in `code` into an elf.

    Str elf = {0};
    elf.len = sizeof(Elf64_Ehdr) + sizeof(Elf64_Phdr) + code.len;
    elf.buf = malloc(elf.len);
    memset(elf.buf, 0, elf.len);

    Elf64_Ehdr *ehdr = (Elf64_Ehdr *)elf.buf;
    ehdr->e_ident[EI_MAG0] = ELFMAG0;
    ehdr->e_ident[EI_MAG1] = ELFMAG1;
    ehdr->e_ident[EI_MAG2] = ELFMAG2;
    ehdr->e_ident[EI_MAG3] = ELFMAG3;
    ehdr->e_ident[EI_CLASS] = ELFCLASS64;
    ehdr->e_ident[EI_DATA] = ELFDATA2LSB;
    ehdr->e_ident[EI_VERSION] = EV_CURRENT;
    ehdr->e_ident[EI_OSABI] = ELFOSABI_SYSV;
    ehdr->e_ident[EI_ABIVERSION] = 0;
    ehdr->e_type = ET_EXEC;
    ehdr->e_machine = EM_X86_64;
    ehdr->e_version = EV_CURRENT; // Version for a second time?
    ehdr->e_entry = base_addr + sizeof(Elf64_Ehdr) + sizeof(Elf64_Phdr);
    // Program header immediately follows ELF header.
    ehdr->e_phoff = sizeof(Elf64_Ehdr);
    ehdr->e_shoff = 0;        // No section headers.
    ehdr->e_flags = 0x000000; // Copied from nasm-produced file; idk why 0.
    ehdr->e_ehsize = sizeof(Elf64_Ehdr);
    ehdr->e_phentsize = sizeof(Elf64_Phdr);
    ehdr->e_phnum = 1;
    ehdr->e_shentsize = sizeof(Elf64_Shdr);
    ehdr->e_shnum = 0;
    ehdr->e_shstrndx = 0;

    Elf64_Phdr *phdr = (Elf64_Phdr *)(elf.buf + sizeof(Elf64_Ehdr));
    phdr->p_type = PT_LOAD;
    phdr->p_flags = PF_X | PF_R;
    phdr->p_offset = 0;
    phdr->p_vaddr = base_addr;
    phdr->p_paddr = base_addr;
    phdr->p_filesz = elf.len;
    phdr->p_memsz = elf.len;
    phdr->p_align = 0x1;

    memcpy(elf.buf + ehdr->e_entry - base_addr, code.buf, code.len);

    return elf;
}

// Run the compiled program and read the resulting 8 bytes (i64) from its
// stdout.
Num run_program(Str path) {
    int pipefd[2];
    if (pipe(pipefd) == -1) {
        fprintf(stderr, "Error pipe\n");
        exit(1);
    }

    pid_t pid = fork();
    if (pid == -1) {
        fprintf(stderr, "Error fork\n");
        exit(1);
    }

    if (pid == 0) { // Child
        close(pipefd[0]);
        dup2(pipefd[1], STDOUT_FILENO);
        close(pipefd[1]);
        char *p = str_as_cstr(path);
        execve(p, (char *[]){p, NULL}, (char *[]){NULL});
        fprintf(stderr, "Error execve %s\n", p);
        exit(1);
    } else {
        // Parent
        close(pipefd[1]);
        Num res = 0;
        size_t nb = 0;
        if ((nb = read(pipefd[0], &res, sizeof(res))) != sizeof(res)) {
            fprintf(stderr, "Error read: got only %ld bytes\n", nb);
            exit(1);
        }
        close(pipefd[0]);
        wait(NULL);
        return res;
    }
}

Num mode_compile_ast(Ast *ast, Str outpath) {
    printf("[+] Running AOT compiler\n");
    Str code = jit_ast(ast);

    // printf("    Hexdump of x86_64 machine code\n");
    // hexdump(code);

    Str elf = build_elf(code);
    munmap(code.buf, code.len);
    printf("    Hexdump of final ELF file\n");
    hexdump(elf);

    printf("    Writing ELF to file %.*s\n", (int)outpath.len, outpath.buf);
    write_program_to_file(elf, outpath);

    printf("    Running file %.*s\n", (int)outpath.len, outpath.buf);
    Num res = run_program(outpath);
    printf("    Result: %ld\n", res);
    return res;
}

/*******************************************************************************
 * CLI argument handling. ******************************************************
 ******************************************************************************/

typedef struct {
    bool is_ok;
    union {
        struct {
            Str input; // Expression to calculate.
            enum {
                ModeTest,
                ModeInterpret,
                ModeVm,
                ModeJit,
                ModeCompile,
            } mode;
            union {
                Str compiler_outpath; // Only needed for ModeCompile.
            } modeopts;
        } ok;
    };
} CliArgs;

void usage() { printf("See README for usage information.\n"); }

CliArgs parse_cli_args(int argc, char *argv[]) {
    for (int i = 1; i < argc; i += 1) {
        if (!strcmp(argv[i], "--help")) {
            usage();
            exit(0);
        }
    }

    if (argc == 2 && !strcmp(argv[1], "test")) {
        return (CliArgs){true, .ok.mode = ModeTest};
    }

    if (argc < 3) {
        return (CliArgs){false};
    }

    CliArgs args = {0};
    args.is_ok = true;

    u8 last_arg_pos = 2;
    if (!strcmp(argv[1], "interpret") && argc == 3) {
        args.ok.mode = ModeInterpret;
    } else if (!strcmp(argv[1], "vm") && argc == 3) {
        args.ok.mode = ModeVm;
    } else if (!strcmp(argv[1], "jit") && argc == 3) {
        args.ok.mode = ModeJit;
    } else if (!strcmp(argv[1], "compile") && argc == 4) {
        args.ok.mode = ModeCompile;
        last_arg_pos += 1;
        args.ok.modeopts.compiler_outpath =
            (Str){(u8 *)argv[2], strlen(argv[2])};
    } else {
        return (CliArgs){false};
    }

    args.ok.input = (Str){(u8 *)argv[last_arg_pos], strlen(argv[last_arg_pos])};

    return args;
}

/*******************************************************************************
 * Tests ***********************************************************************
 ******************************************************************************/

// Run each of the different implementations on some random pre-generated
// expressions and make sure the output agrees.
void test() {
    Str input[] = {
        Str("((3582 / (-1388 - ((-1689 * (-1750 - (2038 + (-2421 * 4)))) + "
            "-3950))) - ((-2755 * 3408) + (1687 / -789)))"),
        Str("((((1183 - (883 / ((-975 / 4055) + (355 - ((-1301 * -2206) / "
            "-706))))) + ((-17 - -370) - -3939)) + -2962) * (((((1785 / "
            "3042) "
            "* ((1622 * (-1541 - -334)) / 1503)) * (2948 - 3518)) * 25) - "
            "-1527))"),
        Str("(-1333 - (2872 - 1715))"),
        Str("((-1417 + 713) + (((-3202 + (((((1227 / 1881) + ((1476 / "
            "((-1397 "
            "- 3724) - (-1396 + -3858))) - (-4039 - ((-664 - (-3826 * "
            "((2750 * "
            "((-3495 / -246) / (((((-2466 + 3771) + 2551) + ((((-2250 * "
            "1161) "
            "* -2055) - 3317) * (-931 * (-3232 + -2539)))) / -3674) + "
            "-2477))) "
            "- 1419))) - 3845)))) - (-2342 / 219)) / -1317) / 2898)) - "
            "-2889) "
            "* ((1666 + 1561) + (-2381 - 2695))))"),
        Str("(-1436 + -682)"),
        Str("(1449 * -337)"),
        Str("((((-1788 / -669) / ((((-2587 + 691) - 3024) - ((-1825 * "
            "-771) - "
            "3228)) / 2684)) + (-1469 - (-2412 - (-3935 / 261)))) / 1046)"),
        Str("(1929 * ((2273 / 3293) * 3317))"),
        Str("((-1963 + -3952) + -133)"),
        Str("(-2012 / -1805)"),
        Str("(((-2077 - 933) * 227) / -3669)"),
        Str("((((2288 / 1041) - 2293) / -2838) - -2149)"),
        Str("((-2503 - (290 / (-2287 / -519))) - (2235 * 1563))"),
        Str("((-2966 + -3626) + 251)"),
        Str("(((-3198 + -1696) * -1487) - 459)"),
        Str("(((320 - ((((((735 / (((-482 + -2807) / -291) + ((-2411 * "
            "((((-1653 / -2479) - ((-2925 + -2100) - 2344)) - 3655) - "
            "-2470)) "
            "/ 2145))) + -763) * -1310) * 3315) - -3527) * -3174)) + "
            "((-2148 * "
            "(3341 * -3158)) / -869)) + (466 / (-2584 + ((-109 + (3616 * "
            "884)) "
            "* -3924))))"),
        Str("(-3257 - 47)"),
        Str("(3585 / (4091 + (-4069 / -605)))"),
        Str("(-4050 - (2039 / ((3191 - (2326 - ((1084 + 3288) - (-1164 / "
            "1431)))) * -2790)))"),
        Str("((718 + 2005) / ((2672 + ((((1315 - ((590 + 902) + -3117)) * "
            "3555) + ((((2531 + ((-982 + 23) * 2171)) - ((-803 / 3331) - "
            "-3307)) * (-1548 - ((2373 + ((2086 + 2328) / -2144)) + "
            "3560))) + "
            "-3409)) - -1750)) + 2103))"),
        Str("(877 - (2304 / 2549))"),
    };

    for (size_t i = 0; i < countof(input); i += 1) {
        LexRetRes tokens = lex(input[i]);
        assert(tokens.is_ok);
        ParseRetRes ast_ = parse(tokens.ok.tokens);
        assert(ast_.is_ok);
        Ast *ast = ast_.ok.ast;
        printf("[+] Parsed AST: ");
        print_ast(ast);
        putchar('\n');

        Num res_interpret = mode_interpret_ast(ast);
        putchar('\n');
        Num res_jit = mode_jit_ast(ast);
        putchar('\n');
        Num res_vm = mode_vm_ast(ast);
        putchar('\n');
        Num res_compile = mode_compile_ast(ast, Str("/tmp/out"));
        putchar('\n');

        assert(res_interpret == res_jit && res_interpret == res_vm &&
               res_interpret == res_compile &&
               "Different implementations do not agree with each other on the "
               "resulting value of the evaluated expression");

        putchar('\n');
        putchar('\n');
    }
}

/*******************************************************************************
 * Main ************************************************************************
 ******************************************************************************/

int main(int argc, char *argv[]) {
    CliArgs args = parse_cli_args(argc, argv);
    if (!args.is_ok) {
        fprintf(stderr, "Cli Argument error\n\n");
        usage();
        exit(1);
    }

    switch (args.ok.mode) {

    case ModeTest: test(); break;

    default: {
        LexRetRes tokens = lex(args.ok.input);
        if (!tokens.is_ok) {
            print_lex_error(tokens.err);
            exit(tokens.err.type);
        }

        ParseRetRes ast_ = parse(tokens.ok.tokens);
        if (!ast_.is_ok) {
            print_parse_error(ast_.err);
            exit(ast_.err);
        }

        Ast *ast = ast_.ok.ast;
        printf("[+] Parsed AST: ");
        print_ast(ast);
        putchar('\n');

        switch (args.ok.mode) {
        case ModeInterpret: mode_interpret_ast(ast); break;
        case ModeVm: mode_vm_ast(ast); break;
        case ModeJit: mode_jit_ast(ast); break;
        case ModeCompile:
            mode_compile_ast(ast, args.ok.modeopts.compiler_outpath);
            break;
        default: break;
        }
    } break;
    }

    return 0;
}

// __asm__ volatile("int3"); // Debug break.

// TODO switch from malloc to arena allocation

// TODO update README after new output formats
