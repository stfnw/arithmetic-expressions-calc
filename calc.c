#include <assert.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

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

TokenList *append_to_list(TokenList *head, Token *token) {
    TokenList *new_head = malloc(sizeof(TokenList));
    new_head->token = token;
    new_head->next = head;
    return new_head;
}

bool is_digit(u8 c) { return '0' <= c && c <= '9'; }

typedef enum {
    LexErrUnexpectedChar = 0x0101,
} LexErrType;

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
            list = append_to_list(list, token);
        }

        else if (s.buf[i] == '+') {
            Token *token = malloc(sizeof(*token));
            token->type = TokenPlusT;
            token->as.numval = 0;
            list = append_to_list(list, token);
            i += 1;
        }

        else if (s.buf[i] == '-') {
            Token *token = malloc(sizeof(*token));
            token->type = TokenMinusT;
            token->as.numval = 0;
            list = append_to_list(list, token);
            i += 1;
        }

        else if (s.buf[i] == '*') {
            Token *token = malloc(sizeof(*token));
            token->type = TokenMultT;
            token->as.numval = 0;
            list = append_to_list(list, token);
            i += 1;
        }

        else if (s.buf[i] == '/') {
            Token *token = malloc(sizeof(*token));
            token->type = TokenDivT;
            token->as.numval = 0;
            list = append_to_list(list, token);
            i += 1;
        }

        else if (s.buf[i] == '(') {
            Token *token = malloc(sizeof(*token));
            token->type = TokenLParenT;
            token->as.numval = 0;
            list = append_to_list(list, token);
            i += 1;
        }

        else if (s.buf[i] == ')') {
            Token *token = malloc(sizeof(*token));
            token->type = TokenRParenT;
            token->as.numval = 0;
            list = append_to_list(list, token);
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

// Print AST as s-expression.
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
        default: assert(false && "Invalid binop type");
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

void print_ast(Ast *ast) {
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

ParseRetRes parse_factor(TokenList *tokens) {
    if (tokens == NULL) {
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

        if (tokens->token->type != TokenNumT) {
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

        if (tokens->token->type != TokenRParenT) {
            return (ParseRetRes){false, .err = ParseErrUnbalancedParanthesis};
        }
        tokens = tokens->next;

        return (ParseRetRes){true, .ok = {.rest = tokens, .ast = r.ok.ast}};
    }

    else {
        return (ParseRetRes){false, .err = ParseErrUnexpectedFactor};
    }
}

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

ParseRetRes parse(TokenList *tokens) {
    ParseRetRes res = parse_expr(tokens);
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
        default: assert(false && "Invalid binop type");
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
        default: assert(false && "Invalid binop type");
        }
    } break;

    default: assert(false && "Invalid symbol type");
    }
}

void vm_bytecode_compile_ast(VM *vm, Ast *ast) {
    vm_bytecode_compile_ast_(vm, ast);
    vm->mem[vm->ip++] = OpExit;
    vm->ip = 0;
}

Num vm_run(VM *vm) {
    while (vm->ip < VM_MEM_SIZE - VM_STACK_SIZE) {
        u8 opcode = vm->mem[vm->ip];
        vm->ip += 1;
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
    u64 i;   // Current position.
} Jit;

typedef Num (*Jitfn)();

// Extend the jits code with given bytes.
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
    jit_push(jit, 1, (((u64)n) >> (0 * 8)) & 0xff); // n in little endian
    jit_push(jit, 1, (((u64)n) >> (1 * 8)) & 0xff); // n in little endian
    jit_push(jit, 1, (((u64)n) >> (2 * 8)) & 0xff); // n in little endian
    jit_push(jit, 1, (((u64)n) >> (3 * 8)) & 0xff); // n in little endian
    jit_push(jit, 1, (((u64)n) >> (4 * 8)) & 0xff); // n in little endian
    jit_push(jit, 1, (((u64)n) >> (5 * 8)) & 0xff); // n in little endian
    jit_push(jit, 1, (((u64)n) >> (6 * 8)) & 0xff); // n in little endian
    jit_push(jit, 1, (((u64)n) >> (7 * 8)) & 0xff); // n in little endian
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
        default: assert(false && "Invalid binop type");
        }
        jit_push(jit, 1, 0x50); // push rax
    } break;

    default: assert(false && "Invalid symbol type");
    }
}

bool matches_function_epilogue(u8 *mem) {
    return mem[0] == 0x5b && mem[1] == 0x5d && mem[2] == 0xc3;
}

void jit_hexdump_program(Str code) {
    for (u64 i = 0; i < code.len; i += 1) {
        if (i % 0x10 == 0 && i != 0) {
            putchar('\n');
        }
        if (i % 0x10 == 0) {
            printf("0x%010lx: ", i);
        }
        if (i % 0x08 == 0) {
            putchar(' ');
        }
        printf("%02x ", code.buf[i]);

        if (i >= 2 && code.len && matches_function_epilogue(code.buf + i - 2)) {
            break;
        }
    }
    putchar('\n');
}

#define JIT_MAX_SIZE 0x1000
// Compile an ast to native x86_64 machine code.
Str jit_ast(Ast *ast) {
    Jit jit = {0};
    jit.n = JIT_MAX_SIZE;
    jit.i = 0;
    jit.mem = mmap(NULL, jit.n, PROT_READ | PROT_WRITE | PROT_EXEC,
                   MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (jit.mem == MAP_FAILED) {
        printf("mmap: Failed to allocate memory");
        exit(1);
    }

    // Function prologue.
    jit_push(&jit, 1, 0x55);             // push rbp
    jit_push(&jit, 3, 0x48, 0x89, 0xe5); // mov  rbp, rsp
    jit_push(&jit, 1, 0x53);             // push rbx (save registers)

    jit_ast_(ast, &jit);
    jit_push(&jit, 1, 0x58); // pop rax (final computed result)

    // Function epilogue.
    jit_push(&jit, 1, 0x5b); //             pop rbx
    jit_push(&jit, 1, 0x5d); //             pop rbp
    jit_push(&jit, 1, 0xc3); //             ret

    Str code = {jit.mem, jit.n};
    return code;
}

Num mode_jit_ast(Ast *ast) {
    printf("[+] Running JIT\n");

    Str code = jit_ast(ast);

    printf("    Hexdump of JIT program\n");
    jit_hexdump_program(code);

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

void mode_compile_ast(Ast *ast) {
    (void)ast;
    assert(false && "TODO Unimplemented");
}

/*******************************************************************************
 * CLI argument handling. ******************************************************
 ******************************************************************************/

typedef struct {
    bool is_ok;
    union {
        struct {
            Str input;
            enum {
                ModeTest,
                ModeInterpret,
                ModeVm,
                ModeJit,
                ModeCompile,
            } mode;
            union {
                Str compiler_outpath;
            } modeopts;
        } ok;
    };
} CliArgs;

void usage() { printf("See README.\n"); }

CliArgs parse_cli_args(int argc, char *argv[]) {
    if (argc >= 2) {
        for (int i = 1; i < argc; i += 1) {
            if (!strcmp(argv[i], "--help")) {
                usage();
                exit(0);
            }
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
        // Num res_compile = mode_compile_ast(ast);
        putchar('\n');

        assert(res_interpret == res_jit && res_interpret == res_vm);
        // && res_interpret = res_compile

        // TODO add other missing implementations
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
        case ModeCompile: mode_compile_ast(ast); break;
        default: break;
        }
    } break;
    }

    return 0;
}

// __asm__ volatile("int3"); // Debug break.

// TODO switch from malloc to arena allocation

// TODO review code and maybe add comments where necessary.
