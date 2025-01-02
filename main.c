#include "lib.c"

int main(int argc, char *argv[]) {
    arena_scratch1 = arena_create(0x1000 * 0x1000);
    arena_scratch2 = arena_create(0x1000 * 0x1000);

    CliArgs args = parse_cli_args(argc, argv);
    if (!args.is_ok) {
        fprintf(stderr, "Cli Argument error\n\n");
        usage();
        exit(1);
    }

    switch (args.ok.mode) {

    case ModeTest: test(); break;

    default: {
        ArenaTemp scratch = arena_get_scratch(NULL);

        LexRetRes tokens = lex(scratch.arena, args.ok.input);
        if (!tokens.is_ok) {
            print_lex_error(tokens.err);
            exit(tokens.err.type);
        }

        ParseRetRes ast_ = parse(scratch.arena, tokens.ok.tokens);
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

        arena_release_scratch(scratch);
    } break;
    }

    arena_destroy(&arena_scratch1);
    arena_destroy(&arena_scratch2);

    return 0;
}
