Exploring various kinds of program execution like

  - interpreter
  - VM (virtual machine)
  - JIT (just-in-time) compiler
  - AOT (ahead-of-time) compiler

with arithmetic expressions as an example.

# Usage

```
calc [interpret | vm | jit | compile outfile] expr
```

`expr` is an arithmetic expression.
The program only supports signed 64 bit integers, and the operations addition, subtraction, multiplication, and division.
Expressions can be explicitly grouped using parenthesis;
but operators also follow the usual precedence rules regarding unary minus, multiplication / division, and addition / subtraction.

# Tests

```
./calc test
```

This computes the result for some pre-generated random arithmetic instructions using each implemented method and asserts that all methods agree with each other on the expression value.

# Example runs

(from 24b51bb160ec670caf0fb0cfc5a6d6d2ced34f12)

## Interpreter

```
$ ./calc interpret "3 * 2 + 2 / 10 / 19 + (3/10) * 4 / 10 + 2 * (4+5) + 9"
[+] Parsed AST: (+ (+ (+ (+ (* 3 2) (/ (/ 2 10) 19)) (/ (* (/ 3 10) 4) 10)) (* 2 (+ 4 5))) 9)

[+] Interpreting AST
    Result: 33
```

## VM

```
$ ./calc vm "3 * 2 + 2 / 10 / 19 + (3/10) * 4 / 10 + 2 * (4+5) + 9"
[+] Parsed AST: (+ (+ (+ (+ (* 3 2) (/ (/ 2 10) 19)) (/ (* (/ 3 10) 4) 10)) (* 2 (+ 4 5))) 9)

[+] Running VM
    VM instruction stream:
         OpPush 3
         OpPush 2
         OpMul
         OpPush 2
         OpPush 10
         OpDiv
         OpPush 19
         OpDiv
         OpAdd
         OpPush 3
         OpPush 10
         OpDiv
         OpPush 4
         OpMul
         OpPush 10
         OpDiv
         OpAdd
         OpPush 2
         OpPush 4
         OpPush 5
         OpAdd
         OpMul
         OpAdd
         OpPush 9
         OpAdd
         OpExit
    Result: 33
```

## JIT compiler

```
$ ./calc jit "3 * 2 + 2 / 10 / 19 + (3/10) * 4 / 10 + 2 * (4+5) + 9"
[+] Parsed AST: (+ (+ (+ (+ (* 3 2) (/ (/ 2 10) 19)) (/ (* (/ 3 10) 4) 10)) (* 2 (+ 4 5))) 9)

[+] Running JIT compiler
    Hexdump of JIT program
0x0000000000:  55 48 89 e5 53 48 b8 03  00 00 00 00 00 00 00 50
0x0000000010:  48 b8 02 00 00 00 00 00  00 00 50 5b 58 48 f7 eb
0x0000000020:  50 48 b8 02 00 00 00 00  00 00 00 50 48 b8 0a 00
0x0000000030:  00 00 00 00 00 00 50 5b  58 48 99 48 f7 fb 50 48
0x0000000040:  b8 13 00 00 00 00 00 00  00 50 5b 58 48 99 48 f7
0x0000000050:  fb 50 5b 58 48 01 d8 50  48 b8 03 00 00 00 00 00
0x0000000060:  00 00 50 48 b8 0a 00 00  00 00 00 00 00 50 5b 58
0x0000000070:  48 99 48 f7 fb 50 48 b8  04 00 00 00 00 00 00 00
0x0000000080:  50 5b 58 48 f7 eb 50 48  b8 0a 00 00 00 00 00 00
0x0000000090:  00 50 5b 58 48 99 48 f7  fb 50 5b 58 48 01 d8 50
0x00000000a0:  48 b8 02 00 00 00 00 00  00 00 50 48 b8 04 00 00
0x00000000b0:  00 00 00 00 00 50 48 b8  05 00 00 00 00 00 00 00
0x00000000c0:  50 5b 58 48 01 d8 50 5b  58 48 f7 eb 50 5b 58 48
0x00000000d0:  01 d8 50 48 b8 09 00 00  00 00 00 00 00 50 5b 58
0x00000000e0:  48 01 d8 50 58 5b 5d c3
    Result: 33
```

## AOT compiler

```

$ ./calc compile /tmp/out "3 * 2 + 2 / 10 / 19 + (3/10) * 4 / 10 + 2 * (4+5) + 9"
[+] Parsed AST: (+ (+ (+ (+ (* 3 2) (/ (/ 2 10) 19)) (/ (* (/ 3 10) 4) 10)) (* 2 (+ 4 5))) 9)

[+] Running AOT compiler
    Hexdump of final ELF file
0x0000000000:  7f 45 4c 46 02 01 01 00  00 00 00 00 00 00 00 00
0x0000000010:  02 00 3e 00 01 00 00 00  78 00 40 00 00 00 00 00
0x0000000020:  40 00 00 00 00 00 00 00  00 00 00 00 00 00 00 00
0x0000000030:  00 00 00 00 40 00 38 00  01 00 40 00 00 00 00 00
0x0000000040:  01 00 00 00 05 00 00 00  00 00 00 00 00 00 00 00
0x0000000050:  00 00 40 00 00 00 00 00  00 00 40 00 00 00 00 00
0x0000000060:  86 01 00 00 00 00 00 00  86 01 00 00 00 00 00 00
0x0000000070:  01 00 00 00 00 00 00 00  e8 21 00 00 00 50 b8 01
0x0000000080:  00 00 00 bf 01 00 00 00  48 89 e6 ba 08 00 00 00
0x0000000090:  0f 05 b8 3c 00 00 00 bf  00 00 00 00 0f 05 55 48
0x00000000a0:  89 e5 53 48 b8 03 00 00  00 00 00 00 00 50 48 b8
0x00000000b0:  02 00 00 00 00 00 00 00  50 5b 58 48 f7 eb 50 48
0x00000000c0:  b8 02 00 00 00 00 00 00  00 50 48 b8 0a 00 00 00
0x00000000d0:  00 00 00 00 50 5b 58 48  99 48 f7 fb 50 48 b8 13
0x00000000e0:  00 00 00 00 00 00 00 50  5b 58 48 99 48 f7 fb 50
0x00000000f0:  5b 58 48 01 d8 50 48 b8  03 00 00 00 00 00 00 00
0x0000000100:  50 48 b8 0a 00 00 00 00  00 00 00 50 5b 58 48 99
0x0000000110:  48 f7 fb 50 48 b8 04 00  00 00 00 00 00 00 50 5b
0x0000000120:  58 48 f7 eb 50 48 b8 0a  00 00 00 00 00 00 00 50
0x0000000130:  5b 58 48 99 48 f7 fb 50  5b 58 48 01 d8 50 48 b8
0x0000000140:  02 00 00 00 00 00 00 00  50 48 b8 04 00 00 00 00
0x0000000150:  00 00 00 50 48 b8 05 00  00 00 00 00 00 00 50 5b
0x0000000160:  58 48 01 d8 50 5b 58 48  f7 eb 50 5b 58 48 01 d8
0x0000000170:  50 48 b8 09 00 00 00 00  00 00 00 50 5b 58 48 01
0x0000000180:  d8 50 58 5b 5d c3
    Writing ELF to file /tmp/out
    Running file /tmp/out
    Result: 33
```

# A note on memory handling

I learned of arena allocation during this project, which came in very handy.
Valgrind output on `48c03fc`:


```
$ valgrind ./calc test > /dev/null
==205044== Memcheck, a memory error detector
==205044== Copyright (C) 2002-2024, and GNU GPL'd, by Julian Seward et al.
==205044== Using Valgrind-3.24.0 and LibVEX; rerun with -h for copyright info
==205044== Command: ./calc test
==205044==
==205044==
==205044== HEAP SUMMARY:
==205044==     in use at exit: 0 bytes in 0 blocks
==205044==   total heap usage: 43 allocs, 43 frees, 100,024 bytes allocated
==205044==
==205044== All heap blocks were freed -- no leaks are possible
==205044==
==205044== For lists of detected and suppressed errors, rerun with: -s
==205044== ERROR SUMMARY: 0 errors from 0 contexts (suppressed: 0 from 0)
```
