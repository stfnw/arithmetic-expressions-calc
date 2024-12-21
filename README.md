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

[+] Running JIT
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

TODO
