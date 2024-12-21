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

TODO

## AOT compiler

TODO
