set 0x0 1
mov 0x1 0x0
mov 0x2 0x0
; fib(1)
out 0x2 1
add 0x0 0x0 0x1
mov 0x2 0x0
; fib(2)
out 0x2 2
add 0x1 0x0 0x1
mov 0x2 0x1
; fib(3)
out 0x2 3
add 0x0 0x0 0x1
mov 0x2 0x0
; fib(4)
out 0x2 5
add 0x1 0x0 0x1
mov 0x2 0x1
; fib(5)
out 0x2 8