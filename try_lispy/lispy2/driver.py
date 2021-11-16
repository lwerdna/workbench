#!/usr/bin/env python

# "driver" for the lispy implementation

import os, sys, inspect

import lispy

if __name__ == '__main__':
    arg0 = sys.argv[1] if sys.argv[1:] else None

    if arg0 == None:
        lispy.repl()

    elif arg0 == 'test':
        tests = [
            ("()", SyntaxError),
            ("(set! x)", SyntaxError),
            ("(define 3 4)", SyntaxError),
            ("(quote 1 2)", SyntaxError),
            ("(if 1 2 3 4)", SyntaxError),
            ("(lambda 3 3)", SyntaxError),
            ("(lambda (x))", SyntaxError),
            ("""(if (= 1 2) (define-macro a 'a)
                (define-macro a 'b))""", SyntaxError),
            ("(define (twice x) (* 2 x))", None),
            ("(twice 2)", 4),
            ("(twice 2 2)", TypeError),
            ("(define lyst (lambda items items))", None),
            ("(lyst 1 2 3 (+ 2 2))", [1,2,3,4]),
            ("(if 1 2)", 2),
            ("(if (= 3 4) 2)", None),
            ("(define ((account bal) amt) (set! bal (+ bal amt)) bal)", None),
            ("(define a1 (account 100))", None),
            ("(a1 0)", 100),
            ("(a1 10)", 110),
            ("(a1 10)", 120),
            ("""
            (define (newton guess function derivative epsilon)
                (define guess2 (- guess (/ (function guess) (derivative guess))))
                (if (< (abs (- guess guess2)) epsilon) guess2
                    (newton guess2 function derivative epsilon)
                )
            )""", None),
            ("""
            (define (square-root a)
                (newton 1 (lambda (x) (- (* x x) a))
                    (lambda (x) (* 2 x)) 1e-8)
            )""", None),
            ("(> (square-root 200.) 14.14213)", True),
            ("(< (square-root 200.) 14.14215)", True),
            ("(= (square-root 200.) (sqrt 200.))", True),
            ("""(define (sum-squares-range start end)
                 (define (sumsq-acc start end acc)
                    (if (> start end) acc (sumsq-acc (+ start 1) end (+ (* start start) acc))))
                 (sumsq-acc start end 0))""", None),
            ("(sum-squares-range 1 3000)", 9004500500), ## Tests tail recursion
            ("(call/cc (lambda (throw) (+ 5 (* 10 (throw 1))))) ;; throw", 1),
            ("(call/cc (lambda (throw) (+ 5 (* 10 1)))) ;; do not throw", 15),
            ("""(call/cc (lambda (throw)
                 (+ 5 (* 10 (call/cc (lambda (escape) (* 100 (escape 3)))))))) ; 1 level""", 35),
            ("""(call/cc (lambda (throw)
                 (+ 5 (* 10 (call/cc (lambda (escape) (* 100 (throw 3)))))))) ; 2 levels""", 3),
            ("""(call/cc (lambda (throw)
                 (+ 5 (* 10 (call/cc (lambda (escape) (* 100 1))))))) ; 0 levels""", 1005),
            ("(* 1i 1i)", -1),
            ("(sqrt -1)", 1j),
            ("(let ((a 1) (b 2)) (+ a b))", 3),
            ("(let ((a 1) (b 2 3)) (+ a b))", SyntaxError),
            ("(and 1 2 3)", 3),
            ("(and (> 2 1) 2 3)", 3),
            ("(and)", True),
            ("(and (> 2 1) (> 2 3))", False),
            ("(define-macro unless (lambda args `(if (not ,(car args)) (begin ,@(cdr args))))) ; test `", None),
            ("(unless (= 2 (+ 1 1)) (display 2) 3 4)", None),
            (r'(unless (= 4 (+ 1 1)) (display 2) (display "\n") 3 4)', 4),
            ("(quote x)", 'x'),
            ("(quote (1 2 three))", [1, 2, 'three']),
            ("'x", 'x'),
            ("'(one 2 3)", ['one', 2, 3]),
            ("(define L (list 1 2 3))", None),
            ("`(testing ,@L testing)", ['testing',1,2,3,'testing']),
            ("`(testing ,L testing)", ['testing',[1,2,3],'testing']),
            ("`,@L", SyntaxError),
            ("""'(1 ;test comments '
             ;skip this line
             2 ; more ; comments ; ) )
             3) ; final comment""", [1,2,3]),
            ]

        for (x, expected) in tests:
            result = ''

            try:
                result = lispy.eval(lispy.parse(x))
                print(x, '=>', lispy.to_string(result))
                ok = (result == expected)
            except Exception as e:
                print(x, '=raises=>', type(e).__name__, e)
                ok = inspect.isclass(expected) and issubclass(expected, Exception) and isinstance(e, expected)
            if not ok:
                print('expression: %s' % x)
                print('    actual: %s' % result)
                print('  expected: %s' % expected)
                break
        else:
            print('PASS')

    else:
        # argument is assumed to be a file
        assert os.path.isfile(arg0)
        data = open(arg0).read()
        exprs = []
        stack = []
        for (i,c) in enumerate(data):
            if c == '(':
                stack.append(i)
            elif c == ')':
                if len(stack)==1:
                    exprs.append(data[stack[0]:i+1])
                stack.pop()
        #print('read %d expressions' % len(exprs))
        for (i,expr) in enumerate(exprs):
            #print('expr%d: %s' % (i, expr))
            #print('tokens: %s' % ', '.join(['"%s"'%t for t in lispy.tokenize(expr)]))
            print(lispy.eval(lispy.parse(expr)))
