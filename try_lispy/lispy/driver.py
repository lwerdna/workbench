#!/usr/bin/env python

# "driver" for the lispy implementation

import os, sys

import lispy

if __name__ == '__main__':
    arg0 = sys.argv[1] if sys.argv[1:] else None

    if arg0 == None:
        lispy.repl()

    elif arg0 == 'test':
        tests = [
            ("(quote (testing 1 (2.0) -3.14e159))", ['testing', 1, [2.0], -3.14e159]),
            ("(+ 2 2)", 4),
            ("(+ (* 2 100) (* 1 10))", 210),
            ("(if (> 6 5) (+ 1 1) (+ 2 2))", 2),
            ("(if (< 6 5) (+ 1 1) (+ 2 2))", 4),
            ("(define x 3)", None),
            ("x", 3),
            ("(+ x x)", 6),
            ("(begin (define x 1) (set! x (+ x 1)) (+ x 1))", 3),
            ("((lambda (x) (+ x x)) 5)", 10),
            ("(define twice (lambda (x) (* 2 x)))", None),
            ("(twice 5)", 10),
            ("(define compose (lambda (f g) (lambda (x) (f (g x)))))", None),
            ("((compose list twice) 5)", [10]),
            ("(define repeat (lambda (f) (compose f f)))", None),
            ("((repeat twice) 5)", 20),
            ("((repeat (repeat twice)) 5)", 80),
            ("""(define fact
                  (lambda (n)
                    (if (<= n 1)
                      1
                      (* n (fact (- n 1))))))""", None),
            ("(fact 3)", 6),
            ("(fact 50)", 30414093201713378043612608166064768844377641568960512000000000000),
            ("(define abs (lambda (n) ((if (> n 0) + -) 0 n)))", None),
            ("(list (abs -3) (abs 0) (abs 3))", [3, 0, 3]),
            ("""(define combine
                  (lambda (f)
                    (lambda (x y)
                      (if (null? x) (quote ())
                        (f (list (car x) (car y))
                          ((combine f) (cdr x) (cdr y))
                        )
                      )
                    )
                  ))""", None),
            ("(define zip (combine cons))", None),
                   ("(zip (list 1 2 3 4) (list 5 6 7 8))", [[1, 5], [2, 6], [3, 7], [4, 8]]),
            ("""(define riff-shuffle (lambda (deck) (begin
                (define take (lambda (n seq) (if (<= n 0) (quote ()) (cons (car seq) (take (- n 1) (cdr seq))))))
                (define drop (lambda (n seq) (if (<= n 0) seq (drop (- n 1) (cdr seq)))))
            (define mid (lambda (seq) (/ (length seq) 2)))
                ((combine append) (take (mid deck) deck) (drop (mid deck) deck)))))""", None),
            ("(riff-shuffle (list 1 2 3 4 5 6 7 8))", [1, 5, 2, 6, 3, 7, 4, 8]),
            ("((repeat riff-shuffle) (list 1 2 3 4 5 6 7 8))",  [1, 3, 5, 7, 2, 4, 6, 8]),
            ("(riff-shuffle (riff-shuffle (riff-shuffle (list 1 2 3 4 5 6 7 8))))", [1,2,3,4,5,6,7,8]),
        ]

        for (x, expected) in tests:
            result = lispy.eval(lispy.parse(x))
            if result != expected:
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
