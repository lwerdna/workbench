(define fact
  (lambda (n)
    (if (<= n 1)
      1
      (* n (fact (- n 1)))
    )
  )
)
(fact 3)
(fact 50)
