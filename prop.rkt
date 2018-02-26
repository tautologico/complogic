#lang racket

(module+ test
  (require rackunit))

(provide (all-defined-out))

(define (mk-and p q)
  `(and ,p ,q))

(define (mk-or p q)
  `(or ,p ,q))

(define (mk-imp p q)
  `(imp ,p ,q))

(define (mk-iff p q)
  `(iff ,p ,q))

(define (binop-arg-pair fm)
  `(,(cadr fm) . ,(caddr fm)))

(define (arg1 fm)
  (cadr fm))

(define (arg2 fm)
  (caddr fm))

(define (rator fm) (car fm))

(define (conjunction? fm)
  (and (list? fm) (equal? (rator fm) 'and)))

(define (disjunction? fm)
  (and (list? fm) (equal? (rator fm) 'or)))

(define (imp? fm)
  (and (list? fm) (equal? (rator fm) 'imp)))

(define (iff? fm)
  (and (list? fm) (equal? (rator fm) 'iff)))

(define (neg? fm)
  (and (list? fm) (equal? (rator fm) 'neg)))

(define (dest-iff fm)
  (if (iff? fm)
      (binop-arg-pair fm)
      (error "dest-iff: Not a biconditional")))

(define (dest-and fm)
  (if (conjunction? fm)
      (binop-arg-pair fm)
      (error "dest-and: Not a conjunction")))

(define (conjuncts fm)
  (if (conjunction? fm)
      (append (conjuncts (cadr fm))
              (conjuncts (caddr fm)))
      (list fm)))

(module+ test
  (check-equal? (dest-iff '(iff P Q)) '(P . Q))
  (check-equal? (dest-and '(and P R)) '(P . R))
  (check-equal? (conjuncts '(and (and P Q) R)) '(P Q R))
  (check-equal? (conjuncts '(and P (or P Q))) '(P (or P Q))))

(define (dest-or fm)
  (if (disjunction? fm)
      (binop-arg-pair fm)
      (error "dest-or: Not a disjunction")))

(define (disjuncts fm)
  (if (disjunction? fm)
      (append (disjuncts (cadr fm))
              (disjuncts (caddr fm)))
      (list fm)))

(define (dest-imp fm)
  (if (imp? fm)
      (binop-arg-pair fm)
      (error "dest-imp: Not an implication")))

(define (antecedent fm)
  (car (dest-imp fm)))

(define (consequent fm)
  (cdr (dest-imp fm)))

(define-syntax let-pair
  (syntax-rules ()
    ((let-pair (x y e1) e2)
     (let* ((x.y e1)
            (x (car x.y))
            (y (cdr x.y)))
       e2))))

(module+ test
  (check-equal? (let-pair (a b (cons 1 2)) (+ a b)) 3)
  (check-equal? (let-pair (p q (dest-and '(and P Q))) (mk-or 'P 'Q)) '(or P Q)))

(define (onatoms f fm)
  (cond [(not (list? fm)) (f fm)]
        [(neg? fm) `(neg ,(onatoms f (cadr fm)))]
        [(conjunction? fm)
         (let-pair (p q (dest-and fm)) `(and ,(onatoms f p) ,(onatoms f q)))]
        [(disjunction? fm)
         (let-pair (p q (dest-or fm)) `(or ,(onatoms f p) ,(onatoms f q)))]
        [(imp? fm)
         (let-pair (p q (dest-imp fm)) `(imp ,(onatoms f p) ,(onatoms f q)))]
        [(iff? fm)
         (let-pair (p q (dest-iff fm)) `(iff ,(onatoms f p) ,(onatoms f q)))]
        [else (error "onatoms: unrecognized formula")]))

(module+ test
  (define (changep at) (if (eq? at 'P) 'PP at))

  (check-equal? (onatoms changep '(imp (or P Q) (and (iff Q R) P)))
                '(imp (or PP Q) (and (iff Q R) PP))))

(define (overatoms f fm b)
  (cond [(not (list? fm)) (f fm b)]
        [(neg? fm) (overatoms f (cadr fm) b)]
        [(or
          (conjunction? fm)
          (disjunction? fm)
          (imp? fm)
          (iff? fm))
         (let-pair (p q (binop-arg-pair fm))
                   (overatoms f p (overatoms f q b)))]
        [else b]))

(define (atom-union f fm)
  (overatoms (lambda (h t) (append (f h) t)) fm '())) ; TODO: setify?

(module+ test
  (check-equal? (atom-union (lambda (x) (list x)) '(imp (or P Q) (and (iff Q R) P)))
                '(P Q Q R P)))

(define (band b1 b2)
  (if (and b1 b2) #t #f))

(define (bor b1 b2)
  (if (or b1 b2) #t #f))

;; TODO change name to avoid conflict with language eval?
(define (eval fm v)
  (cond
    [(eq? fm 'false) #f]
    [(eq? fm 'true) #t]
    [(symbol? fm) (v fm)]
    [(neg? fm) (not (eval (arg1 fm) v))]
    [(conjunction? fm) (band (eval (arg1 fm) v)
                             (eval (arg2 fm) v))]
    [(disjunction? fm) (bor (eval (arg1 fm) v)
                            (eval (arg2 fm) v))]
    [(imp? fm) (bor (not (eval (arg1 fm) v))
                    (eval (arg2 fm) v))]
    [(iff? fm) (= (eval (arg1 fm) v)
                  (eval (arg2 fm) v))]))

;; functions for building valuations
(define empty-valuation '())

(define (valuation alist)
  (lambda (v)
    (cond [(assoc v alist) => cdr]
          [else (error 'valuation "unknown variable in valuation")])))

(module+ test
  (check-equal? (eval '(neg true) empty-valuation) #f)
  (check-equal? (eval '(neg false) empty-valuation) #t)
  (check-equal? (eval '(neg Q) (valuation '((Q . #t)))) #f)
  (check-equal? (eval '(neg Q) (valuation '((Q . #f)))) #t)
  (check-equal? (eval '(and true false) empty-valuation) #f)
  (check-equal? (eval '(and P (neg Q)) (valuation '((P . #t) (Q . #f)))) #t)
  (check-equal? (eval '(and P (neg Q)) (valuation '((P . #t) (Q . #t)))) #f))

#;(define (atoms fm)
  (cond
    [(eq? fm 'false) '()]
    [(eq? fm 'true) '()]
    [(symbol? fm) (list fm)]
    [(neg? fm) (atoms (cadr fm))]
    [(or
      (conjunction? fm)
      (disjunction? fm)
      (imp? fm)
      (iff? fm))
     (let-pair (p q (binop-arg-pair fm))
               (set-union (atoms p) (atoms q)))]))

(define (atoms fm)
  (atom-union list fm))

(module+ test
  (check-true (set=? (atoms '(and (neg P) (or Q (neg R)))) '(P Q R))))

(define (onallvaluations subfn v ats)
  (define (vprime t)
    (lambda (q)
      (if (eq? q (car ats))
          t
          (v q))))
  (cond [(null? ats) (subfn v)]
        [else
         (onallvaluations subfn (vprime #f) (cdr ats))
         (onallvaluations subfn (vprime #t) (cdr ats))]))

(module+ test
  (check-equal? (onallvaluations (lambda (v) #t) empty-valuation '(P Q)) #t))

(define (print-truthtable fm)
  (define ats (atoms fm))
  (define width
    (add1 (apply max (cons 5
                           (map (lambda (a) (string-length (symbol->string a))) ats)))))
  (define (fixw s) (string-append s (make-string (- width (string-length s)) #\space)))
  (define (truthstring p) (fixw (if p "true" "false")))
  (define (mk-row v)
    (define lis (map (lambda (x) (truthstring (v x))) ats))
    (define ans (truthstring (eval fm v)))
    (display (string-join (append lis (list "|" ans))))
    (newline))
  (define separator (make-string (+ (* width (length ats)) 10) #\-))
  (display (string-append (string-join (map (lambda (s) (fixw (symbol->string s))) ats))
                          " | formula"))
  (newline)
  (display separator)
  (newline)
  (onallvaluations mk-row (lambda (x) #f) ats)
  (display separator))
