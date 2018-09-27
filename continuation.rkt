#lang eopl

;; Some until function
(define identifier?
  (lambda (sym)
    (and (symbol? sym) (not (eqv? sym 'lambda)))))

(define foldl
  (lambda (op init xs)
    (if (null? xs)
        init
        (foldl op (op init (car xs)) (cdr xs)))))

(define filter
  (lambda (pred? xs)
    (cond [(null? xs) '()]
          [(pred? (car xs)) (cons (car xs) (filter pred? (cdr xs)))]
          [else (filter (cdr xs))])))

(define last
  (lambda (xs)
    (cond [(null? xs) (eopl:error `last " apply to empty list")]
          [(null? (cdr xs)) (car xs)]
          [else (last (cdr xs))])))

;; Define datatype Environment
(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var symbol?)
   (val expval?)
   (env environment?))
  (extend-env-rec
   (p-name (list-of identifier?))
   (b-vars (list-of (list-of identifier?)))
   (bodies (list-of expression?))
   (env environment?)))

; Environment * Symbol -> ExpVal
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env () (report-no-binding-found search-var))
      (extend-env (var val env1) (if (eqv? var search-var)
                                     val
                                     (apply-env env1 search-var)))
      ; (extend-env-rec (p-name b-var p-body saved-env)
      ;  (if (eqv? search-var p-name)
      ;      (prov-val (procedure b-var p-body env)) ;; not saved-env but env to find fun name again
      ;      (apply-env saved-env search-env)))
      (extend-env-rec (p-names b-vars p-bodies saved-env)
                      (letrec ([find (lambda (names vars bodies)
                                       (cond [(null? names) (apply-env saved-env search-var)]
                                             [(eqv? search-var (car names))
                                              (proc-val (procedure (car vars) (car bodies) env))]
                                             [else (find (cdr names) (cdr vars) (cdr bodies))]))])
                        (find p-names b-vars p-bodies))))))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error `apply-env "No binding for ~s" search-var)))

; Scannar & Parser & REPL
(define scanner
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

(define scan
  (sllgen:make-string-scanner scanner grammar))

(define scan&parse
  (sllgen:make-string-parser scanner grammar))

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (value-of/k exp1 (init-env) (end-cont))))))

(define repl
  (sllgen:make-rep-loop "-->"
                        value-of-program
                        (sllgen:make-stream-parser scanner grammar)))

; Expression value representation
(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc proc?))
  (list-val (lst (list-of expval?))))

(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (lst) lst)
      (else (report-expval-extractor-error 'list val)))))

(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))

(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (report-expval-extractor-error 'bool val)))))

(define expval->proc
  (lambda (val)
    (cases expval val
      (proc-val (proc) proc)
      (else (report-expval-extractor-error 'proc val)))))

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (saved-env environment?)))

(define apply-procedure/k
  (lambda (proc1 vals cont) 
    (cases proc proc1
      (procedure (vars body saved-env)
                 (letrec ([extend-envs (lambda (vars vals env)
                                         (if (null? vars)
                                             env
                                             (extend-env (car vars)
                                                         (car vals)
                                                         (extend-envs (cdr vars)
                                                                      (cdr vals)
                                                                      env))))])
                   (value-of/k body (extend-envs vars vals saved-env) cont))))))

(define report-expval-extractor-error
  (lambda (type val)
    (eopl:error 'expval "extract ~s value error from ~s" type val)))

; Program    ::= Expression
;               a-program (exp1)
(define-datatype program program?
  (a-program (exp1 expression?)))

(define-datatype expression expression?
  (const-exp (num number?))
  (var-exp (var symbol?))
  (add-exp (exp1 expression?) (exps (list-of expression?)))
  (diff-exp (exp1 expression?) (exp2 expression?))
  (mul-exp (exp1 expression?) (exps (list-of expression?)))
  (div-exp (exp1 expression?) (exp2 expression?))
  (zero?-exp (exp1 expression?))
  (if-exp (exp1 expression?) (exp2 expression?) (exp3 expression?))
  (let-exp (vars (list-of identifier?)) (exps  (list-of expression?)) (body expression?))
  (emptylist-exp)
  (cons-exp (exp1 expression?) (exp2 expression?))
  (list-exp (lst (list-of expression?)))
  (proc-exp (vars (list-of identifier?)) (body expression?))
  (call-exp (rator expression?) (rands (list-of expression?)))
  (letrec-exp (p-names (list-of identifier?))
              (b-vars (list-of (list-of identifier?)))
              (p-bodies (list-of expression?))
              (letrec-body expression?)))

; Grammar, Constuct AST
(define grammar
  '((program (expression) a-program)
    (expression (identifier) var-exp)
    (expression (number) const-exp)
    (expression ("+" "(" expression (arbno "," expression) ")") add-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("*" "(" expression (arbno "," expression) ")") mul-exp)
    (expression ("/" "(" expression "," expression ")") div-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letrec"
                 (arbno identifier "(" (separated-list identifier ",") ")" "=" expression)
                 "in" expression)
                letrec-exp)))

#|
(define end-cont
  (lambda ()
    (lambda (val) ;; previous passing value
      (begin (eopl:printf "End of Computation.~%") val))))

(define zero1-cont
  (lambda (cont)
    (lambda (val)
      (apply-cont cont (bool-val (zero? (expval->num val)))))))

(define let-exp-cont
  (lambda (var body env cont)
    (lambda (val)
      (value-of/k body (extend-env var val env) cont))))

(define if-test-cont
  (lambda (exp2 exp3 env cont)
    (lambda (val)
      (if (expval->bool val)
          (value-of/k exp2 env cont)
          (value-of/k exp3 env cont)))))

(define diff1-cont
  (lambda (exp2 cont)
    (lambda (val)
      (value-of/k exp2 env (diff2-cont val1 cont)))))

(define diff2-cont
  (lambda (val1 cont)
    (lambda (val2)
      (let ([n1 (expval->num val1)]
            [n2 (expval->num val2)])
        (apply cont (num-val (- n1 n2)))))))

(define rator-cont
  (lambda (rand env cont)
    (lambda (val)
      (value-of/k rand env (rand-cont val cont)))))

(define rand-cont
  (lambda (val1 cont)
    (lambda (val)
      (apply-procedure/k (expval-> proc val1) val cont))))
|#
(define-datatype continuation continuation?
  (end-cont)
  (add1-cont
   (exps (list-of expression?))
   (env environment?)
   (cont continuation?))
  (add2-cont
   (val expval?)
   (cont continuation?))
  (diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (diff2-cont
   (val expval?)
   (cont continuation?))
  (mul1-cont
   (exps (list-of expression?))
   (env environment?)
   (cont continuation?))
  (mul2-cont
   (val expval?)
   (cont continuation?))
  (div1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (div2-cont
   (val expval?)
   (cont continuation?))
  (zero1-cont
   (cnt continuation?))
  (let-exp-cont
   (vars (list-of identifier?))
   (body expression?)
   (env environment?)
   (cont continuation?))
  (cons1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (cons2-cont
   (val expval?)
   (cont continuation?))
  (list1-cont
   (exps (list-of expression?))
   (env environment?)
   (cont continuation?))
  (list2-cont
   (val expval?)
   (cont continuation?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?))
  (rator-cont
   (rand (list-of expression?))
   (env environment?)
   (cont continuation?))
  (rands-cont
   (val1 expval?)
   (cont continuation?)))

;; type Answer = ExpVal
;; apply-cont :: Cont * ExpVal -> Answer
(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont () (begin
                     (eopl:printf "End of computation.~%")
                     val))
      (add1-cont (exps env saved-cont)
                (value-of/k (list-exp exps) env (add2-cont val saved-cont)))
      (add2-cont (val1 saved-cont)
                 (let ([n (expval->num val1)]
                       [tail (map (lambda (v) (expval->num v)) (expval->list val))])
                   (apply-cont saved-cont (num-val (foldl + n tail)))))
      (diff1-cont (exp2 env saved-cont)
                  (value-of/k exp2 env (diff2-cont val saved-cont)))
      (diff2-cont (val1 cont)
                  (let ([num1 (expval->num val1)]
                        [num2 (expval->num val)])
                    (apply-cont cont (num-val (- num1 num2)))))
      (mul1-cont (exps env saved-cont)
                (value-of/k (list-exp exps) env (mul2-cont val saved-cont)))
      (mul2-cont (val1 saved-cont)
                 (let ([n (expval->num val1)]
                       [tail (map (lambda (v) (expval->num v)) (expval->list val))])
                   (apply-cont saved-cont (num-val (foldl * n tail)))))
      (div1-cont (exp2 env cont)
                  (value-of/k exp2 env (div2-cont val cont)))
      (div2-cont (val1 cont)
                  (let ([num1 (expval->num val1)]
                        [num2 (expval->num val)])
                    (apply-cont cont (num-val (quotient num1 num2)))))
      (zero1-cont (saved-cont)
                  (apply-cont saved-cont
                              (bool-val)
                              (zero? expval->num val)))
      (let-exp-cont (vars body saved-env saved-cont)
                     (let ([vals (expval->list val)])
               
                       (letrec ([extend-envs (lambda (vars vals env)
                                               (if (null? vars)
                                                   env
                                                   (extend-env (car vars)
                                                               (car vals)
                                                               (extend-envs (cdr vars)
                                                                            (cdr vals)
                                                                            env))))])
                         (value-of/k body
                                     (extend-envs vars vals saved-env)
                                     saved-cont))))
      (cons1-cont (exp2 env saved-cont)
                 (value-of/k exp2 env (cons2-cont val saved-cont)))
      (cons2-cont (val1 saved-cont)
                  (let ([tail (expval->list val)])
                    (apply-cont saved-cont (list-val (cons val1 tail)))))
      (list1-cont (exps env saved-cont)
                 (value-of/k (list-exp exps) env (list2-cont val saved-cont)))
      (list2-cont (val1 saved-cont)
                  (let ([tail (expval->list val)])
                    (apply-cont saved-cont (list-val (cons val1 tail)))))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (if (expval->bool val)
                        (value-of/k exp2 saved-env saved-cont)
                        (value-of/k exp3 saved-env saved-cont)))
      (rator-cont (rands env cont)
                  (value-of/k (list-exp rands) env (rands-cont val cont)))
      (rands-cont (val1 cont)
                 (let ([proc1 (expval->proc val1)]
                       [args (expval->list val)])
                   (apply-procedure/k proc1 args cont))))))

; Evaluator
(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      (const-exp (num) (apply-cont cont (num-val num)))
      (var-exp (var) (apply-cont cont (apply-env env var)))
      (add-exp (exp1 exps) (value-of/k exp1 env (add1-cont exps env cont)))
      (diff-exp (exp1 exp2)
                (value-of/k exp1 env (diff1-cont exp2 env cont)))
      (mul-exp (exp1 exps) (value-of/k exp1 env (mul1-cont exps env cont)))
      (div-exp (exp1 exp2)
                (value-of/k exp1 env (div1-cont exp2 env cont)))
      (zero?-exp (exp1) (value-of/k exp1 env (zero1-cont cont)))
      (if-exp (exp1 exp2 exp3)
              (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
      (let-exp (vars exps body)
               (if (null? vars)
                   (value-of/k body env cont)
                   (value-of/k (list-exp exps) env (let-exp-cont vars body env cont))))
      (emptylist-exp () (apply-cont cont (list-val '())))
      (cons-exp (exp1 exp2) (value-of/k exp1 env (cons1-cont exp2 env cont)))
      (list-exp (lst)
                (if (null? lst)
                    (apply-cont cont (list-val '()))
                    (value-of/k (car lst) env (list1-cont (cdr lst) env cont))))
      (proc-exp (vars exp1) (apply-cont cont (proc-val (procedure vars exp1 env))))
      (call-exp (rator rands)
                (value-of/k rator env
                            (rator-cont rands env cont)))
      (letrec-exp (p-names b-vars p-bodies letrec-body)
                  (value-of/k letrec-body (extend-env-rec p-names b-vars p-bodies env) cont)))))

(define init-env
  (lambda ()
    (extend-env 'x (num-val 1) (empty-env))))


;; Test
(define assertEqual
  (lambda (name)
    (lambda (expected actual)
      (let ([e (expected)]
            [a (actual)])
        (if (equal? (expected) (actual))
            (eopl:printf "~s test passed\n" name)
            (eopl:printf "~s test failed expected: ~s but actual: ~s\n" name e a))))))

;; TestCase
(define evaluate
  (lambda (str)
    (value-of-program
     (scan&parse str))))

(define let-ast (evaluate "let x = 30 in let y = -(x,1) in -(x,y)"))
((assertEqual 'let) (lambda () 1) (lambda () (expval->num let-ast)))