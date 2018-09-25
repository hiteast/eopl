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

(define location
  (lambda (x xs)
    (define loc
      (lambda (ys n)
        (cond [(null? ys) #f]
              [(eq? x (car ys)) n]
              [else (loc (cdr ys) (+ n 1))])))
    (loc xs 0)))

;; Define datatype Environment
(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var symbol?)
   (val reference?)
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
                      (let ([n (location search-var p-names)])
                        (if n
                            (newref (proc-val
                                     (procedure (list-ref b-vars n)
                                                (list-ref p-bodies n)
                                                env)))
                            (apply-env saved-env search-var)))))))

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
    ;; infinity memory store
    (initialize-store!)
    (cases program pgm
      (a-program (exp1) (value-of exp1 (init-env))))))

(define repl
  (sllgen:make-rep-loop "-->"
                        value-of-program
                        (sllgen:make-stream-parser scanner grammar)))

;; store
(define empty-store
  (lambda () '()))

;; a scheme variable containing the current state of the store. Initially set to a dummy value.
(define the-store 'uninitialized)

;; get-store :: () -> Sto
(define get-store
  (lambda () the-store))

;; initialize-store! :: () -> Unspecified
(define initialize-store!
  (lambda () (set! the-store (empty-store))))

;; reference? :: SchemeVal -> Bool
(define reference? ; i.e. memory address
  (lambda (v) (number? v)))

;; newref :: ExpVal -> Ref
(define newref             
  (lambda (val)
    (let ([next-ref (length the-store)])
      ; extend current memory, append a new ref, return its address
      (set! the-store (append the-store (list val)))
      ; DEBUG (eopl:printf "next-ref ~s\n" next-ref)
      next-ref)))

;; deref :: Ref -> ExpVal
(define deref    
  (lambda (ref)
    ; list-ref :: List of a * Int -> a
    (list-ref the-store ref)))

;; setref! :: Ref * Expval -> Unspecified
(define setref!
  (lambda (ref val)
    (set! the-store ;; global variable `the-store
          (letrec ([setref-inner (lambda (store1 ref1)
                                   (cond [(null? store1) (report-invalid-reference ref the-store)]
                                         [(zero? ref1) (cons val (cdr store1))]
                                         [else (cons (car store1)
                                                     (setref-inner (cdr store1) (- ref1 1)))]))])
            (setref-inner the-store ref)))))

(define report-invalid-reference
  (lambda (ref store)
    (eopl:error 'setref! "address ~s beyond memory ~s" ref store)))


; Expression value representation
;; DenVal ::= ref(ExpVal)
(define-datatype denval denval?
  (ref-val (ref expval?)))

(define denval->ref
  (lambda (den)
    (cases denval den
      (ref-val (ref) ref))))

;; ExpVal ::= Int + Bool + Proc
(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc proc?))
  (list-val (lst (list-of expval?))))

 ;; accessor of expval
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

(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (lst) lst)
      (else (report-expval-extractor-error 'list val)))))

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (saved-env environment?)))

(define apply-procedure
  (lambda (proc1 expvals)
    (cases proc proc1
      (procedure (vars body saved-env) (letrec ([append-env (lambda (vs es env)
                                                              (if (null? vs)
                                                                  env
                                                                  (extend-env (car vs)
                                                                              (newref (car es))
                                                                              (append-env (cdr vs)
                                                                                          (cdr es)
                                                                                          env))))])
                                         (value-of body (append-env vars expvals saved-env)))))))

(define report-expval-extractor-error
  (lambda (type val)
    (eopl:error 'expval-bool "extract ~s value error from ~s" type val)))

; Program    ::= Expression
;               a-program (exp1)
(define-datatype program program?
  (a-program (exp1 expression?)))

(define-datatype expression expression?
  (const-exp (num number?))
  (var-exp (var symbol?))
  (diff-exp (exp1 expression?) (exp2 expression?))
  ; (plus-exp (exp1 expression?) (exp2 expression?))
  (plus-exp (exps (list-of expression?)))
  ; (mul-exp (exp1 expression?) (exp2 expression?))
  (mul-exp (exps (list-of expression?)))
  (div-exp (exp1 expression?) (exp2 expression?))
  (minus-exp (exp1 expression?))
  (zero?-exp (exp1 expression?))
  (equal?-exp (exp1 expression?) (exp2 expression?))
  (less?-exp (exp1 expression?) (exp2 expression?))
  (greater?-exp (exp1 expression?) (exp2 expression?))
  (cons-exp (exp1 expression?) (exp2 expression?))
  (emptylist-exp)
  (car-exp (exp1 expression?))
  (cdr-exp (exp1 expression?))
  (null?-exp (exp1 expression?))
  (list-exp (lst (list-of expression?)))
  (if-exp (exp1 expression?) (exp2 expression?) (exp3 expression?))
  (cond-exp (tests (list-of expression?)) (jumps (list-of expression?)))
  ; (let-exp (var identifier?) (exp1 expression?) (exp2 expression?))
  (let-exp (vars (list-of identifier?)) (exprs (list-of expression?)) (exp2 expression?))
  (let*-exp (vars (list-of identifier?)) (exprs (list-of expression?)) (exp2 expression?))
  ; (proc-exp (var identifier?) (body expression?))
  (proc-exp (vars (list-of identifier?)) (body expression?))
  ; (call-exp (rator expression?) (rand expression?))
  (call-exp (rator expression?) (rands (list-of expression?)))
  ; (letrec-exp (p-name identifier?) (b-var identifier?) (p-body expression?)
  ; (letrec-body expression?))
  (letrec-exp (p-names (list-of identifier?))
              (b-vars (list-of (list-of identifier?)))
              (p-bodies (list-of expression?))
              (letrec-body expression?))
  (assign-exp (var identifier?) (exp expression?))
  (begin-exp (fst expression?) (rest (list-of expression?))))

; Grammar, Constuct AST
(define grammar
  '((program (expression) a-program)
    (expression (identifier) var-exp)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" (separated-list expression ",") ")") plus-exp)
    (expression ("*" "(" (separated-list expression ",") ")") mul-exp)
    (expression ("/" "(" expression "," expression ")") div-exp)
    (expression ("minus" "(" expression ")") minus-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("=" "(" expression "," expression ")") equal?-exp)
    (expression ("<" "(" expression "," expression ")") less?-exp)
    (expression (">" "(" expression "," expression ")") greater?-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    ;; collect to (cond tests jumps) where tests & jumps are list of expression
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    ; (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("let*" (arbno identifier "=" expression) "in" expression) let*-exp)
    ; (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    ; (expression ("(" expression expression ")") call-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    ; (expression ("letrec" identifier "(" identifier")" "=" expression "in" expression) letrec-exp)
    (expression ("letrec"
                 (arbno identifier "(" (separated-list identifier ",") ")" "=" expression)
                 "in" expression)
                letrec-exp)
    (expression ("set" identifier "=" expression) assign-exp)
    (expression ("begin" expression (arbno ";" expression) "end") begin-exp)))

; Evaluator
(define value-of
  (lambda (exp env)
    (cases expression exp
      ; (value-of (const-exp n) p) = n
      (const-exp (num) (num-val num))
      ; (value-of (var-exp var) p) = (apply-env p var)
      (var-exp (var) (deref (apply-env env var))) ;; each var become a reference
      ; (value-of (diff-exp exp1 exp2) p) = (- ((value-of exp1) p) ((value-of exp1) p))
      (diff-exp (exp1 exp2)
                (let* ([val1 (value-of exp1 env)]
                       [val2 (value-of exp2 env)]
                       [num1 (expval->num val1)]
                       [num2 (expval->num val2)])
                  (num-val (- num1 num2))))
      ; (value-of (diff-exp exp1 exp2) p) = (+ ((value-of exp1) p) ((value-of exp1) p))
      (plus-exp (exps)
                (let* ([vals (map (lambda (exp) (value-of exp env)) exps)]
                       [nums (map (lambda (val) (expval->num val)) vals)])
                  (num-val (foldl + 0 nums))))
      ; (value-of (diff-exp exp1 exp2) p) = (* ((value-of exp1) p) ((value-of exp1) p))
      (mul-exp (exps)
                (let* ([vals (map (lambda (exp) (value-of exp env)) exps)]
                       [nums (map (lambda (val) (expval->num val)) vals)])
                  (num-val (foldl * 1 nums))))
      ; (value-of (diff-exp exp1 exp2) p) = (quotient ((value-of exp1) p) ((value-of exp1) p))
      (div-exp (exp1 exp2)
                (let* ([val1 (value-of exp1 env)]
                      [val2 (value-of exp2 env)]
                      [num1 (expval->num val1)]
                      [num2 (expval->num val2)])
                  (num-val (quotient num1 num2))))
      ; (value-of (minus-exp exp) p) = (value-of (diff-exp (num-val 0) (exp)) p)
      (minus-exp (exp1)
                 (let* ([val (value-of exp1 env)]
                        [num (expval->num val)])
                   (num-val (- num))))
      ; (value-of (zero?-exp exp1) p) =
      ; (bool-exp #t) if (expval->num val1) == 0
      ; (bool-exp #f) if (expval->num val1) != 0
      (zero?-exp (exp1) (let* ([val (value-of exp1 env)]
                               [num (expval->num val)])
                          (bool-val (eqv? num 0))))
      (equal?-exp (exp1 exp2) (let* ([val1 (value-of exp1 env)]
                                    [val2 (value-of exp2 env)]
                                    [num1 (expval->num val1)]
                                    [num2 (expval->num val2)])
                                (bool-val (= num1 num2))))
      (less?-exp (exp1 exp2) (let* ([val1 (value-of exp1 env)]
                                    [val2 (value-of exp2 env)]
                                    [num1 (expval->num val1)]
                                    [num2 (expval->num val2)])
                               (bool-val (< num1 num2))))
      (greater?-exp (exp1 exp2) (let* ([val1 (value-of exp1 env)]
                                       [val2 (value-of exp2 env)]
                                       [num1 (expval->num val1)]
                                       [num2 (expval->num val2)])
                                  (bool-val (> num1 num2))))
      (cons-exp (exp1 exp2) (let* ([fst (value-of exp1 env)]
                                   [snd (value-of exp2 env)]
                                   [lst (expval->list snd)])
                              (list-val (cons fst lst))))
      ; (value-of (emptylist-exp) p) = `()
      (emptylist-exp () (list-val '()))
      (car-exp (exp1) (let* ([val (value-of exp1 env)]
                             [lst (expval->list val)])
                        (car lst)))
      (cdr-exp (exp1) (let* ([val (value-of exp1 env)]
                             [lst (expval->list val)])
                        (list-val (cdr list))))
      (null?-exp (exp1) (let* ([val (value-of exp1 env)]
                               [lst (expval->list val)])
                          (bool-val (null? lst))))
      (list-exp (lst) (list-val (map (lambda (e) (value-of e env)) lst)))
      ; (value-of (zero?-exp exp1) p) =
      ; (value-of exp2 p) if (expval->bool val1) = #t
      ; (value-of exp3 p) if (expval->bool val1) = #f
      (if-exp (exp1 exp2 exp3) (let ([val1 (value-of exp1 env)])
                                 (if (expval->bool val1)
                                     (value-of exp2 env)
                                     (value-of exp3 env))))
      ; (value-of (cond-exp tests jumps) p) = i-th tests == #t => i-th jumps 
      (cond-exp (tests jumps) (if (null? tests)
                                  (eopl:error `cond-exp "none of condition test success")
                                  (let* ([val (value-of (car tests) env)]
                                         [b (expval->bool val)])
                                    (if b
                                        (value-of (car jumps) env)
                                        (value-of (cond-exp (cdr tests) (cdr jumps)) env)))))
      ; (value-of (let-exp var exp1 body) p) = (value-of body (var=val)p)
      ;; (let-exp (var exp1 exp2) (value-of exp2 (extend-env var (value-of exp1 env) env)))
      (let-exp (vars exprs exp2)
               (letrec ([vals (map (lambda (e) (value-of e env)) exprs)]
                        [append-env (lambda (vs vals env)
                                      (if (null? vs)
                                          env
                                          (extend-env (car vs)
                                                      (newref (car vals)) ;; wrap as reference value
                                                      (append-env (cdr vs)
                                                                  (cdr vals)
                                                                  env))))])
                             (value-of exp2 (append-env vars vals env))))
      ; desugar: let* x in y => (λx.y x)
      (let*-exp (vars exprs exp2)
               (cond [(null? vars) (value-of exp2 env)]
                     [else (let* ([var (car vars)]
                                  [exp (car exprs)]
                                  [val (value-of exp env)])
                             (value-of (let-exp (cdr vars) (cdr exprs) exp2)
                                       (extend-env var (newref val) env)))]))
      ; closure
      ; (proc-exp (var exp1) (proc-val (procedure var exp1 env)))
      (proc-exp (vars exp1) (proc-val (procedure vars exp1 env)))
      ; evaluate a closure = evaluate closure under extend arguments to its env
      (call-exp (rator rands)
                ; DEBUG (eopl:printf "~s\n" rands)
                ; DEBUG (eopl:printf "~s\n" rator)
                (let ([proc (expval->proc (value-of rator env))]
                                    [args (map (lambda (rand) (value-of rand env)) rands)])
                                (apply-procedure proc args)))
      ;; evaluate a closure = evaluate closure under extend arguments to its env
      ;; with env contains function
      (letrec-exp (p-names b-vars p-bodies letrec-body)
                  (value-of letrec-body (extend-env-rec p-names b-vars p-bodies env)))
      (assign-exp (var exp1) ;; assignment expression return value is undefined
                  (begin
                    (setref! (apply-env env var)
                             (value-of exp1 env))
                    (num-val 27)))
      (begin-exp (fst rest)
                 (let* ([exps (cons fst rest)]
                       [vals (map (lambda (exp) (value-of exp env)) exps)])
                   (last vals))))))

(define init-env
  (lambda ()
    (empty-env)))


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

(define let-ast (evaluate "let x = 30 in let x = -(x,1) y = -(x,2) in -(x,y)"))

(define let*-ast (evaluate "let x = 30 in let* x = -(x,1) y = -(x,2) in -(x,y)"))

(define letrec-ast
  (evaluate "letrec odd(x) = if zero?(x) then 0 else (even -(x,1))
                    even(x) = if zero?(x) then 1 else (odd -(x,1))
             in (odd 12)"))

(define counter
  (evaluate "let g = proc()
                      let counter = 0
                      in begin
                           set counter = -(counter, 1);
                           counter
                         end
             in let a = (g 11)
                in let b = (g 11)
                   in -(a,b)"))

((assertEqual 'let) (lambda () 1) (lambda () (expval->num let-ast)))
((assertEqual 'let*) (lambda () 2) (lambda () (expval->num let*-ast)))
((assertEqual 'letrec) (lambda () 0) (lambda () (expval->num letrec-ast)))