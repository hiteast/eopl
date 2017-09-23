#lang eopl

(define empty-env
  (lambda () (list 'empty-env)))

(define extend-env
  (lambda (var val env)
    (list 'extend-env var val env)))

(define apply-env
  (lambda (env search-var)
    (cond [(eqv? (car env) 'empty-env) (report-no-binding-found)]
          [(eqv? (car env) 'extend-env)
           ;; ('extend-env var val env)
           (let ([saved-var (cadr env)]
                 [saved-val (caddr env)]
                 [saved-env (cadddr env)])
             (if (eqv? search-var saved-var)
                 saved-val
                 (apply-env saved-env search-var)))]
          [else report-invalid-env])))

(define report-no-binding-found
  (lambda (search-var)
     (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-no-let-bindings
  (lambda ()
    (eopl:error "let has no bindings")))

(define report-no-unpack-bindings
  (lambda ()
    (eopl:error "unpack has no bindings")))

(define report-unpack-dismatch-error
  (lambda ()
    (eopl:error "unpack variables dismatch list")))

(define report-none-condition
  (lambda ()
    (eopl:error "Cond expressions none conditions")))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))


(define identifier?
  (lambda (s)
    (and (symbol? s)
         (not (eqv? s 'lambda)))))

(define list-of
  (lambda (pred?)
    (lambda (ls)
      (or (null? ls)
          (and (pred? (car ls))
               ((list-of pred?) (cdr ls)))))))

;; Program ::= Expression
(define-datatype program program?
  (a-program (exp1 expression?)))

;; Expression ::= Number
;;            ::= -(Expression, Expression)
;;            ::= +(Expression, Expression)
;;            ::= *(Expression, Expression)
;;            ::= //(Expression, Expression)
;;            ::= mod(Expression, Expression)
;;            ::= >(Expression, Expression)
;;            ::= >=(Expression, Expression)
;;            ::= <(Expression, Expression)
;;            ::= <=(Expression, Expression)
;;            ::= and(Expression, Expression)
;;            ::= or(Expression, Expression)
;;            ::= not(Expression)
;;            ::= ~ Expression  ;; minus
;;            ::= zero?(Expression)
;;            ::= if Expression then Expression else Expression
;;            ::= identifier
;;            ::= let {identifier = Expression}* in Expression  ;; identifier not influence each
;;            ::= let* {identifier = Expression}* in Expression  ;; identifier influence each
;;            ::= nil   ;; empty list
;;            ::= cons(Expression, Expression)
;;            ::= car(Expression)
;;            ::= cdr(Expression)
;;            ::= list(Expression *(,))
;;            ::= unpack {identifier}* = Expression in Expression
;;            ::= fn (identifier) => Expression  ;; lambda function
;;            ::= fn ({identifier ,}*) => Expression ;; lambda multi-parameters
;;            ::= (Expression Expression)   ;;function apply
;;            ::= (Expression {Expression}*)  ;; multiparameter function apply
;;            ::= letfn identifier(identifier) = Expression in Expression  ;; single parameter function assginment syntax sugar
;;            ::= letfn identifier(identifier*) = Expression in Expression  ;; multi-parameter function assginment syntax sugar
;;TODO: function support recursion

(define just-scan
  (sllgen:make-string-scanner scanner grammar))

(define scan&parse
  (sllgen:make-string-parser scanner grammar))

(define scanner
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

(define grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    ;;    (expression ("+" "(" expression "," expression ")") add-exp)
    (expression ("+" "(" (separated-list expression ",") ")") add-exp)
    ;;    (expression ("*" "(" expression "," expression ")") mult-exp)
    (expression ("*" "(" (separated-list expression ",") ")") mult-exp)
    (expression ("//" "(" expression "," expression ")") quot-exp)
    (expression ("mod" "(" expression "," expression ")") mod-exp) ;; % is comment, replaced by mod
    (expression ("=" "(" expression "," expression ")") eq-exp)
    (expression (">" "(" expression "," expression ")") bigger-exp)
    (expression (">=" "(" expression "," expression ")") bigger-eq-exp)
    (expression ("<" "(" expression "," expression ")") less-exp)
    (expression ("<=" "(" expression "," expression ")") less-eq-exp)
    (expression ("and" "(" expression "," expression ")") and-exp)
    (expression ("or" "(" expression "," expression ")") or-exp)
    (expression ("not" "(" expression ")") not-exp)
    (expression ("~" expression) minus-exp)
    (expression ("zero?" "(" expression ")") zero-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("let*" (arbno identifier "=" expression) "in" expression) let*-exp)
    ;; (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("nil") emptylist)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("cond" (arbno expression "=>" expression) "end") cond-exp)
    (expression ("unpack" (arbno identifier) "=" expression "in" expression) unpack-exp)
    ;;    (expression ("fn" "(" identifier ")" "=>" expression) proc-exp)
    (expression ("fn" "(" (separated-list identifier ",") ")" "=>" expression) proc-exp)
    ;;    (expression ("λ" (arbno identifier) "=>" expression) proc-exp)
    ;;    (expression ("(" expression expression ")") call-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letfn" identifier "(" (separated-list identifier ",") ")" "=" expression "in" expression) letfn-exp)))

(define-datatype expression expression?
  (const-exp (exp1 number?))
  (diff-exp (exp1 expression?)
            (exp2 expression?))
  ;;  (add-exp (exp1 expression?)
  ;;           (exp2 expression?))
  (add-exp (exps (list-of expression?)))
  ;;  (mult-exp (exp1 expression?)
  ;;            (exp2 expression?))
  (mult-exp (exps (list-of expression?)))
  (quot-exp (exp1 expression?)
            (exp2 expression?))
  (mod-exp (exp1 expression?)
           (exp2 expression?))
  (bigger-exp (exp1 expression?)
              (exp2 expression?))
  (bigger-eq-exp (exp1 expression?)
                 (exp2 expression?))
  (eq-exp (exp1 expression?)
          (exp2 expression?))
  (less-exp (exp1 expression?)
            (exp2 expression?))
  (less-eq-exp (exp1 expression?)
               (exp2 expression?))
  (and-exp (exp1 expression?)
           (exp2 expression?))
  (or-exp (exp1 expression?)
          (exp2 expression?))
  (not-exp (exp1 expression?))
  (minus-exp (exp1 expression?))
  (zero-exp (exp1 expression?))
  (if-exp (exp1 expression?)
          (exp2 expression?)
          (exp3 expression?))
  (var-exp (var identifier?))
  ;; let var = exp1 in body
  ;;  (let-exp (var identifier?)
  ;;           (exp1 expression?)
  ;;           (body expression?))
  ;; let {var = exp}* in body
  (let-exp (vars (list-of identifier?))
           (vals (list-of expression?))
           (body expression?))
  (let*-exp (vars (list-of identifier?))
            (vals (list-of expression?))
            (body expression?))
  (emptylist)
  (cons-exp (exp1 expression?)
            (exp2 expression?))
  (car-exp (exp1 expression?))
  (cdr-exp (exp1 expression?))
  (list-exp (exps (list-of expression?)))
  (cond-exp (conds (list-of expression?))
            (results (list-of expression?)))
  (unpack-exp (vars (list-of identifier?))
              (exp1 expression?)
              (body expression?))
  ;;  (proc-exp (var identifier?)
  ;;            (body expression?))
  (proc-exp (vars (list-of identifier?))
            (body expression?))
  ;;  (call-exp (rator expression?)
  ;;            (rand expression?))
  (call-exp (rator expression?)
            (rands (list-of expression?)))
  (letfn-exp (fname identifier?)
             (vars (list-of identifier?))
             (fbody expression?)
             (body expression?)))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (lst-val (lst list?))
  (proc-val (proc procedure?)))

(define expval->num
  (lambda (val)
    (cases expval val
           (num-val (num) num)
           (else (report-expval-extractor-error 'number val)))))

(define expval->bool
  (lambda (val)
    (cases expval val
           (bool-val (bool) bool)
           (num-val (num) (not (= num 0)))
           (else (report-expval-extractor-error 'boolean val)))))

(define expval->lst
  (lambda (val)
    (cases expval val
          (lst-val (lst) lst)
          (else (report-expval-extractor-error 'list val)))))

(define expval->proc
  (lambda (val)
    (cases expval val
           (proc-val (proc) proc)
           (else (report-expval-extractor-error 'proceducre val)))))

(define closure
  (lambda (var body env)
    (lambda (val)
      (value-of body (extend-env var val env)))))

(define apply-closure
  (lambda (proc val)
    (proc val)))

(define report-expval-extractor-error
  (lambda (var val)
    (eopl:error "Error when extract" val 'to var)))

(define value-of-program
  (lambda (prog)
    (cases program prog
           (a-program (exp1)
                      (value-of exp1 (empty-env))))))

(define value-of
  (lambda (exp env)
    (cases expression exp
           (const-exp (var)
                      (num-val var))
           (var-exp (var)
                    (apply-env env var))
           (diff-exp (exp1 exp2)
                     (num-val (- (expval->num (value-of exp1 env))
                                 (expval->num (value-of exp2 env)))))
           ;;           (add-exp (exp1 exp2)
           ;;                    (num-val (+ (expval->num (value-of exp1 env))
           ;;                                (expval->num (value-of exp2 env)))))
           (add-exp (exps)
                    (if (null? exps)
                        (num-val 0)
                        (num-val (+ (expval->num (value-of (car exps) env))
                                    (expval->num (value-of (add-exp (cdr exps)) env))))))
           ;;           (mult-exp (exp1 exp2)
           ;;                     (num-val (* (expval->num (value-of exp1 env))
           ;;                                 (expval->num (value-of exp2 env)))))
           (mult-exp (exps)
                     (if (null? exps)
                         (num-val 1)
                         (num-val (* (expval->num (value-of (car exps) env))
                                     (expval->num (value-of (add-exp (cdr exps)) env))))))
           (quot-exp (exp1 exp2)
                     (num-val (quotient (expval->num (value-of exp1 env))
                                        (expval->num (value-of exp2 env)))))
           (mod-exp (exp1 exp2)
                    (num-val (modulo (expval->num (value-of exp1 env))
                                     (expval->num (value-of exp2 env)))))
           (eq-exp (exp1 exp2)
                   (bool-val (equal? (value-of exp1 env)
                                     (value-of exp2 env))))
           (bigger-exp (exp1 exp2)
                       (bool-val (> (expval->num (value-of exp1 env))
                                    (expval->num (value-of exp2 env)))))
           (bigger-eq-exp (exp1 exp2)
                          (bool-val (>= (expval->num (value-of exp1 env))
                                        (expval->num (value-of exp2 env)))))
           (less-exp (exp1 exp2)
                     (bool-val (< (expval->num (value-of exp1 env))
                                  (expval->num (value-of exp2 env)))))
           (less-eq-exp (exp1 exp2)
                        (bool-val (<= (expval->num (value-of exp1 env))
                                      (expval->num (value-of exp2 env)))))
           (and-exp (exp1 exp2)
                    (bool-val (and (expval->bool (value-of exp1 env))
                                   (expval->bool (value-of exp2 env)))))
           (or-exp (exp1 exp2)
                    (bool-val (or (expval->bool (value-of exp1 env))
                                  (expval->bool (value-of exp2 env)))))
           (not-exp (exp1)
                    (bool-val (not (expval->bool (value-of exp1 env)))))
           (minus-exp (exp1)
                      (num-val (- (expval->num (value-of exp1 env)))))
           (zero-exp (exp)
                     (bool-val (eq? (expval->num (value-of exp env)) 0)))
           (if-exp (exp1 exp2 exp3)
                   (if (expval->bool (value-of exp1 env))
                       (value-of exp2 env)
                       (value-of exp3 env)))
           ;;           (let-exp (var exp1 body)
           ;;                    (value-of body (extend-env var (value-of exp1 env) env)))
           (let-exp (vars exps body)
                    (cond [(or (null? vars)
                               (null? exps))
                           (report-no-let-bindings)]
                          [else (letrec ([eval-env (lambda (old-vars old-exps old-env)
                                                     (if (null? old-vars)
                                                         old-env
                                                         (eval-env (cdr old-vars)
                                                                   (cdr old-exps)
                                                                   (extend-env (car old-vars)
                                                                               (value-of (car old-exps) env)
                                                                               old-env))))])
                                  (value-of body (eval-env vars exps env)))]))
           (let*-exp (vars exps body)
                    (cond [(or (null? vars)
                               (null? exps))
                           (report-no-let-bindings)]   ;; let _ in body
                          [(and (null? (cdr vars))     ;; let var = exp in body
                                (null? (cdr exps)))
                           (value-of body (extend-env (car vars)
                                                      (value-of (car exps) env)
                                                      env))]
                          [else (value-of (let*-exp (cdr vars) (cdr exps) body)
                                          (extend-env (car vars)
                                                      (value-of (car exps) env)
                                                      env))]))
           (emptylist () (lst-val '()))
           (cons-exp (exp1 exp2)
                     (lst-val (cons (value-of exp1 env)
                                    (expval->lst (value-of exp2 env)))))
           (car-exp (exp1)
                    (car (expval->lst (value-of exp1 env))))
           (cdr-exp (exp1)
                    (lst-val (cdr (expval->lst (value-of exp1 env)))))
           (list-exp (exps)
                     (if (null? exps) (lst-val '())
                         (lst-val (cons (value-of (car exps) env)
                                        (expval->lst (value-of (list-exp (cdr exps)) env))))))
           (cond-exp (conds results)
                     (if (null? conds) (report-none-condition)
                         (let ([cnd (car conds)]
                               [res (car results)])
                           ;; exprd => exprv
                           (if (expval->bool (value-of cnd env))
                               (value-of res env)
                               (value-of (cond-exp (cdr conds) (cdr results)) env)))))
           (unpack-exp (vars exp1 body)
                       (if (null? vars)
                           (report-no-unpack-bindings)
                           (letrec ([ls (value-of exp1 env)]
                                    [eval-env (lambda (vrs xs old-env)
                                                (cond [(and (null? vrs)
                                                            (null? xs)) old-env]
                                                      [(or (null? vrs)
                                                           (null? xs)) (report-unpack-dismatch-error)]
                                                      [else (eval-env (cdr vrs)
                                                                      (cdr xs)
                                                                      (extend-env (car vrs)
                                                                                  (car xs)
                                                                                  old-env))]))])
                             (value-of body (eval-env vars
                                                      (expval->lst (value-of exp1 env))
                                                      env)))))
           ;;           (proc-exp (var body)
           ;;                     (proc-val (closure var body env)))
           (proc-exp (vars body)
                     (cond [(null? vars) (lambda () (value-of body env))]
                           [(null? (cdr vars))
                            (proc-val (closure (car vars) body env))]  ;; single parameter
                           [else (proc-val (closure (car vars)
                                                    (proc-exp (cdr vars) body)
                                                    env))]))
           ;;           (call-exp (rator rand)
           ;;                     (apply-closure (expval->proc (value-of rator env))
           ;;                                    (value-of rand env)))
           (call-exp (rator rands)
                     (cond [(null? rands)
                            ((value-of rator env))]
                           [(null? (cdr rands))
                            (apply-closure (expval->proc (value-of rator env))
                                           (value-of (car rands) env))]
                           [else (apply-closure (expval->proc (value-of (call-exp rator (cdr rands)) env))
                                                (value-of (car rands) env))]))
           (letfn-exp (fname vars fbody body)
                      (value-of body (extend-env fname
                                                 (value-of (proc-exp vars fbody) env)
                                                 env))))))

(define repl
  (sllgen:make-rep-loop
   "$ "
   value-of-program
   (sllgen:make-stream-parser scanner grammar)))
