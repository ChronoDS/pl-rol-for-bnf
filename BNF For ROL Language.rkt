#lang pl

;;;;;;;;;;;;;;;;;;;Q1;;;;;;;;;;;;;
#| BNF for the ROL language:
	<ROL>  ::=  {reg-len = <num><RegE>}
	<RegE> ::=   <Bits> | {and <RegE><RegE>} | {or <RegE><RegE>} | {shl<RegE>} | {with {<ID><RegE>} <RegE>} | {<ID>} | {if <Bool> <RegE> <RegE>}
	<Bool> ::=   {false} | {true} | {maj? {<RegE>}} | {geq? {<RegE> <RegE>}}
	<Bits> ::=   0 | 1 | <Bits>...
|#  
 
;; Defining two new types 
(define-type BIT = (U 0 1)) 
(define-type Bit-List = (Listof BIT)) 

;; RegE abstract syntax trees   
(define-type RegE     
[Reg  Bit-List]
[And  RegE RegE]     
[Or   RegE RegE]     
[Shl  RegE]     
[Id   Symbol]     
[With Symbol RegE RegE]     
[Bool Boolean]     
[Geq RegE RegE]     
[Maj RegE]     
[If RegE RegE RegE]) 
 
;; Next is a technical function that converts (casts) ;; (any) list into a bit-list. We use it in parse-sexpr.
(: list->bit-list : (Listof Any) -> Bit-List)  ;; to cast a list of bits as a bit-list  
(define (list->bit-list lst)   
	(cond [(null? lst) null]  
		[(eq? (first lst) 1)(cons 1 (list->bit-list (rest lst)))] 
		[else (cons 0 (list->bit-list (rest lst)))])) 
 
(: parse-sexpr : Sexpr -> RegE)  ;; to convert the main s-expression into ROL
(define (parse-sexpr sexpr)  
 	(match sexpr
          [(list 'reg-len '= (number: n) sexp)
              (if (> n 0)
                  (parse-sexpr-RegL sexp n) ;; remember to make sure specified register length is at least 1  
		  (error 'parse-sexpr "Register length must be at least 1 ~s" sexpr))]))
(: parse-sexpr-RegL : Sexpr Number -> RegE)  ;; to convert s-expressions into RegEs
(define (parse-sexpr-RegL sexpr reg-len)
   (match sexpr   
	[(list (and a (or 1 0)) ... )
         (if (= reg-len(length a)) (Reg (list->bit-list a))
             (error 'parse-sexpr "wrong number of bits in ~s" a))]
	[(list 'and l1 l2) (And (parse-sexpr-RegL l1 reg-len) (parse-sexpr-RegL l2 reg-len))]
        [(list 'or l1 l2)  (Or (parse-sexpr-RegL l1 reg-len)  (parse-sexpr-RegL l2 reg-len))]
	[(list 'shl R) (Shl (parse-sexpr-RegL R reg-len))]
        [(list 'geq? a b) (Geq (parse-sexpr-RegL a reg-len)(parse-sexpr-RegL b reg-len))]
        [(list 'maj? a) (Maj (parse-sexpr-RegL a reg-len))]
        [(symbol: id) (match id
        ;;This was treacky one. We cahnged it only when we discovered that the boolean value was read as Id.
                        [(symbol: 'true)  (Bool #t)]
                        [(symbol: 'false) (Bool #f)]
                        [(symbol: id) (Id id)])]
        [(cons 'with args)
         (match sexpr
         [(list 'with (list (symbol: name) named-expr) body)
          (With name (parse-sexpr-RegL named-expr reg-len)(parse-sexpr-RegL body reg-len))]
           [else (error 'parse-sexpr-RegL "bad 'with syntax in ~s" sexpr)])]
        [(list 'if a b c) (If (parse-sexpr-RegL a reg-len)(parse-sexpr-RegL b reg-len)(parse-sexpr-RegL c reg-len))]
	[else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))
        ;[(boolean: b) (Bool b)] isn't required, since there isn't a way to recieve boolean here.
 
(: parse : String -> RegE)  ;; parses a string containing a RegE expression to a RegE AST  
(define (parse str)
       (parse-sexpr (string->sexpr str)))

;;;;;;;;;;;;;;;;;Q2;;;;;;;;;;;;;;;;;
;It actually took us several minutes to complete q2.
;It was difficult to understand we need another name for boolean, other than the typical Bool.

(define-type RES
  [RegV Bit-List]
  [boo Boolean])

;;;;;;;;;;;;;;;;;Q3;;;;;;;;;;;;;;;;;


 #| Formal specs for `subst': 
     (`BL' is a Bit-List, `E1', `E2' are <RegE>s, `x' is some <id>, `y' is a *different* <id>, ‘BOOL’ is Boolean ) 
        BL[v/x]                = BL 
        BOOL[v/x]                = BOOL 
        {and E1 E2}[v/x]      = {and E1[v/x] E2[v/x]} 
        {or E1 E2}[v/x]       = {or E1[v/x] E2[v/x]} 
        {shl E}[v/x]          = {shl E[v/x]} 
        y[v/x]                = y 
        x[v/x]                = v 
        {with {y E1} E2}[v/x] = {with {y E1[v/x]} E2[v/x]} 
        {with {x E1} E2}[v/x] = {with {x E1[v/x]} E2} 
    {if {E1} E2 E3}[v/x] = {if {E1[v/x]} E2[v/x] E3[v/x]} 
    {maj? E1}[v/x] = {maj? E1[v/x] } 
       {geq? E1}[v/x] = {geq? E1[v/x] } 
  |#
;;there is a problem in those formal specs: geq? should conatin E1 and E2, not only E1.


(: subst : RegE Symbol RegE -> RegE)
;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument


(define (subst expr from to)
  (cases expr
	[(Reg a) expr]
	[(And a b) (And (subst a from to) (subst b from to))]     
	[(Or  a b) (Or  (subst a from to) (subst b from to))]     
	[(Shl a)   (Shl (subst a from to))]
	[(Id  name) (if (eq? name from) to expr)]	;;if the name of ID equals, it should be replaced. otherwise- don't touch     
	[(With name named-Reg body)
	        (With name (subst named-Reg from to) (if (eq? name from) body  ;;if name==from, this is a new binding instance, we still need to replace in named-Reg
                                                     (subst body from to)))]    
	[(Bool a) expr]
	[(Geq a b) (Geq (subst a from to) (subst b from to))] 
	[(Maj a) (Maj (subst a from to))]
	[(If a b c) (If (subst a from to)(subst b from to)(subst c from to))]))

;;[else (error 'subst "bad 'with syntax in ~s" expr)]))  ;;I really don't know why we don't need an else here.

;;;;;;;;;;;;;;;;;;;Q4;;;;;;;;;;;;;;;;
;We tried to do something unorthodox in the helper functions. 

#| Formal specs for `eval':
 eval(Reg) = Reg
 eval(bl) = bl
 eval(true) = true
 eval(false) = false
 eval({and E1 E2}) = (<x1 bit-and y1> <x2 bit-and y2> ... <xk bit-and yk>), where eval(E1) = (x1 x2 ... xk) and eval(E2) = (y1 y2 ... yk)
 eval({or E1 E2}) = (<x1 bit-or y1> <x2 bit-or y2> ... <xk bit-or yk>,) where eval(E1) = (x1 x2 ... xk) and eval(E2) = (y1 y2 ... yk)
 eval({shl E}) = (x2 ... xk x1), where eval(E) = (x1 x2 ... xk)
 eval({with {x E1} E2}) = eval(E2[eval(E1)/x])
 eval({if E1 E2 E3}) = eval(E3) if eval(E1) = false
                     = eval(E2) otherwise
 eval({maj? E}) = true if x1+x2+...+xk >= k/2, and false otherwise, where eval(E) = (x1 x2 ... xk)
 eval({geq? E1 E2}) = true if x_i >= y_i, where eval(E1) = (x1 x2 ... xk) and eval(E2) = (y1 y2 ... yk) and i is the first index s.t. x_i and y_i are not equal (or i =k if all are equal)
 eval({if Econd Edo Eelse}) = eval(Edo) if eval(Econd) = true,
                            = eval(Eelse), otherwise.
|#

;It's a good thing that I am TAing Logic Systems, why do you thing and && or are arithmetical operations? they are logical!!

;; Defining functions for dealing with arithmetic operations
;; on the above types
(: bit-and : BIT BIT -> BIT) ;; Arithmetic and
(define(bit-and a b)
  (if (eq? a b) a 0)) 
(: bit-or : BIT BIT -> BIT) ;; Aithmetic or
(define(bit-or a b)
  (if (eq? a b) a 1))

;It's a good thing that I am TAing Logic Systems, why do you thing and && or are arithmetical operations? they are logical!!

(: reg-arith-op : (BIT BIT -> BIT) RES RES -> RES)
;; Consumes two registers and some binary bit operation 'op',
;; and returns the register obtained by applying op on the
;; i'th bit of both registers for all i.
(define (reg-arith-op op reg1 reg2)
(: bit-arith-op : Bit-List Bit-List -> Bit-List)
;; Consumes two bit-lists and uses the binary bit operation 'op'.
;; It returns the bit-list obtained by applying op on the
;; i'th bit of both registers for all i.
(define (bit-arith-op bl1 bl2)
  ;;We've decided to find out who is op once, not in each iteration of the reccursion.
  ( : bit-arith-helper : Bit-List Bit-List Bit-List -> Bit-List)
  (define (bit-arith-helper l1 l2 lresult)
    (if (null? l1) lresult
                   (bit-arith-helper (rest l1) (rest l2) (append lresult (list (op (first l1) (first l2))) ))))
  (bit-arith-helper bl1 bl2 null))
;At first we wanted to check if op is and or or, and to call bit-arith-or-helper and bit-arith-and-helper, but we decided to ignore that and took the original path.
  
(RegV (bit-arith-op (RegV->bit-list reg1) (RegV->bit-list reg2))))


(: majority? : Bit-List -> Boolean)
;; Consumes a list of bits and checks whether the
;; number of 1's are at least as the number of 0's.
;; The logic is simple- upon recieveing 1 add 1, upon recieveing 0 decrease 1, check if the last result positive or negative.
(define(majority? bl)
  ( : majority?-helper : Bit-List Number -> Boolean)
  (define (majority?-helper lst c)
    (cond
	[(and (null? lst) (or (> c 0) (= c 0))) true]
	[(null? lst) false]
	[(= (first lst) 1) (majority?-helper (rest lst) (+ c 1))]
	[else (majority?-helper (rest lst) (- c 1))]))
  (majority?-helper bl 0))

(: geq-bitlists? : Bit-List Bit-List -> Boolean)
;; Consumes two bit-lists and compares them. It returns true if the
;; first bit-list is larger or equal to the second.
(define (geq-bitlists? bl1 bl2)
   (cond
	[(null? bl1) true] ;;Both lists equal until the last bit. True.
	[(and (= (first bl1) 1) (= (first bl2) 0)) true] ;;bl1[i]>bl2[i]. True
	[(and (= (first bl1) 0) (= (first bl2) 1)) false] ;;bl1[i]<bl2[i]. False
	[else (geq-bitlists? (rest bl1) (rest bl2))])) ;;bl1[i]==bl2[i]. Reccursion.

(: shift-left : Bit-List -> Bit-List)
;; Shifts left a list of bits (once)
(define(shift-left bl)
  (append (rest bl) (list (first bl)))) ;;put the first bit as last.
(: RegV->bit-list : RES -> Bit-List)
;; extract a bit-list from RES type
  (define (RegV->bit-list res)
  (cases res
      [(RegV a) a]
      [(boo a) (error 'RegV->bit-list "bad syntax in ~s" res)]))
( : boo->Boolean : RES -> Boolean)
(define (boo->Boolean value)
  (cases value
    [(RegV a) (error 'boo->Boolean "This is a bit-list, not boolean! in ~s" value)]
    [(boo a) (if (eq? a #t) #t #f)]))
  
(: eval : RegE -> RES)
;; evaluates RegE expressions by reducing them to bit-lists
;; It took two tries to remmember to insert RegV->bit-list everywhere.
(define (eval expr)
  (cases expr
    [(Reg a) (RegV a)] 
    [(And a b) (reg-arith-op bit-and (eval a) (eval b))]     
    [(Or a b)  (reg-arith-op bit-or  (eval a) (eval b))]
    [(Shl a) (RegV (shift-left (RegV->bit-list (eval a))))] 
    [(With name named-expr body) (eval (subst body name (Reg (RegV->bit-list (eval named-expr)))))] 
    [(Bool b) (boo b)] 
    [(Geq a b) (boo (geq-bitlists? (RegV->bit-list (eval a)) (RegV->bit-list (eval b))))] 
    [(Maj a) (boo (majority? (RegV->bit-list (eval a))))]
    [(Id sym) (error 'eval "free identifier: ~s" sym)]
    [(If cond trueValue falseValue) (if (boo->Boolean (eval cond)) (eval trueValue) (eval falseValue))]))


#|   eval({with {x E1} E2}) = eval(E2[eval(E1)/x]) |#
;;;;;;;;;;;;;;;;;Q5;;;;;;;;;
;it took 3 minutes to realize that you required this cases in run as well.
(: run : String -> Bit-List)
(define (run str)
  (cases (eval (parse str))
    [(RegV a) a]
    [(boo a) (error 'run "the expression is boolean, not bit-list in ~s" (eval (parse str)))]))
  
;;;Tests!! 
(test (run "{ reg-len = 2 {and {1 0}{0 0}}}") =>'(0 0))
(test (run "{ reg-len = 2 {and {1 0}{1 1}}}") =>'(1 0))
(test (run "{ reg-len = 2 {and {1 1}{0 1}}}") =>'(0 1))
(test (run "{ reg-len = 2 {and {1 1}{1 1}}}") =>'(1 1))
(test (run "{ reg-len = 1 {or {0}{0}}}") =>'(0))
(test (run "{ reg-len = 1 {or {1}{0}}}") =>'(1))
(test (run "{ reg-len = 1 {or {0}{1}}}") =>'(1))
(test (run "{ reg-len = 1 {or {1}{1}}}") =>'(1))
(test (run "{ reg-len = 4 {1 0 0 0}}") => '(1 0 0 0))
(test (run "{ reg-len = 4 {shl {1 0 0 0}}}") => '(0 0 0 1))
(test (run "{ reg-len = 4 {and {shl {1 0 1 0}}{shl {1 0 1 0}}}}") =>'(0 1 0 1))
(test (run "{ reg-len = 4 { or {and {shl {1 0 1 0}} {shl {1 0 0 1}}} {1 0 1 0}}}") =>'(1 0 1 1));(test (run "{ reg-len = 2 { or {and {shl {1 0}} {1 0}} {1 0}}}") => '(1 0));(test (run "{ reg-len = 4 {with {x {1 1 1 1}} {shl y}}}") =error> "free identifier: y")
(test (run "{ reg-len = 2 { with {x { or {and {shl {1 0}} {1 0}} {1 0}}}
         {shl x}}}") => '(0 1)) (test (run "{ reg-len = 4  {or {1 1 1 1} {0 1 1}}}") =error> "wrong number of bits in (0 1 1)")
(test (run "{ reg-len = 0 {}}") =error> "Register length must be at least 1")
(test (geq-bitlists? '(1 0 1) '(1 1 1)) => #f)
(test (geq-bitlists? '(1 1 1) '(1 1 1)) => #t)
(test (geq-bitlists? '(1 0 1) '(0 1 1)) => #t)
(test (run "{ reg-len = 3 {if {geq? {1 0 1} {1 1 1}} {0 0 1} {1 1 0}}}") => '(1 1 0))
(test (run "{ reg-len = 4 {if {maj? {0 0 1 1}} {shl {1 0 1 1}} {1 1 0 1}}}") => '(0 1 1 1))
(test (run "{ reg-len = 4 {if {maj? {0 0 0 1}} {shl {1 0 1 1}} {1 1 0 1}}}") => '(1 1 0 1))
(test (run "{ reg-len = 4 {if false {shl {1 0 1 1}} {1 1 0 1}}}") => '(1 1 0 1))
(test (run "{ reg-len = 4 {if true {shl {1 0 1 1}} {1 1 0 1}}}") => '(0 1 1 1))
(test (run "{reg-len = 1 {maj? {1}}}") =error> "run: the expression is boolean, not bit-list in (boo #t)")
(test (run "{reg-len = 1 {x}}") =error> "parse-sexpr: bad syntax in (x)")
(test (eval (Id 'y)) =error> "eval: free identifier: y")
(test (run "{reg-len = 1 {with { a {0}}}}") =error> "parse-sexpr-RegL: bad 'with syntax in (with (a (0)))")
(test (boo->Boolean (RegV '(1 0))) =error> "boo->Boolean: This is a bit-list, not boolean! in (RegV (1 0))")
(test (RegV->bit-list (boo #t)) =error> "RegV->bit-list: bad syntax in (boo #t)")

;Writing a tests for subst was very hard threw run function. After discussing with Leora Schmerler about it we decided to test subst alone.

(test (subst (Bool #t) 'x (Bool #f)) => (Bool #t))
(test (subst (If (Bool #f) (Reg '(0 1)) (Reg '(0 0))) 'x (Reg '(1 1))) => (If (Bool #f) (Reg '(0 1)) (Reg '(0 0))))
(test (subst (And (Reg '(0 0)) (Reg '(0 1))) 'x (Reg '(0 0))) => (And (Reg '(0 0)) (Reg '(0 1))))
(test (subst (Or  (Reg '(0 0)) (Reg '(0 1))) 'x (Reg '(0 0))) => (Or  (Reg '(0 0)) (Reg '(0 1))))
(test (subst (Geq (Reg '(1 0)) (Reg '(0 1))) 'x (Reg '(1 1))) => (Geq (Reg '(1 0)) (Reg '(0 1))))
(test (subst (Maj (Reg '(1))) 'x (Reg '(0))) => (Maj (Reg '(1))))
(test (subst (Id 'x) 'y (Reg '(0 1))) => (Id 'x)) 
(test (subst (With 'x (Reg '(0 0)) (Reg '(1 1))) 'y (Reg '(1 0))) => (With 'x (Reg '(0 0)) (Reg '(1 1))))
(test (subst (With 'y (Reg '(0 0)) (Id 'y)) 'y (Reg '(1 0))) => (With 'y (Reg '(0 0)) (Id 'y)))
