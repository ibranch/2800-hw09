; **************** BEGIN INITIALIZATION FOR ACL2s B MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#|
Pete Manolios
Fri Jan 27 09:39:00 EST 2012
----------------------------

Made changes for spring 2012.


Pete Manolios
Thu Jan 27 18:53:33 EST 2011
----------------------------

The Beginner level is the next level after Bare Bones level.

|#

; Put CCG book first in order, since it seems this results in faster loading of this mode.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg/ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "base-theory" :dir :acl2s-modes)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :ttags :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading trace-star and evalable-ld-printing books.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil)
(include-book "hacking/evalable-ld-printing" :uncertified-okp nil :dir :system :ttags ((:evalable-ld-printing)) :load-compiled-file nil)

;theory for beginner mode
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s beginner theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "beginner-theory" :dir :acl2s-modes :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s Beginner mode.") (value :invisible))
;Settings specific to ACL2s Beginner mode.
(acl2s-beginner-settings)

; why why why why 
(acl2::xdoc acl2s::defunc) ; almost 3 seconds

(cw "~@0Beginner mode loaded.~%~@1"
    #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup ""
    #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")


(acl2::in-package "ACL2S B")

; ***************** END INITIALIZATION FOR ACL2s B MODE ******************* ;
;$ACL2s-SMode$;Beginner
#|
CS 2800 Homework 9 - Spring 2017


This homework is to be done in a group of 2-3 students. 

If your group does not already exist:

 * One group member will create a group in BlackBoard
 
 * Other group members then join the group
 
 Submitting:
 
 * Homework is submitted by one group member. Therefore make sure the person
   submitting actually does so. In previous terms when everyone needed
   to submit we regularly had one person forget but the other submissions
   meant the team did not get a zero. Now if you forget, your team gets 0.
   - It wouldn't be a bad idea for group members to send confirmation 
     emails to each other to reduce anxiety.

 * Submit the homework file (this file) on Blackboard.  Do not rename 
   this file.  There will be a 10 point penalty for this.

 * You must list the names of ALL group members below, using the given
   format. This way we can confirm group membership with the BB groups.
   If you fail to follow these instructions, it costs us time and
   it will cost you points, so please read carefully.

;;;;<Init::Tags>;;;;
Please ignore (and don't change) tags like the one on the line above. We are again 
looking into how we can improve homework grading. These tags are to mark where 
questions are in the file
   
;;;;<Init::Names>;;;;
Names of ALL group members: Izaak Branch, Chris Kenyon

Note: There will be a 10 pt penalty if your names do not follow 
this format.

|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
For this homework you may want to use ACL2s to help you.

Technical instructions:

- open this file in ACL2s as hw09.lisp

- make sure you are in BEGINNER mode. This is essential! Note that you can
  only change the mode when the session is not running, so set the correct
  mode before starting the session.

- insert your solutions into this file where indicated (usually as "...")

- only add to the file. Do not remove or comment out anything pre-existing
  unless asked to.

- make sure the entire file is accepted by ACL2s. In particular, there must
  be no "..." left in the code. If you don't finish all problems, comment
  the unfinished ones out. Comments should also be used for any English
  text that you may add. This file already contains many comments, so you
  can see what the syntax is.

- when done, save your file and submit it as hw09.lisp

- avoid submitting the session file (which shows your interaction with the
  theorem prover). This is not part of your solution. Only submit the lisp
  file!

|#
#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Measure Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
A measure function m for function f satisfies the 
following conditions (as discussed in class and in lectures):
1. m has the same arguments and the same input contract as f.
2. m's output contract is (natp (m ...))
3. m is admissible.
4. On every recursive call of f, given the input contract and 
   the conditions that lead to that call, m applied to the arguments in
   the call is less than m applied to the original inputs.
   
Thus when you are asked to prove termination using a measure function, you
need to
a) write the function (if not provided) which satisfies points 1-3
b) Write proof obligations corresponding to recursive calls in f
c) Prove the proof obligations using equational reasoning or using an approach
   we specify
|#



;;;;<Init::Functions>;;;;
;; Here are some potentially useful (and admissible) functions.
;; Typical tests and headers are minimal since these aren't for coding. They
;; MAY be useful for measure functions.
;;
;; Throughout the assignment you can also assume abs (below) is defined and 
;; returns the absolute value of a rational number.  If the input is an integer, 
;; the result is a natural number.
;;
;; Finally lists of natural numbers (lon) and non-negative rationals 
;; are defined below for reference


(defdata nnr (range rational (0 <= _)))
(defdata lon (listof nat))
(defdata lonnr (listof nnr))

(defunc nat/ (x y)
  :input-contract (and (natp x)(posp y))
  :output-contract (natp (nat/ x y))
  (if (< x y)
    0
    (+ 1 (nat/ (- x y) y))))

(defunc int/ (x y)
  :input-contract (and (integerp x)(posp y))
  :output-contract (integerp (int/ x y))
  (cond ((integerp (/ x y))   (/ x y))
        ((< x 0)    (- (unary-- (nat/ (unary-- x) y)) 1))
        (t          (nat/ x y))))

(check= (int/ 4 5) 0)
(check= (int/ 6 5) 1)
(check= (int/ -6 5) -2)
(check= (int/ -4 5) -1)
(check= (int/ -5 5) -1)
(check= (int/ 5 5) 1)

;; Theorems to help ACL2s prove phi_int_floor
(defthm nat/-lte (implies (and (natp x)(posp y))
                          (<= (nat/ x y) (/ x y))))

(defthm nat/-gt (implies (and (natp x)(posp y)
                              (not (integerp (/ x y))))
                         (< (- (/ x y) 1) (nat/ x y))))

(defthm phi_int_floor (implies (and (integerp x)(posp y))
                               (<= (int/ x y) (/ x y)))
  :hints (("Goal" :use (:instance nat/-gt (x (- x))))))
;; Feel free to use phi_int_floor as a theorem 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; max-l: lon -> nat
;; (max-l l) takes a non-empty list of natural numbers l
;; and returns the largest element in the list.
(defunc max-l (l)
  :input-contract (and (lonp l)(consp l))
  :output-contract (natp (max-l l))
  (cond ((endp (rest l))                 (first l))
        ((< (first l) (max-l (rest l)))  (max-l (rest l)))
        (t                               (first l))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abs: rational -> nnr
;; (abs r) takes a rational r and returns the magnitude
;; of r (or how far r is from 0)
(defunc abs (r)
  :input-contract (rationalp r)
  :output-contract (nnrp (abs r))
  (if (< r 0)
    (unary-- r)
    r))#|ACL2s-ToDo-Line|#

#|<Init::Fin>

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
|##|  FUNCTION WITH THE GIVEN MEASURE  |
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

For each one of questions i=1,2,3,4 you are given ACL2s expressions
involving a function mi (m1, m2, m3, m4).  Each expression 
represents a proof obligation necessary for proving mi is a measure
function for a function fi (see point 4 above regarding proving
termination using a measure function)

Your tasks are:

 
1) Define a function fi (f1, f2, f3, f4) that 
a) is admissible
b) the expressions match the requirements on a measure function mi
for fi that mi decreases with each recursive call

2) Define an admissible measure function mi for fi.

3) Write down the given ACL2s expressions again, BUT this time plug
in the definition of mi into the expressions. Follow the format shown
in the example below.  Convince yourself that they evaluate to T 
(no formal proof is required).

Example (i=0)
(implies (and (posp p)(> p 1))
         (< (m0 (- p 1)) (m0 p))
         
1. We define the following ACL2s function:
(defunc f0 (p)
 :input-contract (posp p)
 :output-contract (posp (f0 p))
 (if (< 1 p)
     (f0 (- p 1))
     p))
Convince yourselves that f0 is admissible (no proof necessary).
In particular, it is terminating.
     
2. A measure function for f0 is:
(defunc m0 (p)
 :input-contract (posp p)
 :output-contract (natp (m0 p))
 p)
 
3) The above expression with the body of m0 plugged in 
becomes (using in-fix notation):
 (posp p) /\ (p > 1) => ((m0 (p - 1)) = (p - 1) < p = (m0 p))
 
 which is valid
 
;;<FGM::a>;; 
1. 
(implies (and (listp x) (natp n) (not (endp x)))
         (< (m1 (rest x) n) (m1 x n)))

(defunc f1 (x n)
 :input-contract (and (listp x) (natp n))
 :output-contract (listp (f1 x n))
 (if (endp x)
     x
     (rest x)))
     
(defunc m1 (x n)
 :input-contract (and (listp x) (natp n))
 :output-contract (natp (m1 x n))
 (len x))
 
(listp x) /\ (natp n) /\ (not (endp x)) => (m1 (rest x) n) = (len (rest x)) < (len x) = (m1 x n)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;<FGM::b>;;
2.
For first recursive call:
(implies (and (natp n) (integerp i) (not (equal i 0)) (< i 0))
         (< (m2 n (+ i 1)) (m2 n i)))
For second recursive call:
(implies (and (natp n) (integerp i) (not (equal i 0)) (not (< i 0)))
         (< (m2 (+ n 1) (- i 1)) (m2 n i)))

(defunc f2 (n i)
 :input-contract (and (natp n) (integerp i) (not (equal i 0)))
 :output-contract (natp (f2 n i))
 (cond ((equal i 0) n) 
       ((< i 0)     (f2 n (+ 1 i)))
       (t           (f2 (+ n 1) (- i 1)))))
     
(defunc m2 (n i)
 :ic (and (natp n) (integerp i) (not (equal i 0)))
 :oc (natp (m2 n i))
 (abs i))
 
For the first:
(natp n) /\ (integerp i) /\ (not (equal i 0)) /\ (< i 0) => (m2 n (+ i 1)) = (abs (+ 1 i)) < (abs i) = (m2 n i)

For the second:
(natp n) /\ (integerp i) /\ (not (equal i 0)) /\ (not (< i 0)) => (m2 (+ n 1) (- i 1)) = (abs (- i 1)) < (abs i) = (m2 n i)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;<FGM::c>;;
3. Assuming lon (list of naturals) is defined
For the first recursive call:
(implies (and (lonp l)(natp n)(not (and (equal n 0)(endp l)))(> n 0))
         (< (m3 l (- n 1)) (m3 l n)))
For the second recursive call:
(implies (and (lonp l)(natp n)(not (and (equal n 0)(endp l)))(not (> n 0)))
         (< (m3 (rest l) n) (m3 l n)))

.......................

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;<FGM::d>;;
4.  EXTRA PRACTICE (no points for question 4)

ACL2s will have problems proving the function f4 associated with
the following expression will terminate (so don't try to admit it) 
but can you prove it using some functions above?

(implies (and (rationalp r)(not (integerp r)))
         (< (m4 (/ (- (numerator r) 1) (denominator r))) (m4 r)))

.........................


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
|##|  5. Fixing a non-terminating function  |
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(a) Melanie is considering the following function:

    (defunc great (a b c)
      :input-contract (and (posp a) (lonp b) (posp c))
      :output-contract (natp (great a b c))
      (cond ((endp b)        (+ 1 (great a (cons c b) c)))
            ((< (first b) a) (+ 1 (great a (cons (+ c (first b))
                                                    (rest b)) c)))
            ((equal (first b) a) 0)
            (t               (+ 1 (great a (cons 0 b) c)))))
            
She claims that this function will be admitted by ACL2s since its body is a
legal expression satisfying all body contracts, and the output contract is
trivially satisfied as well. But she forgot something! Show that the
function does not (always) terminate by giving an input in the form of
concrete values a,b,c that satisfies the input contract but causes an
infinite execution.
;;<FNT::a>;;

a = 1
b = '(0)
c = 2

(b) Melanie admits there were problems in her definition. Her new
function (OMG = OK Melanie's Great) is:

(defunc omg (a b c)
  :input-contract (and (posp a) (lonp b) (posp c))
  :output-contract (natp (omg a b c))
  (cond ((endp b)        (+ 1 (omg a (cons c b) c)))
        ((< (first b) a) (+ 1 (omg a (cons (+ 1 (first b))
                                                (rest b)) c)))
        ((equal (first b) a) 0)
        (t               (+ 1 (omg a (cons a (rest b)) c)))))

Write a measure function (m-omg) that can be used to prove that omg terminates.
Try to make this measure function as simple as possible, otherwise
part c will be more difficult. You shouldn't need more than one if statement + math

Hint: First run function omg on a few well-chosen test cases (exercising
all clauses of the cond) and see what happens. What changes? How long can chains of
recursive calls to this function actually be? If b is not empty, will it ever
be empty some time later? For empty lists can I return a number that is guaranteed 
to be larger than subsequent calls to m-omg?
;;<FNT::b>;;
.................


c) Now prove the function terminates using your measure function.  

Write each conjecture
;;<FNT::c>;;

.........................
                       
Now discharge these proof obligations using equational reasoning. For the sake of time, 
prove 2 of the 3 conjectures (your choice):
.........................


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
|##| 6. Humans are Smarter than Computers  |
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
From HW08, function f20 was not admissible into ACL2s, however, you hopefully found
a measure function that could prove termination. Show that you are smarter than
ACL2s. PROVE the measure function m20 decreases with each recursive call to f20.

(defunc  f20 (n m)
  :input-contract (and (integerp n)(integerp m))
  :output-contract (integerp (f20 n m))
  (cond ((equal n m)                 1)
        ((< n m)  (f20 (+ n 1)(- m 1)))
        (t             (f20 (- n 1) m))))
        
(defunc m20 (n m)
  :input-contract (and (integerp n)(integerp m))
  :output-contract (natp (m20 n m))
  (if (>= n m) (- n m) (+ (- m n) 1)))

;;<HSC::a>;;
a)
Write the conjectures needed to prove m20 is a measure function
1. (integerp n) /\ (integerp m) /\ (>= n m) => (m20 (- n 1) m) < (m20 n m)
2. (integerp n) /\ (integerp m) /\ (< n m) => (m20 (+ n 1) (- m 1)) < (m20 n m)


;;<HSC::b>;;
b) Now prove each conjecture. Notice, you may have to do a proof by cases
if you don't know if n < m in the recursive call:

1. (integerp n) /\ (integerp m) /\ (>= n m) => (m20 (- n 1) m) < (m20 n m)

C1. (integerp n)
C2. (integerp m)
C3. (>= n m)
-------------
(m20 (- n 1) m) < (m20 n m)
= {def m20|((n (- n 1)) on LHS, c3, if-axiom; def m20 on RHS, c3, if-axiom}
(- (- n 1) m) < (- n m)
= {arithmetic}
n - m - 1 < n - m
which is true, so QED


2. (integerp n) /\ (integerp m) /\ (< n m) => (m20 (+ n 1) (- m 1)) < (m20 n m)

C1. (integerp n)
C2. (integerp m)
C3. (< n m)
----------
C4. (not (>= n m)) {C3, PL}

(m20 (+ n 1) (- m 1)) < (m20 n m)
= {def m20|((n (+ n 1)) (m (- m 1))) on LHS, C4, if-axiom; def m20 on RHS, c4, if-axiom}
(+ (- (- m 1) (+ n 1)) 1) < (+ (- m n) 1)
= {arithmetic, put in infix for reading purposes}
((m - 1) - (n + 1)) + 1 < (m - n) + 1
which is true (a smaller number minus a bigger number is less than a bigger number minus a smaller number), so QED


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
|##|  MORE MEASURE FUNCTIONS  |
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
For each of the following terminating functions, write a measure function. You 
DO NOT need to prove that the function is a measure, just write the measure 
function in ACL2s syntax. These exercises are intended you to give additional 
practice coming up with measure functions. You are encouraged to do the proofs 
for additional practice, but you are NOT required to submit the proofs.

;;<MM::a>;;
7.
(defunc do-nothing (x y z)
 :input-contract (and (listp x)(listp y)(integerp z))
 :output-contract (listp (do-nothing x y z))
 (cond ((and (endp x)(> z 0))  y)
       ((and (endp y)(< z 0))  x)
       ((equal z 0)           (app x y)) 
       ((> z 0)               (do-nothing (rest x) (cons (first x) y) (- z 1)))
       (t                     (do-nothing (cons (first y) x) (rest y) (+ z 1)))))

.................


;;<MM::b>;;
8.
(defunc do-something (x y)
  :input-contract (and (natp x) (lonp y))
  :output-contract (booleanp (do-something x y))
  (cond ((equal x (len y))   t)
        ((> x (len y))      (do-something (- x 1) y))
        (t                  (do-something (len y) (list x x x)))))

..............

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;<MM::c>;;
9. EXTRA PRACTICE (No marks): Jaideep's Tear Inducer. 
This is just a challenge question that I love. Jaideep accidentally 
created it last Summer and if you can solve it, you probably
understand measure functions well. It's actually shocking how 
complicated the measure function is despite how simple the function 
looks.  If you come up with a solution which requires less than 5 
conditions (and you prove it works), please let us know.

(defunc jti (x y)
  :input-contract (and (natp x) (natp y))
  :output-contract (booleanp (jti x y))
  (cond ((equal x y) t)
        ((> x y)(jti (- x 1) (+ y 1)))
        (t (jti (+ y 1) x))))
...........


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;<MM::d>;;
10.
(defunc do-anything(x y)
  :input-contract (and (natp x) (lonp y))
  :output-contract (listp (do-anything x y))
  (cond ((equal x (len y))    y)
        ((> x (len y))       (do-anything x (cons x y)))
        (t                   (do-anything (+ x 1) y))))

..............



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
|##|  Introduction to Induction  |
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

We will be looking at inductive proofs (in various forms) for the remainder of term.
Prove the conjectures in questions 11-13 using induction.

If you want an example of an inductive proof, look at our proof for Gauss' Trick
phi_sumn: (implies (natp n) (equal (sumn n)(fsumn n)) where sumn is the slow
way to sum numbers from 0 to n while fsumn is n * (n+1) / 2.

We broke that proof into 3 parts

phi_sumn1: ~(natp n) => phi_sumn
phi_sumn2: (natp n) /\ (equal n 0) => phi_sumn
phi_sumn3: (natp n) /\ (not (equal n 0)) /\ phi_sumn|((n (- n 1))) => phi_sumn

Notice that phi_sumn1 is the "bad data" or ~IC case which we ignored when doing
equational reasoning.
            
You'll also notice that since the conjectures imply phi_sumn
you should swap in the ENTIRE phi_sumn conjecture and use
exportation to get your context. Exportation means we just get 
a sequence of ands which imply (sumn n) = (fsumn n) for each of the 
conjectures.

I will use the term proof obligations to refer to conjectures used to prove a
particular theorem (eg "=> phi_sumn") while the induction scheme can be applied
to any inductive proof (eg "=> phi" where phi is not specified).

For each induction scheme conjecture we add the conditions that 
lead to a particular branch.  We also assume that the 
conjecture holds for the next recursive call.  Thus we substitute 
variables in the conjecture to what they will be at the next recursive call
(similar to what we did for measure functions)

|#

#|
;;<II::a>;;
11) EXTRA PRACTICE (no points for question 11)
Prove that app is associative using induction (this will similar to what we did in
lecture when discussing equational reasoning).
(phi_assoc_app: (implies (and (listp x)(listp y)(listp z))
                         (equal (app (app x y) z) (app x (app y z))))

Write your proof obligations associated with using the induction scheme that 
listp gives rise to.
;;<II::a.listp>;;
.................


Write the proof obligations if you want to prove phi_assoc_app using the induction
scheme for app.
;;<II::a.app>;;
.................


Now do the proof using the induction scheme for app (we did a very similar proof
in class using the I.S. for listp)
;;<II::a.proof>;;
................
|#

#|
12) Prove the following conjecture using the induction scheme that arises from 
the function in:
phi-in-max: (implies (and (lonp l)(consp l)) (in (max-l l) l))

For the proof, the definition of in is:
(defunc in (e l)
  :input-contract (listp l)
  :output-contract (booleanp (in e l))
  (if (endp l)
    nil
    (or (equal e (first l)) (in e (rest l)))))

Also see the definition of max-l above.

;;<II::b.init>;;
Write the induction scheme for in or provide the proof obligations using
the induction scheme for in:
.......................


;;<II::b>;;
Prove the conjectures so you can conclude (by induction) phi-in-max is a theorem
Next assignment, we will say obligation 1 (not the input contract) is "Trivial" 
and not even do the proof but for now prove all conjectures.
Can you see why we typically say trivial for the ~IC case if you 
choose the right induction scheme?
..................


13) Prove the following conjecture
phi_poweven: (implies (and (rationalp x)(natp p))
                      (>= (pow x (* p 2)) 0))
Where
(defunc pow (x p)
  :input-contract (and (rationalp x) (natp p))
  :output-contract (rationalp (pow x p))
  (if (equal p 0)
    1
    (* x (pow x (- p 1)))))

Use the induction scheme for nind.  What are the proof obligations?
;;<II::c.nind>;;
........................


;;<II::c.proof>;;
Prove the three conjectures to prove that phi-poweven is a theorem.
You can use the following theorem without proving it:
T_esquare: (implies (rationalp r)(>= (* r r) 0))
...............


|#