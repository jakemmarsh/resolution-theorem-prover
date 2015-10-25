;;; -*- Mode: Lisp; Package: USER -*-

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;
;;;;; COS 470: UNIFY.LISP
;;;;;  
;;;;; This file contains functions to perform unification on predicate
;;;;; calculus expressions.   They are modifications of the unify functions
;;;;; in Winston and Horn.
;;;;;
;;;;; Unify has two required arguments--expressions--and one optional 
;;;;;   argument--a unifier (or binding list).  It returns two values
;;;;;   (using "values").  The first is either T or nil, depending on 
;;;;;   whether or not the unification was successful.  The second is 
;;;;;   a unifier (or updated unifier, if the optional argument was given)
;;;;;   resulting from the unification (if the unification was successful;
;;;;;   else the value of the optional argument is returned).
;;;;;
;;;;; A unifier (binding list) has the following form:
;;;;;    ((var1 val1) (var2 val2) ... (var_n val_n))
;;;;;
;;;;; The functions in this file work in a version of Common Lisp that 
;;;;;   is on my computer; however, they haven't been tested on Kepler.
;;;;;   Consequently, you may have to modify them for your purposes.
;;;;;
;;;;; Below are some suggestions on how to represent predicate calculus
;;;;; expressions in Lisp.
;;;;;
;;;;; Predicate syntax:
;;;;;    Human(Socrates) becomes (human socrates)
;;;;;    Human(x) becomes (human ?x)  -- i.e., ?x means "x" is a variable
;;;;;    Human(x) and Roman(x) becomes (and (human ?x) (roman ?x))
;;;;;    Pompeian(x) or Roman(x) becomes (or (pompeian ?x) (roman ?x))
;;;;;    ~Pompeian(x) becomes (not (pompeian ?x))
;;;;;    Bird(x) ==> Flies(x) becomes (implies (bird ?x) (flies ?x))
;;;;;    
;;;;; Quantifier syntax:
;;;;;    existential:  (exists (?x) (on ?x ?y))
;;;;;    universal:    (forall (?x) (implies (man ?x) (mortal ?x)))
;;;;;
;;;;; Variables
;;;;; ---------
;;;;;    Note that there are some functions in this file to help you deal with 
;;;;;    "AI variables", i.e., those whose name is prefaced by "?":
;;;;;       o (variable? <foo>) returns t if <foo> is a variable
;;;;;       o (varname <foo>) returns the name of the variable -- e.g., ?X ->
;;;;;         X
;;;;;       o (make-var <foo>) will create a variable whose name is <foo>, for 
;;;;;         example X -> ?X
;;;;;       o see below for info about newSymbol 
;;;;;       o bound? -- returns non-nil if a variable is bound in a binding
;;;;;       o binding -- returns the binding of a variable in a binding list,
;;;;;         preferring to return non-variable bindings when there are both
;;;;;         variable and non-variable bindings; see description of function
;;;;;         for details
;;;;;       o find-binding, extract-value -- helps you find a variable's
;;;;;         binding in a binding list -- deprecated functions; use binding
;;;;;         instead 
;;;;;       o add-binding -- adds a binding for a variable to a binding list
;;;;;       o instantiate -- instantiates all the variables in an expression
;;;;;         with their bindings from a binding list
;;;;;
;;;;; Author: Roy Turner
;;;;; Date: Created: 1/25/90
;;;;; Modifications:
;;;;;   o 3/14/90: prepared for class
;;;;;   o 13:04 - Thu Nov 5, 1998 -rmt- Modifications added for COS 470, F98:
;;;;;      o newSymbol symbol generator added.  Call is:
;;;;;             (newsymbol <foo>)
;;;;;        where <foo> is a symbol or a string.  A new, unique symbol based
;;;;;        on that is returned.  Any trailing numerals are stripped from the 
;;;;;        symbol, and then a new number is appended to make a unique name.
;;;;;   o 22:41 - Mon Apr 7, 2014 -rmt- 
;;;;;     o Cleaned up some equality operators for efficiency
;;;;;     o Removed an old macro character definition that isn't needed here
;;;;;     o Finally added string-append as a macro, since it doesn't appear in
;;;;;       (e.g.) SBCL
;;;;;     o Added an instantiate function, along with helper functions bound?
;;;;;       and binding
;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A more sanely-named concatenation function for strings:
(defmacro string-append (&rest strings)
  `(concatenate 'string ,@strings))

;;; Unify two expressions; bindings is optional.
(defun unify (p1 p2 &optional bindings)
  (cond
   ((variable? p1)
    (unify-variable p1 p2 bindings))
   ((variable? p2)
    (unify-variable p2 p1 bindings))
   ((and (atom p1) (atom p2)) 
    (unify-atoms p1 p2 bindings))
   ((and (listp p1) (listp p2))
    (unify-elements p1 p2 bindings))
   (t (values nil bindings))))

(defun unify-atoms (p1 p2 bindings)
  (values (eql p1 p2) bindings))

;;; This looks through the elements of two lists, making sure that 
;;; corresponding elements unify and maintaining appropriate bindings.
(defun unify-elements (p1 p2 bindings)
  (let (blist matched?)
    (multiple-value-setq (matched? blist)
      (unify (first p1) (first p2) bindings))
    (cond
     ((null matched?)
      (values nil bindings))
     ((multiple-value-setq (matched? blist)
	(unify (rest p1) (rest p2) blist))
      (values matched? blist))
     (t
      (values nil bindings)))))

;;; This unifies a variable (P1) with an arbitrary expression (P2), updating 
;;; bindings as necessary
(defun unify-variable (p1 p2 bindings)
  (let ((binding (find-binding p1 bindings)))
    (if binding
	(unify (extract-value binding) p2 bindings)
	(if (inside? p1 p2 bindings)
	    (values nil bindings)
	    (values t (add-binding p1 p2 bindings))))))

;;; This looks up a variable's binding in "bindings".
(defun find-binding (var bindings)
  (assoc var bindings))

;;; This returns the value portion of a binding.
(defun extract-value (binding)
  (cadr binding))

;;; This returns T if "var" occurs in expression "expr".
(defun inside? (var expr bindings)
  (if (eql var expr)
      nil
      (inside-or-equal? var expr bindings)))

(defun inside-or-equal? (var expr bindings)
  (cond
   ((eql var expr) t)
   ((and (not (variable? expr)) (atom expr)) nil)
   ((variable? expr)
    (let ((binding (find-binding expr bindings)))
      (when binding
	(inside-or-equal? var (extract-value binding) bindings))))
   (t (or (inside-or-equal? var (first expr) bindings)
	  (inside-or-equal? var (rest expr) bindings)))))

;;; This adds a new binding of the form "(var val)" to "bindings", or creates
;;; a new binding list if "bindings" is nil.
(defun add-binding (var val bindings)
  (if (eq '_ var)
      bindings
      (cons (list var val) bindings)))

;;; Returns t if <thing> is a variable, else returns nil.
(defun variable? (thing)
  (or (and (listp thing)
           (eql (car thing) '*var*))
      (and (symbolp thing)
           (eql (char (symbol-name thing) 0)
                  #\?))))

;;; Returns the name of the variable.
(defun varname (var)
  (cond
    ((and (consp var)
          (consp (cdr var)))
     (cadr var))
    ((eql (char (string var) 0) #\?)
     (intern  (string-left-trim '(#\?) (string var))))))

;;; Function: make-var
;;;
;;;   Create a new variable whose name is "var".  If "var" is 'x1,
;;;   for example, the new one will be ?X1.
;;;
;;; Arglist: var
;;; Returns:
;;; Side-effects:
;;; Author: rmt (Roy Turner) - Thu Nov  5 09:07:37 1998
(defun make-var (var)
  (intern (concatenate 'string "?" 
		       (cond
			((stringp var) var)
			(t (symbol-name var))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;.
;;;;; >> Symbol Generation <<
;;;;;
;;;;;  The following extends Lisp's symbol generation functionality (i.e.,
;;;;;  gensym) to allow creation of arbitrarily-named, unique symbols.  The
;;;;;  entry point is "newSymbol".
;;;;;
;;;;; Copied from CDPS group's Utilities package, rmt (Roy Turner) - Thu Nov 5
;;;;; 09:11:44 1998
;;;;;.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; Class: SymbolGenerator
;;;
;;;  Holds the state of symbol generation.  [Copied from Utilities, where a
;;;  class was needed; if doing this from scratch for this class, I'd have
;;;  used just a hash table.  Won't hurt you to see how a class is defined in
;;;  Lisp!] 
;;; 
;;; Superclasses: 
;;; Instance variables: (counterTable)
;;; Author: rmt (Roy Turner) - Thu Nov  5 09:12:55 1998
;;; Modifications:

(defclass SymbolGenerator ()
  ((counterTable :initform (make-hash-table :test #'equal))))


;;; Function: newSymbol
;;;
;;;   This returns a unique symbol based on "prefix", which can be a string or 
;;;   a symbol.
;;;
;;; Arglist: &optional prefix &key (package) (intern t)
;;; Returns:
;;; Side-effects:
;;; Author: rmt (Roy Turner) - Thu Nov  5 09:14:39 1998
;;; Modifications:  Removes trailing numbers, checks for uniqueness.
(defun newSymbol (&optional prefix &key s (intern t))
  (with-slots (counterTable) *symbolGenerator*
   (let (num sym) 
     (cond
       ((symbolp prefix)
	;; convert to string, call again:
	(newSymbol (symbol-name prefix) :package package :intern intern))
       ((stringp prefix)
	;; get rid of trailing numerals:
	(setq prefix (string-right-trim "0123456789" prefix))
	;; try new symbol names until we find one that is not in use:
	(loop do
	      (cond
	       ((setq num (gethash prefix counterTable))
		;; number exists for this prefix -- new number is just incremented
		;; one: 
		(setq num (1+ num))
		(setf (gethash prefix counterTable) num))
	       (t
		;; no number yet:
		(setf (gethash prefix counterTable) 1)
		(setq num 1)))
	    until (not (find-symbol
			(setq sym (string-append prefix 
						 (princ-to-string num))))))
	;; found one, create the symbol...
	(setq sym (make-symbol sym))
	(when intern			     ;then intern the symbol:
	  (setq sym (if package
		      (intern (format nil "~a~s" prefix num) package)
		      (intern (format nil "~a~s" prefix num)))))
	sym)
       (t
	;; then can't do any better than regular old gensym:
	(gensym))))))

;;; Function: instantiate(thing, bindings)
;;;
;;;   Replace all instances of variables in "thing" with their bindings from
;;;   "bindings".  Note that if there are circularities, e.g., if "bindings"
;;;   is: 
;;;         ((?x ?y) (?y ?z) (?z ?x)) 
;;;   then this function will likely infinitely recur.
;;;
;;; Arglist: thing, bindings
;;; Returns:
;;; Side-effects:
;;; Author: rmt (Roy Turner)
;;; Created: 23:26 - Mon Apr 7, 2014 -rmt- 
(defun instantiate (thing bindings)
  (let (val)
    (cond
     ((null thing) nil)
     ((listp thing)
      (cons (instantiate (car thing) bindings)
	    (instantiate (cdr thing) bindings)))
     ((or (not (variable? thing)) (not (bound? thing bindings)))
      thing)
     ((or (not (variable? (setq val (binding thing bindings))))
	  (eql val thing))		;same variable returne => no binding
      val)
     (t (instantiate val bindings)))))

;;; Function: bound?(thing, bindings)
;;;
;;; Returns non-nil (actually the binding pair) if "thing" is a variable
;;; appearing in "bindings".  Note that a variable may be bound to another,
;;; such as in the binding list ((?x ?y) (?y 3)).  In this case, ?x is bound
;;; to ?y and ?y is bound to both ?x and to 3 -- that is, the order doesn't
;;; matter when a variable is bound to another variable.
;;; 
;;;
;;; Arglist: thing, bindings
;;; Returns:
;;; Side-effects:
;;; Author: rmt (Roy Turner)
;;; Created: 23:26 - Mon Apr 7, 2014 -rmt- 
(defun bound? (thing bindings)
  (car (member thing bindings :test #'(lambda (th b)
					(or (eql th (car b))
					    (eql th (cadr b)))))))

;;; Function: binding(thing, bindings)
;;;
;;; Returns the binding for "thing" from "bindings" if one exists, otherwise
;;; returns "thing" itself.  This will preferentially return non-variable
;;; bindings; for example:
;;;       (binding '?x '((?y ?x) (?x 3)))
;;; will return 3.
;;;
;;; Arglist: thing, bindings
;;; Returns:
;;; Side-effects:
;;; Author: rmt (Roy Turner)
;;; Created: 23:26 - Mon Apr 7, 2014 -rmt- 
(defun binding (thing bindings)
  (loop with val
      with b
      for binding in bindings do
	(when (member thing binding)
	  (setq b (if (eql thing (car binding))
		    (cadr binding)
		    (car binding)))
	  (if (not (variable? b))
	    (return b)
	    (unless val (setq val b))))
	finally (return val)))
       
(defvar  *SymbolGenerator* (make-instance 'SymbolGenerator))