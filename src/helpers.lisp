;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;
;;;;; NAME: Jake Marsh
;;;;;
;;;;; CLASS: COS 470
;;;;; ASSIGNMENT: Resolution Theorem Prover
;;;;; DUE: 4/24/14
;;;;;
;;;;; This program accepts a set of axioms and a theorem as 
;;;;; inputs, and attempts to prove a given theorem using a 
;;;;; resolution theorem prover.
;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; //==========================================================================

;;; Function: and?
;;;
;;;   Returns t or nil, depending on whether or not provided axiom is an AND.
;;;
;;; Arglist: axiom
;;; Returns: t or nil.
;;; Side-effects:
;;; Author: Jake Marsh 4-23-14
(defun and? (axiom)
  (eq (car axiom) 'AND))

;;; Function: or?
;;;
;;;   Returns t or nil, depending on whether or not provided axiom is an OR.
;;;
;;; Arglist: axiom
;;; Returns: t or nil.
;;; Side-effects:
;;; Author: Jake Marsh 4-23-14
(defun or? (axiom)
  (eq (car axiom) 'OR))

;;; Function: not?
;;;
;;;   Returns t or nil, depending on whether or not provided axiom is a NOT.
;;;
;;; Arglist: axiom
;;; Returns: t or nil.
;;; Side-effects:
;;; Author: Jake Marsh 4-23-14
(defun not? (axiom)
  (eq (car axiom) 'NOT))

;;; Function: implication?
;;;
;;;   Returns t or nil, depending on whether or not provided axiom is an IMPLICATION.
;;;
;;; Arglist: axiom
;;; Returns: t or nil.
;;; Side-effects:
;;; Author: Jake Marsh 4-23-14
(defun implication? (axiom)
  (eq (car axiom) 'IMPLIES))

;;; Function: is-operator?
;;;
;;;   Returns t or nil, depending on whether or not provided element is an operator.
;;;
;;; Arglist: element
;;; Returns: t or nil.
;;; Side-effects:
;;; Author: Jake Marsh 4-23-14
(defun is-operator? (element)
  (or (eq element 'not) (eq element 'and) (eq element 'or) (eq element 'implies)))

;;; //==========================================================================

;;; Function: negate
;;;
;;;   Returns the negated form of the specified axiom.
;;;
;;; Arglist: axiom
;;; Returns: a list of the form (NOT <axiom>)
;;; Side-effects:
;;; Author: Jake Marsh 4-23-14
(defun negate (axiom)
  (let ((return-list axiom))
	  (cond
        ;; if it is just a single symbol and not a list, return (NOT <symbol>)
        ((not (listp return-list))
          (list 'not return-list))
     
        ((not? return-list)
          ;; remove NOT
          (setf return-list (remove 'not return-list :count 1))
          ;; if list now only has one item, remove extra parentheses
          (if (= (length return-list) 1)
              (setf return-list (nth 0 return-list))
            ;; else, negate or un-negate remaining items
            (progn
	          (setf (nth 0 return-list) (negate (nth 0 return-list)))
	          (if (nth 1 return-list)
	            (setf (nth 1 return-list) (negate (nth 1 return-list))))))
          return-list)
     
	    ((and? return-list)
          ;; change to an OR
          (setf (nth 0 return-list) 'or)
          ;; negate or un-negate following items
          (setf (nth 1 return-list) (negate (nth 1 return-list)))
          (setf (nth 2 return-list) (negate (nth 2 return-list)))
          return-list)
     
	    ((or? return-list)
	      ;; change to an AND
          (setf (nth 0 return-list) 'and)
          ;; negate or un-negate following items
          (setf (nth 1 return-list) (negate (nth 1 return-list)))
          (setf (nth 2 return-list) (negate (nth 2 return-list)))
          return-list)
     
	    ((implication? return-list)
          ;; change to an AND
          (setf (nth 0 return-list) 'and)
          ;; negate or un-negate second item
          (setf (nth 2 return-list) (negate (nth 2 return-list)))
	      return-list)
     
	    (t (list 'not return-list)))))

;;; Function: is-negation?
;;;
;;;   Returns t or nil, depending on whether or not axiom-one is a negation of axiom-two.
;;;
;;; Arglist: axiom-one, axiom-two
;;; Returns: t or nil.
;;; Side-effects:
;;; Author: Jake Marsh 4-23-14
(defun is-negation? (axiom-one axiom-two)
  ;; only process if the two axioms are the same length (minus the 'not') and that axiom-one begins with NOT
  (if (or (not (= (- (length axiom-one) 1) (length (list axiom-two)))) (not (equal 'not (nth 0 axiom-one))))
      (return-from is-negation? nil)
   
    ;; if first test is passed, verify that the rest of the two axioms are the same
    (loop for x from 0 to (- (length (list axiom-two)) 1)
      do (if (not (equal (nth (+ x 1) axiom-one) (nth x (list axiom-two))))
        (return-from is-negation? nil))))
  t)

;;; //==========================================================================

;;; Function: flatten
;;;
;;;   Recursively flattens a list of lists and returns the result.
;;;
;;; Arglist: aList
;;; Returns: the flattened list.
;;; Side-effects:
;;; Author: Jake Marsh 4-29-14
(defun flatten (aList)
  (cond 
    ; return nil if list is null
    ((null aList) 
      nil)
    ; return list if it is indivisible
    (( atom aList) 
      (list aList ))
    ; otherwise loop through and recursively 'flatten' each item in the list
    (t 
      (loop for item in aList appending (flatten item)))))

;;; Function: get-terms
;;;
;;;   Calls 'flatten' on the provided axiom and recursively collects all the 
;;;   terms that appear within the flattened axiom along with the corresponding axiom.
;;;
;;; Arglist: axiom, terms, return-list
;;; Returns: a list of unique terms in tha axiom, paired with the axiom in which they appear
;;; Side-effects:
;;; Author: Jake Marsh 4-29-14
(defun get-terms (axiom terms return-list)
  (let ((flat-list (flatten axiom)))
    ;; get each individual symbol
    (loop for term in flat-list
      do (if (and (not (is-operator? term)) (not (member term terms)))
           (setf terms (append terms (list term)))))
    ;; loop through the found terms
    (loop for term in terms do
      ;; loop through each item in the original axiom, pairing (t ?a) statements with t, ?a
      (loop named inner-loop for element in axiom do
        (cond
          ;; if its a list but contains the element, push the whole list
          ((and (listp element) (member term element))
            (push (list term element) return-list))
          ;; if the entire axiom only has a length of 2 and contains the element, push the whole axiom
          ((and (= (length axiom) 2) (member term axiom))
            (push (list term axiom) return-list))
          ;; else, if it's a list not satisfying above conditions, recurse over it
          ((listp element)
            (setf return-list (get-terms element terms return-list))))))
    ;; return a list of items of the format (<term>, <statement>), with duplicates removed
    (remove-duplicates return-list :test #'equal)))