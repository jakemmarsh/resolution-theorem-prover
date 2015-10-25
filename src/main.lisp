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

;;; Function: get-knowledge-base
;;;
;;;   Returns the axioms of the knowledge base for the specified domain.
;;;
;;; Arglist: domain
;;; Returns: Axioms for the specified domain.
;;; Side-effects: Can throw an error if an invalid domain is specified.
;;; Author: Jake Marsh 4-23-14
(defun get-knowledge-base (domain)
	(cond
	  ((= 0 domain)
	    '(
          (or (not (p ?x)) (q ?x))
          (or (not (q ?x)) (t ?x))
          (or (not (r ?x)) (t ?x))
          (p ?a)
        ))
	  ((= 1 domain)
	    '(
          (dog d)
          (owns jack d)
          (or (or (not (dog ?x)) (not (owns ?x ?y))) (animallover ?x))
          (or (not (animallover ?z)) (not (animal ?w)) (not (kills ?z ?w)))
          (or (kills jack tuna) (kills curiosity tuna))
          (cat tuna)
          (or (not (cat ?u)) (animal ?u))
        ))
      (t (error "That is not a valid domain."))))

;;; Function: get-theorem
;;;
;;;   Returns the theorem for the specified domain.
;;;
;;; Arglist: domain
;;; Returns: Theorem for the specified domain.
;;; Side-effects: Can throw an error if an invalid domain is specified.
;;; Author: Jake Marsh 4-23-14
(defun get-theorem (domain)
  (cond
    ((= 0 domain)
      '(or (t ?a) (r ?a)))
    ((= 1 domain)
       '(kills curiousity cat))
    (t (error "That is not a valid domain."))))

;;; //==========================================================================

;;; Function: create-indexes
;;;
;;;   Sets up some indexes that allow the knowledge base to be searched efficiently 
;;;   at run time. For every term, creates a set of pointers to every axiom in 
;;;   which the term appears.
;;;
;;; Arglist: element, index-table, knowledge-base, current-index
;;; Returns: Hash table of terms and corresponding lists of occurrences in knowledge base.
;;; Side-effects:  Modifies the provided index-table.
;;; Author: Jake Marsh 4-24-14
(defun create-indexes (element index-table knowledge-base current-index)
    (cond
        ;; only recurse if a list
        ((listp element)
          ;; check if at a parent-level axiom,
          ;; and store the index in array if so (for later adding to hash table)
          (loop for x from 0 to (- (length knowledge-base) 1) do
            (if (equal (nth x knowledge-base) element)
              (setq current-index x)))
          
          ;; recursively call create-indexes on each element of axiom list
          (loop for term in element do
              (create-indexes term index-table knowledge-base current-index)))
         
         ;; else if it's a single item, add to hashtable if it's not an operator
         ((not (is-operator? element))
	        ;; if symbol doesn't exist in hash table yet, 
	        ;; create it as a list and add current axiom index
	        (if (not (gethash element index-table))
	            (setf (gethash element index-table) (list current-index))
           
	          ;; otherwise, just add current index to that item's list in the hash table if not already
	          (if (not (member current-index (gethash element index-table)))
                (setf (gethash element index-table) (append (gethash element index-table) (list current-index)))))))
  index-table)


;;; Function: get-containing-axioms
;;;
;;;   Retrieves all the axioms in the knowledge-base that contain any of the terms
;;;   in the provided list, using the previously created index and knowledge base
;;;   for searching and retrieval.
;;;
;;; Arglist: terms, knowledge-base, indexes
;;; Returns: a list of axioms in the knowledge-base that contain any of the terms specified.
;;; Side-effects:
;;; Author: Jake Marsh 4-24-14
(defun get-containing-axioms (terms knowledge-base indexes)
  (let ((containing-axioms (list)))
    (loop for term in terms do
      (let ((occurrence-indexes (gethash term indexes)))
         (loop for index in occurrence-indexes do
           (push (nth index knowledge-base) containing-axioms))))
    containing-axioms))

;;; //==========================================================================

(defun attempt-unify (statement knowledge-base indexes)
  ;; terms-pairs are of the format (<term>, <statement>)
  (let* ((term-pairs (get-terms statement (list) (list))) (containing-axioms (list)))
    ;; loop through term-pairs, extracting all necessary information
    (loop for pair in term-pairs do
      (setf containing-axioms (append containing-axioms (get-containing-axioms (list (first pair)) knowledge-base indexes))))
    
    ;; loop through all of the containing axioms
    (loop for axiom in containing-axioms do
      (loop for pair in term-pairs do
        ;; try to unify with each <statement> within the terms if an obvious simple axiom
        (cond
          ((and (listp axiom) (= (length axiom) 2) (not (is-operator? (first axiom))))
	        (if (unify (second pair) axiom)
	          ;; if successful, determine what part of the clause remains and return (t <remaining-clause>)
	          (return-from attempt-unify (list t nil))))
          ;; if no first-level unification was found, go deeper into nested lists
          ((listp axiom)
            (loop for element in axiom do
              (cond
                ;; try to unify if an obvious simple axiom
                ((and (listp element) (= (length element) 2) (not (is-operator? (first element))))
                  (if (unify (second pair) element)
                    (return-from attempt-unify (list t nil))))
                ;; again go deeper if no second-level unification was found
                ((listp element)
                  (loop for item in element do
                    (if (unify (second pair) item)
                      (return-from attempt-unify (list t nil)))))))))))
          
    ;; return (nil nil) if no unifications were successful
    (list nil nil)))

;;; Function: theorem-prover
;;;
;;;   Runs the theorem solver on the given knowledge base
;;;   using the previously created indexes.
;;;
;;; Arglist: theorem knowledge-base indexes
;;; Returns: Result of resolution theorem prover.
;;; Side-effects:
;;; Author: Jake Marsh 4-23-14
(defun theorem-prover (theorem knowledge-base indexes)
  ;; start with just the negated theorem in TBU, and a place to save the clause
  ;; resulting from a unification
  (let ((to-be-used (list theorem)) (clause nil))
    ;; if theorem is an 'AND', split it up and start TBU over with the 2 axioms
    (if (and? theorem)
      (setf to-be-used (list (second theorem) (third theorem))))
    
    ;; loop, removing a statement from TBU, finding unifications, and put them in TBU
    (loop while (> (length to-be-used) 0) do
      ;; reset list of checked axioms
      (setf checked-axioms (list))
      
      ;; remove statement from TBU
      (let ((statement (pop to-be-used)))
	          
	     ;; Try to find unification, save result as clause
	     ;; attempt-unify returns data in the form (<successful?>, <clause>)
	     (let ((unify-result (attempt-unify statement knowledge-base indexes)))
           ;; if unification was successful, get remaining clause and save it as 'clause'
           (if (first unify-result)
               (setf clause (second unify-result))
             ;; else, unification (and current branch) failed
             (return-from theorem-prover nil)))
	           
	       ;; if resulting clause is empty, theorem proved
		   (if (or (null clause) (= (length clause) 0))
	          (return-from theorem-prover t)
	         ;; else, if the negated value of clause is in the TBU remove it and don't add anything
	         (if (member (negate clause) to-be-used)
	             (setf to-be-used (delete (negate clause) to-be-used))
		       ;; else, add to TBU if not already there
		       (if (not (member clause to-be-used))
		         (push clause to-be-used)))
		   ))))
  nil)

;; for backtracking:
;; maintain a "last TBU" as a previous snapshot of TBU list.
;; if come to a dead end, save the wrong choice as a variable
;; and revert to the "last TBU", making sure not to use the wrong choice again.
;; only consider the prover 'failed' if all of the axioms remaining in TBU
;; have been checked and failed

;;; //==========================================================================

;;; Function: run-test
;;;
;;;   Retrieves the axioms and theorem for the specified domain, then 
;;;   runs the theorem prover. Returns the result of the prover (t or nil).
;;;
;;; Arglist: domain
;;; Returns: result of running the theorem prover on the specified domain.
;;; Side-effects:
;;; Author: Jake Marsh 4-23-14
(defun run (domain)
  (format t "~%")
  (let ((knowledge-base (get-knowledge-base domain)) (theorem (negate (get-theorem domain))))
    (let ((indexes (make-hash-table)))
      (create-indexes knowledge-base indexes knowledge-base 0)
      
      (format t "negated theorem: ~s~%" theorem)
      (format t "knowledge base: ~s~%" knowledge-base)
      
      (if (theorem-prover theorem knowledge-base indexes)
          (format t "~%Theorem was successfully proven.~%")
        (format t "~%Theorem was not able to be proven.~%"))
    )))

;;; //==========================================================================

(run 0)
(format t "~%~%~%")
(run 1)