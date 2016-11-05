;;; -*- mode: lisp -*-
;;; 
;;; (c) copyright 2005 by Aleksandar Bakic (a_bakic@yahoo.com)
;;; 

;;; Adaptation of binary sequences by Robert Will (real-world-phenomena.org)
;;; Like obinseq, but keeping two counts:
;;;   the number of lines (length) and the number of objects in lines (size)
;;;   a leaf is an integer, the number of object in the corresponding line

(in-package :binseq)

(defun obinseq2-p (s)
  (or (null s)
      (integerp s)
      (and (consp s)
	   (and (let ((v (car s)))
		  (and (vectorp v)
		       (= (length v) 2)
		       (integerp (aref v 0))
		       (integerp (aref v 1))))
		(consp (cdr s))
		(obinseq2-p (cadr s))
		(obinseq2-p (cddr s))))))

(defun list-obinseq2 (l)
  (flet ((%split (l n) ; TODO: use side-effects to avoid consing
	   (loop for b on l
	      and i from 0
	      if (< i n)
	      collect (car b) into a
	      else do (return (values a b))
	      finally (return (values l nil)))))
    (cond
      ((null l) nil)
      ((null (cdr l))
       (let ((e (car l)))
       (assert (integerp e) nil
	       "Sequence element must be an integer: ~S" e)
       e))
      (t (let ((len (length l)))
	   (multiple-value-bind (a b) (%split l (floor len 2))
	     (let* ((sa (list-obinseq2 a))
		    (sb (list-obinseq2 b))
		    (size (+ (obinseq2-size sa) (obinseq2-size sb))))
	       `(#(,len ,size) . (,sa . ,sb)))))))))

(defun obinseq2-list (s)
  (labels ((%to-list (s l)
	     (cond
	       ((null s) nil)
	       ((integerp s) (cons s l))
	       (t (%to-list (cadr s) (%to-list (cddr s) l))))))
    (%to-list s nil)))

(defun obinseq2-empty (s)
  (null s))

(defun obinseq2-length (s)
  (cond
    ((null s) 0)
    ((integerp s) 1)
    (t (aref (car s) 0))))

(defun obinseq2-size (s)
  (cond
    ((null s) 0)
    ((integerp s) s)
    (t (aref (car s) 1))))

(defun obinseq2-cons (e s)
  (obinseq2-append e s))

(defun obinseq2-snoc (e s)
  (obinseq2-append s e))

(defun obinseq2-append (a b)
  (labels ((%not-much-longer (a b)
	     (<= (obinseq2-length a) (* *imbalance-bound* (obinseq2-length b))))
	   (%much-shorter (a b)
	     (not (%not-much-longer b a)))
	   (%similar-in-length (a b)
	     (and (%not-much-longer a b) (%not-much-longer b a)))
	   (%cond-single (la lb lc)
	     (and (<= lb (* *imbalance-bound* lc))
		  (<= (+ lb lc) (* *imbalance-bound* la))))
	   (%cond-double (la lb lc)
	     (<= (+ la lb) (* (+ 1 *imbalance-bound*) lc)))
	   (%cons (a b)
	     (let ((len (+ (obinseq2-length a) (obinseq2-length b)))
		   (size (+ (obinseq2-size a) (obinseq2-size b))))
	       (assert (>= len 2))
	       `(#(,len ,size) . (,a . ,b))))
	   (%rotate-right (s1 s2)
	     (cond
	       ((consp s1)
		(let* ((a (cadr s1))
		       (b (cddr s1))
		       (la (obinseq2-length a))
		       (lb (obinseq2-length b))
		       (ls2 (obinseq2-length s2)))
		  (cond
		    ((%cond-single la lb ls2)
		     (%cons a (%cons b s2)))
		    ((%cond-double la lb ls2)
		     (let ((s11 (cadr b))
			   (s12 (cddr b)))
		       (%cons (%cons a s11) (%cons s12 s2))))
		    (t (%append a (%append b s2))))))
	       (t (%append a (%append b s2)))))
	   (%rotate-left (s1 s2)
	     (cond
	       ((consp s2)
		(let* ((a (cddr s2))
		       (b (cadr s2))
		       (la (obinseq2-length a))
		       (lb (obinseq2-length b))
		       (ls1 (obinseq2-length s1)))
		  (cond
		    ((%cond-single la lb ls1)
		     (%cons (%cons s1 b) a))
		    ((%cond-double la lb ls1)
		     (let ((s21 (cddr b))
			   (s22 (cadr b)))
		       (%cons (%cons s1 s22) (%cons s21 a))))
		    (t (%append (%append s1 b) a)))))
	       (t (%append (%append s1 b) a))))
	   (%append (a b)
	     (cond
	       ((%similar-in-length a b)
		(%cons a b))
	       ((%much-shorter a b)
		(%rotate-left a b))
	       (t (%rotate-right a b)))))
    (cond
      ((null a) b)
      ((null b) a)
      (t (%append a b)))))

(defun obinseq2-front (s i)
  (cond
    ((<= i 0) nil)
    ((<= (obinseq2-length s) i) s)
    (t (cond
	 ((<= i (obinseq2-length (cadr s))) (obinseq2-front (cadr s) i))
	 (t (obinseq2-append
	     (cadr s)
	     (obinseq2-front (cddr s) (- i (obinseq2-length (cadr s))))))))))

(defun obinseq2-back (s i)
  (cond
    ((<= i 0) nil)
    ((<= (obinseq2-length s) i) s)
    (t (cond
	 ((<= i (obinseq2-length (cddr s))) (obinseq2-back (cddr s) i))
	 (t (obinseq2-append
	     (obinseq2-back (cadr s) (- i (obinseq2-length (cddr s))))
	     (cddr s)))))))

(defun %o2has-index (s i)
  (and (<= 0 i) (< i (obinseq2-length s))))

(defun %o2has-gap (s i)
  (and (<= 0 i) (<= i (obinseq2-length s))))

(defun obinseq2-get (s i)
  (assert (%o2has-index s i) nil "Index out of bounds: ~S, ~S" s i)
  (obinseq2-back (obinseq2-front s (1+ i)) 1))

(defun obinseq2-set (s i e)
  (assert (%o2has-index s i) nil "Index out of bounds: ~S, ~S, ~S" s i e)
  (obinseq2-append
   (obinseq2-front s i)
   (obinseq2-cons e (obinseq2-back s (- (obinseq2-length s) i 1)))))

(defun obinseq2-sub (s i n)
  (assert (and (>= n 0) (<= (+ i n) (obinseq2-length s))) nil
	  "Invalid subsequence bounds: ~S, ~S, ~S" s i n)
  (obinseq2-back (obinseq2-front s (+ i n)) n))

(defun obinseq2-insert (s i e)
  (assert (%o2has-gap s i) nil "Index out of bounds: ~S, ~S, ~S" s i e)
  (obinseq2-append
   (obinseq2-front s i)
   (obinseq2-cons e (obinseq2-back s (- (obinseq2-length s) i)))))

(defun obinseq2-insert* (s i s2)
  (assert (%o2has-gap s i) nil "Index out of bounds: ~S, ~S, ~S" s i s2)
  (if (null s2)
      s
      (obinseq2-append
       (obinseq2-front s i)
       (obinseq2-append s2 (obinseq2-back s (- (obinseq2-length s) i))))))

(defun obinseq2-remove (s i)
  (assert (%o2has-index s i) nil "Index out of bounds: ~S, ~S" s i)
  (obinseq2-append
   (obinseq2-front s i)
   (obinseq2-back s (- (obinseq2-length s) i 1))))

(defun obinseq2-remove* (s i n)
  (assert (%o2has-index s i) nil "Start index out of bounds: ~S, ~S, ~S" s i n)
  (assert (and (>= n 0) (<= (+ i n) (obinseq2-length s))) nil
	  "Count out of range: ~S, ~S, ~S" s i n)
  (if (zerop n)
      s
      (obinseq2-append
       (obinseq2-front s i)
       (obinseq2-back s (- (obinseq2-length s) i n)))))
