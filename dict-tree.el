
;;; dict-tree.el --- dictionary data structure package


;; Copyright (C) 2004-2006 Toby Cubitt

;; Author: Toby Cubitt <toby-predictive@dr-qubit.org>
;; Version: 0.8.3
;; Keywords: dictionary, tree
;; URL: http://www.dr-qubit.org/emacs.php


;; This file is NOT part of Emacs.
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
;; MA 02110-1301, USA.


;;; Commentary:
;;
;; A dictionary is used to store strings, along with arbitrary data
;; associated with each string. As well as basic data insertion,
;; manipulation and retrieval, a dictionary can perform prefix
;; searches on those strings, retrieving all strings with a given
;; prefix in either alphabetical or any other order (see the
;; `dictree-complete' and `dictree-complete-ordered' functions), and
;; is able to cache results in order to speed up those searches. The
;; package also provides persistent storage of the data structures to
;; files.
;;
;; A dictionary consists of a list containing either 5 or 10 elements
;; (see the dictree-create function for details).
;;
;; This package uses the ternary search tree package, tstree.el.


;;; Change log:
;;
;; Version 0.8.3
;; * fixed internal function and macro names
;; * changed naming prefix from dict- to dictree- to avoid conflicts
;; * `dict-write' now unloads old name and reloads new
;;
;; Version 0.8.2
;; * added more commentary
;;
;; Version 0.8.1
;; * fixed nasty bug in `dict-map' and `dict-mapcar' caused by dynamic scoping
;;
;; Version 0.8
;; * changed `dict-map(car)' into functions and made them work with
;;   lookup-only dicts
;; * `dict-insert' now returns the new data value
;; * rewrote cache data structures: data is now wrapped inside a cons cell, so
;;   that cache entries can point to it instead of duplicating it. This fixes
;;   some caching bugs and makes updating cached data when inserting words
;;   much faster
;; * dictionaries (but not lookup-only) can now associate two pieces of data
;;   with each word: normal data, used to rank words returned by
;;   `dict-complete-ordered', and meta-data, not used for ranking
;; * modified functions to work with new caching and meta-data, and added
;;   `dict-set-meta-data' and `dict-lookup-meta-data'
;; * renamed to `dict-tree' to help avoid conflicts with other packages
;;
;; Version 0.7
;; * added `dict-mapcar' macro
;;
;; Version 0.6.2
;; * minor bug fixes
;;
;; Version 0.6.1
;; * minor bug fixes
;;
;; Version 0.6
;; * added dict-size function
;; * added dict-dump-words-to-buffer function
;; * dictionaries now set their names and filenames by doing a library search
;;   for themselves when loaded using require
;; * added `read-dict' minibuffer completion function
;; * interactive commands that read a dictionary name now provide completion
;;
;; Version 0.5
;; * added dict-dump-words-to-file function
;;
;; Version 0.4
;; * fixed bug in dict-read-line
;;
;; Version 0.3
;; * added dict-map function
;;
;; Version 0.2
;; * added dictionary autosave flag and related functions;
;; * fixed bug preventing dict caches being loaded properly;
;; * explicitly require cl.el;
;;
;; Note: version 0.1 dictionaries not compatible with version 0.2 and above!
;;
;; Version 0.1
;; * initial release



;;; Code:

(provide 'dict-tree)
(require 'tstree)
;; the only required common-lisp functions are `subseq', `map' and `merge'
(require 'cl)




;;; ====================================================================
;;;  Internal functions and variables for use in the dictionary package


(defvar dictree-loaded-list nil
  "Stores list of loaded dictionaries.")


(defmacro dictree--name (dict)  ; INTERNAL USE ONLY
  ;; Return the name of dictonary DICT
  `(nth 1 ,dict)
)


(defmacro dictree--set-name (dict name)  ; INTERBAL USE ONLY
  ;; Set the name of dictionary DICT
  `(setcar (cdr ,dict) ,name)
)


(defmacro dictree--filename (dict)  ; INTERNAL USE ONLY.
  ;; Return the filename of dictionary DICT
  `(nth 2 ,dict)
)


(defmacro dictree--set-filename (dict filename)  ; INTERNAL USE ONLY.
  ;; Set the filename of dictionary DICT
  `(setcar (cdr (cdr ,dict)) ,filename)
)


(defmacro dictree--autosave (dict)  ; INTERNAL USE ONLY
  ;; Return the autosave flag of dictionary DICT
  `(nth 3 ,dict)
)


(defmacro dictree--set-autosave (dict flag)  ; INTERNAL USE ONLY
  ;; Set the autosave flag of dictionary DICT
  `(setcar (cdr (cdr (cdr ,dict))) ,flag)
)


(defmacro dictree--modified (dict)  ; INTERNAL USE ONLY
  ;; Return the modified flag of dictionary DICT
  `(nth 4 ,dict)
)


(defmacro dictree--set-modified (dict flag)  ; INTERNAL USE ONLY
  ;; Set the modified flag of dictionary DICT
  `(setcar (cdr (cdr (cdr (cdr ,dict)))) ,flag)
)


(defmacro dictree--tstree (dict)  ; INTERNAL USE ONLY.
  ;; Return the ternary search tree of dictionary DICT
  `(nth 5 ,dict)
)


(defmacro dictree--lookup-only (dict)  ; INTERNAL USE ONLY.
  ;; Return the lookup-only setting of dictionary DICT
  `(nth 6 ,dict)
)


(defmacro dictree--lookup-hash (dict)  ; INTERNAL USE ONLY
  ;; Return the lookup hash table of dictionary DICT
  `(nth 7 ,dict)
)


(defmacro dictree--set-lookup-hash (dict hash)  ; INTERNAL USE ONLY
  ;; Set the completion hash for dictionary DICT
  `(setcar (cdr (cdr (cdr (cdr (cdr (cdr (cdr ,dict))))))) ,hash)
)


(defmacro dictree--lookup-speed (dict)  ; INTERNAL USE ONLY
  ;; Return the lookup speed of dictionary DICT
  `(nth 8 ,dict)
)


(defmacro dictree--completion-hash (dict)  ; INTERNAL USE ONLY
  ;; Return the completion hash table of dictionary DICT
  `(nth 9 ,dict)
)


(defmacro dictree--set-completion-hash (dict hash)  ; INTERNAL USE ONLY
  ;; Set the completion hash for dictionary DICT
  `(setcar (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr ,dict))))))))) ,hash)
)


(defmacro dictree--completion-speed (dict)  ; INTERNAL USE ONLY
  ;; Return the completion speed of dictionary DICT
  `(nth 10 ,dict)
)


(defmacro dictree--ordered-hash (dict)  ; INTERNAL USE ONLY
  ;; Return the ordered completion hash table of dictionary DICT
  `(nth 11 ,dict)
)


(defmacro dictree--set-ordered-hash (dict hash)  ; INTERNAL USE ONLY
  ;; Set the completion hash for dictionary DICT
  `(setcar (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr ,dict)
							     ))))))))))
	   ,hash)
)


(defmacro dictree--ordered-speed (dict)  ; INTERNAL USE ONLY
  ;; Return the ordered completion speed of dictionary DICT
  `(nth 12 ,dict)
)


(defmacro dictree--insfun (dict)  ; INTERNAL USE ONLY.
  ;; Return the insert function of dictionary DICT.
  `(if (dictree--lookup-only ,dict)
       (nth 2 ,dict)
     (tstree--tree-insfun (dictree--tstree ,dict)))
)


(defmacro dictree--rankfun (dict)  ; INTERNAL USE ONLY
  ;; Return the rank function of dictionary DICT.
  `(if (dictree--lookup-only ,dict)
       nil
     (tstree--tree-rankfun (dictree--tstree ,dict)))
)


(defmacro dictree--wrap-data (data &optional meta-data)  ; INTERNAL USE ONLY
  ;; wrap the data in a cons cell
  `(cons ,data ,meta-data))


(defmacro dictree--get-data (cell)  ; INTERNAL USE ONLY
  ;; get data component from data cons cell
  `(car ,cell))


(defmacro dictree--set-data (cell data)  ; INTERNAL USE ONLY
  ;; set data component of data cons cell
  `(setcar ,cell ,data))


(defmacro dictree--get-metadata (cell)  ; INTERNAL USE ONLY
  ;; get meta-data component of data cons cell
  `(cdr ,cell))


(defmacro dictree--set-metadata (cell meta-data)  ; INTERNAL USE ONLY
  ;; set meta-data component of data cons cell
  `(setcdr ,cell ,meta-data))


(defmacro dictree--wrap-insfun (insfun)  ; INTERNAL USE ONLY
  ;; return wrapped insfun to deal with data wrapping
  `(lambda (new cell)
     ;; if data doesn't already exist, wrap and return new data
     (if (null cell)
	 (dictree--wrap-data (funcall ,insfun new nil))
       ;; oterhwise, update data cons cell with new data and return it
       (dictree--set-data cell (funcall ,insfun new (dictree--get-data cell)))
       cell))
)


(defmacro dictree--wrap-rankfun (rankfun)  ; INTERNAL USE ONLY
  ;; return wrapped rankfun to deal with data wrapping
  `(lambda (a b) (funcall ,rankfun (cons (car a) (dictree--get-data (cdr a)))
			  (cons (car b) (dictree--get-data (cdr b))))))


(defmacro dictree--wrap-filter (filter)  ; INTERNAL USE ONLY
  ;; return wrapped filter function to deal with data wrapping
  `(lambda (str data) (funcall ,filter str (dictree--get-data data))))



(defmacro dictree--cache-create (list maxnum)  ; INTERNAL USE ONLY
  ;; Return a completion cache entry
  `(cons ,list ,maxnum))


(defmacro dictree--cache-completions (cache)  ; INTERNAL USE ONLY
  ;; Return the completions list for cache entry CACHE
  `(car ,cache))


(defmacro dictree--cache-maxnum (cache)  ; INTERNAL USE ONLY
  ;; Return the max number of completions returned for cache entry CACHE
  `(cdr ,cache))


(defmacro dictree--set-cache-completions (cache completions)  ; INTERNAL USE ONLY
  ;; Set the completions list for cache entry CACHE
  `(setcar ,cache ,completions))


(defmacro dictree--set-cache-maxnum (cache maxnum)  ; INTERNAL USE ONLY
  ;; Set the completions list for cache entry CACHE
  `(setcdr ,cache ,maxnum))




;;; ================================================================
;;;      The public functions which operate on dictionaries


(defun dictree-p (obj)
  "Return t if OBJ is a dictionary, nil otherwise."
  (eq (car-safe obj) 'DICT)
)


(defun dictree-name (dict)
  "Return dictionary DICT's name."
  (dictree--name dict)
)


(defun dictree-create (name &optional filename autosave
			      lookup-speed complete-speed
			      ordered-speed lookup-only
			      insert-function rank-function
			      unlisted)
  "Create an empty dictionary stored in variable NAME, and return it.

Optional argument FILENAME supplies a directory and file name to
use when saving the dictionary. If the AUTOSAVE flag is non-nil,
then the dictionary will automatically be saved to this file when
it is unloaded or when exiting emacs.

The SPEED settings set the desired speed for the corresponding
dictionary search operations (lookup, completion, ordered
completion), in seconds. If a particular instance of the
operation \(e.g. looking up the word \"cat\"\) takes longer than
this, the results will be cached in a hash table. If exactly the
same operation is requested subsequently, it should perform
significantly faster. \(Note \"should\": there's no guarantee!\)
The down side is that the memory or disk space required to store
the dictionary grows, and inserting words into the dictionary
becomes slower, since the cache has to be synchronized.

All SPEED's default to nil. The values nil and t are special. If
a SPEED is set to nil, no caching is done for that operation. If
it is set to t, everything is cached for that operation \(similar
behaviour can be obtained by setting the SPEED to 0, but it is
better to use t\).

If LOOKUP-ONLY is non-nil, it disables all advanced search
features for the dictionary \(currently, completion\). All the
SPEED settings are ignored, as is the RANK-FUNCTION, and
everything is stored in the lookup cache, even when inserting
data. This is appropriate when a dictionary is only going to be
used for lookup, since it speeds up lookups *and* decreases the
memory required.


Optional argument INSERT-FUNCTION sets the function used to
insert data into the dictionary. It should take two arguments:
the new data, and the data already in the dictionary (or nil if
none exists yet). It should return the data to insert. It
defaults to replacing any existing data with the new data.

Optional argument RANK-FUNCTION sets the function used to rank
the results of the `dictree-complete-ordered' function. It should
take two arguments, each a cons whose car is a word in the
dictionary and whose cdr is the data associated with that
word. It should return non-nil if the first argument is
\"better\" than the second, nil otherwise. It defaults to string
comparison of the words, ignoring the data \(which is not very
useful, since the `dictree-complete' function already returns
completions in alphabetical order much more efficiently, but at
least will never cause any errors, whatever data is stored!\)

If optional argument UNLISTED is non-nil, the dictionary will not
be added to the list of loaded dictionaries. Note that this will
disable autosaving."

  ;; a dictionary is a list containing:
  ;; ('DICT
  ;;  name
  ;;  filename
  ;;  autosave flag
  ;;  modified flag
  ;;  tstree / insert-function (if lookup-only)
  ;   lookup-only
  ;;  lookup-hash
  ;;  --- rest only if not lookup-only ---
  ;;  lookup-speed
  ;;  complete-hash
  ;;  complete-speed
  ;;  ordered-hash
  ;;  ordered-speed)
  (let (dict insfun rankfun)
    
    ;; wrap insert-function and rank-function to deal with data wrapping
    (setq insfun (if insert-function
		     (eval (macroexpand `(dictree--wrap-insfun ,insert-function)))
		   ;; insert-function defaults to "replace"
		   (lambda (a b) a))
	  
	  rankfun (if rank-function
		      (eval (macroexpand `(dictree--wrap-rankfun ,rank-function)))
		    ;; rank-function defaults to numeric comparison of data
		    (lambda (a b) (> (dictree--get-data (cdr a))
				     (dictree--get-data (cdr b))))))
    
    (setq dict
	 (if lookup-only
	     ;; if dict is lookup only, use insert-function since there's no
	     ;; need to wrap data, and store it where tstree usually goes
	     (list 'DICT (symbol-name name) filename
		   autosave t insert-function t
		   (make-hash-table :test 'equal))
	   
	   (list 'DICT (symbol-name name) filename autosave t
		 (tstree-create '- insfun rankfun) nil
		 (if lookup-speed (make-hash-table :test 'equal) nil)
		 lookup-speed
		 (if complete-speed (make-hash-table :test 'equal) nil)
		 complete-speed
		 (if ordered-speed (make-hash-table :test 'equal) nil)
		 ordered-speed)))
    ;; add dictionary to loaded list
    (unless unlisted (push dict dictree-loaded-list))
    dict)
)




(defun dictree-create-type (name type &optional filename autosave
			      lookup-speed complete-speed ordered-speed)
  "Create an empty dictionary of type TYPE stored in variable NAME, and return
it. Type can be one of dictionary, spell-check, lookup, or
frequency. `dictree-create-type' is a simplified interface to `dictree-create'.

The \"dictionary\" type is exactly like a normal, paper-based dictionary: it
can associate arbitrary data with any word in the dictionary. Inserting data
for a word will replace any existing data for that word. All SPEED arguments
default to nil.

A \"spell-check\" dictionary stores words, but can not associate any data with
the words. It is appropriate when the dictionary will only be used for
checking if a word is in the dictionary (e.g. for spell-checking). All SPEED
arguments default to nil.

A \"lookup\" dictionary is like a dictionary-type dictionary, but can only be
used to look up words, not for more advanced searches (e.g. word
completion). This has both speed and memory benefits. It is appropriate when
the more advanced searches are not required. Any SPEED arguments are ignored.

A \"frequency\" dictionary associates a number with each word in the
dictionary. Inserting new data adds it to the existing data. It is
appropriate, for instance, when storing word-frequencies\; the
`dictree-complete-ordered' function can then be used to return the most likely
completions. All SPEED arguments default to nil.

See `dictree-create' for more details.


Technicalities:

For the \"dictionary\" type, INSERT-FUNCTION is set to \"replace\", and
RANK-FUNCTION to string comparison of the words (not very useful, since the
`dictree-complete' function already returns completions sorted alphabetically,
and does it much more efficiently than `dictree-complete-ordered', but at least
it will not cause errors!).

For the \"spell-check\" type, INSERT-FUNCTION is set to a function that always
returns t. RANK-FUNCTION is set to string comparison of the words.

For the \"lookup\" type, INSERT-FUNCTION is set to \"replace\", and
LOOKUP-ONLY is set to t.

For the \"frequency\" type, INSERT-FUNCTION sums the new and existing
data. Nil is treated as 0. The RANK-FUNCTION is set to numerical
\"greater-than\" comparison of the data."
  
  (let (insfun rankfun lookup-only)
    ;; set arguments based on type
    (cond
     ;; dictionary type
     ((eq type 'dictionary)
      (setq insfun (lambda (a b) a))
      (setq rankfun (lambda (a b) (string< (car a) (car b)))))
     
     ;; spell-check type
     ((eq type 'spell-check)
      (setq insfun (lambda (a b) t))
      (setq rankfun (lambda (a b) (string< (car a) (car b)))))
     
     ;; lookup type
     ((eq type 'lookup)
      (setq insfun (lambda (a b) a))
      (setq rankfun (lambda (a b) (string< (car a) (car b))))
      (setq lookup-only t))
     
     ;; frequency type
     ((eq type 'frequency)
      (setq insfun (lambda (new old)
		     (cond ((and (null new) (null old)) 0)
			   ((null new) old)
			   ((null old) new)
			   (t (+ old new)))))
      (setq rankfun (lambda (a b) (> (cdr a) (cdr b)))))
     )
    
    (dictree-create name filename autosave
		 lookup-speed complete-speed ordered-speed
		 lookup-only insfun rankfun))
)




(defun dictree-insert-function (dict)
  "Return the insertion function for dictionary DICT."
  (dictree--insfun dict)
)



(defun dictree-rank-function (dict)
  "Return the rank function for the dictionary DICT (note: returns nil if
lookup-only is set for the dictionary)."
  (dictree--rankfun dict)
)



(defun dictree-empty (dict)
  "Return t if the dictionary DICT is empty, nil otherwise."
  (if (dictree--lookup-only dict)
      (= 0 (hash-table-count (dictree--lookup-hash dict)))
    (tstree-empty (dictree--tstree dict)))
)




(defun dictree-insert (dict word &optional data insert-function)
  "Insert WORD and DATA into dictionary DICT.
If WORD does not already exist, this creates it. How the data is inserted
depends on the dictionary's insertion function (see `dictree-create').

The optional INSERT-FUNCTION over-rides the dictionary's own insertion
function. It should take two arguments: the data DATA, and the data associated
with WORD in the dictionary (nil if none already exists). It should return the
data to insert."
  ;; make sure WORD is a string
  (when (not (stringp word))
    (error "Wrong argument type stringp, %s" (prin1-to-string word)))
  (when (not (dictree-p dict))
    (error "Wrong argument type dictree-p"))
  
  (let ((insfun (if insert-function
		    (eval (macroexpand `(dictree--wrap-insfun ,insert-function)))
		  (dictree--insfun dict))))
    ;; set the dictionary's modified flag
    (dictree--set-modified dict t)
    
    ;; if dictionary is lookup-only, just insert the data in the lookup cache
    (if (dictree--lookup-only dict)
	(let ((lookup-hash (dictree--lookup-hash dict)))
	  (puthash
	   word (funcall insfun data (gethash word lookup-hash))
	   lookup-hash))

      
      ;; otherwise...
      (let ((tstree (dictree--tstree dict))
	    newdata)
	
        ;; insert word in dictionary's ternary search tree
	(setq newdata (tstree-insert tstree word data insfun))
	
	
        ;; synchronize the completion caches
	(when (or (dictree--completion-speed dict) (dictree--ordered-speed dict))
	  (let ((completion-hash (dictree--completion-hash dict))
		(ordered-hash (dictree--ordered-hash dict))
		(rankfun (dictree--rankfun dict))
		str wrd cache cmpl maxnum)
	    
	    ;; have to check every possible substring that could be cached!
	    (dotimes (i (1+ (length word)))
	      (setq str (substring word 0 i))

	      ;; synchronize the completion hash, if it exists
	      (when (and (dictree--completion-speed dict)
			 (setq cache (gethash str completion-hash)))
		(setq cmpl (dictree--cache-completions cache))
		(setq maxnum (dictree--cache-maxnum cache))
		;; if word is already in the completion list, it doesn't need
		;; updating, otherwise update it from the tree
		;; (Note: we could instead add word to the list and re-sort,
		;;  but it's probably not worth it)
		(unless (assoc word cmpl)
		  (setcar cache
			  (tstree-complete (dictree--tstree dict) str maxnum))))
	      
	      
	      ;; synchronize the ordered completion hash, if it exists
	      (when (and (dictree--ordered-speed dict)
			 (setq cache (gethash str ordered-hash)))
		(setq cmpl (dictree--cache-completions cache))
		(setq maxnum (dictree--cache-maxnum cache))
		(setq wrd (substring word i))
		(cond
		 
		 ;; if word is in the completion list...
		 ((assoc wrd cmpl)
		  ;; re-sort the list
		  (dictree--set-cache-completions cache (sort cmpl rankfun))
		  (setq cmpl (dictree--cache-completions cache))
		  ;; if word is now at the end of the list, we've no choice
		  ;; but to update from the tree
		  (when (equal (caar (last cmpl)) wrd)
		    (dictree--set-cache-completions
		     cache (tstree-complete-ordered tstree str maxnum
						    nil rankfun))))
		 
		 ;; if word isn't in the completion list...
		 (t
		  ;; add word to the end of the list and re-sort
		  (setcdr (last cmpl) (list (cons wrd newdata)))
		  (dictree--set-cache-completions cache (sort cmpl rankfun))
		  (setq cmpl (dictree--cache-completions cache))
		  ;; remove excess completions
		  (when (> (length cmpl) maxnum)
		    (setcdr (nthcdr (1- maxnum) cmpl) nil)))))
	      )))
	
	;; return the new data value
	(dictree--get-data newdata))))
)



(defun dictree-lookup (dict word)
  "Return the data associated with WORD in dictionary DICT, or nil if WORD is
not in the dictionary.

Note: this will not distinguish between a non-existent WORD and a WORD whose
data is nil. \(\"spell-check\" type dictionaries created using
`dictree-create-type' store t as the data for every word to avoid this problem)
Use `dictree-member-p' to distinguish non-existent words from nil data."
  
  ;; first check the lookup hash for the word
  (let ((data (if (dictree--lookup-speed dict)
		  (gethash word (dictree--lookup-hash dict))
		nil))
	time)
    
    ;; if it wasn't in the lookup hash and the dictionary isn't lookup-only,
    ;; search in the ternary search tree
    (unless (or data (dictree--lookup-only dict))
      ;; time the lookup
      (let (time)
	(setq time (float-time))
	(setq data (tstree-member (dictree--tstree dict) word))
	(setq time (- (float-time) time))
	
        ;; if the lookup was slower than the dictionary's lookup speed, add it
        ;; to the lookup hash and set the modified flag
	(when (and (dictree--lookup-speed dict)
		   (or (eq (dictree--lookup-speed dict) t)
		       (> time (dictree--lookup-speed dict))))
	  (dictree--set-modified dict t)
	  (puthash word data (dictree--lookup-hash dict)))))
    
    ;; return the data
    (dictree--get-data data))
)



(defun dictree-set-meta-data (dict word meta-data)
  "Set meta-data (data not used to rank words) for WORD
in dictionary DICT."
  
  ;; make sure WORD is a string
  (when (not (stringp word))
    (error "Wrong argument type stringp, %s" (prin1-to-string word)))
  (when (not (dictree-p dict))
    (error "Wrong argument type dictree-p"))
  
  ;; set the dictionary's modified flag
  (dictree--set-modified dict t)
    
  ;; if dictionary is lookup-only, refuse!
  (if (dictree--lookup-only dict)
      (error "Lookup-only dictionaries can't contain meta-data")
    ;; otherwise, set word's meta-data
    (dictree--set-metadata (tstree-member (dictree--tstree dict) word) meta-data))
)


	
(defun dictree-lookup-meta-data (dict word)
  "Return any meta-data (data not used to rank words)
associated with WORD in dictionary DICT, or nil if WORD is not in
the dictionary.

Note: this will not distinguish between a non-existent WORD and a
WORD with no meta-data. Use `dictree-member-p' to distinguish
non-existent words."

  (when (dictree--lookup-only dict)
    (error "Lookup-only dictionaries can't contain meta-data"))
  
  ;; first check the lookup hash for the word
  (let ((data (if (dictree--lookup-speed dict)
		  (gethash word (dictree--lookup-hash dict))
		nil))
	time)
    
    ;; if it wasn't in the lookup hash, search in the ternary search tree
    (unless data
      ;; time the lookup
      (let (time)
	(setq time (float-time))
	(setq data (tstree-member (dictree--tstree dict) word))
	(setq time (- (float-time) time))
	
        ;; if the lookup was slower than the dictionary's lookup speed, add it
        ;; to the lookup hash and set the modified flag
	(when (and (dictree--lookup-speed dict)
		   (or (eq (dictree--lookup-speed dict) t)
		       (> time (dictree--lookup-speed dict))))
	  (dictree--set-modified dict t)
	  (puthash word data (dictree--lookup-hash dict)))))
    
    ;; return the meta-data
    (dictree--get-metadata data))
)




(defun dictree-member-p (dict word)
  "Return t if WORD is in dictionary DICT, nil otherwise."
  
  ;; if dictionary is lookup-only, look in lookup hash and use dummy variable
  ;; to distinguish non-existent words from those with nil data
  (if (dictree--lookup-only dict)
      (if (eq (gethash word (dictree--lookup-hash dict) 'not-in-here)
	      'not-in-here) nil t)
    ;; otherwise look in the ternary search tree
    (tstree-member-p (dictree--tstree dict) word))
)



;; (defun dictree-delete (dict word)
;;   "Delete WORD from DICT"
;; )



(defun dictree-map (function dict)
  "Apply FUNCTION to all entries in dictionary DICT, for side-effects only.

FUNCTION will be passed two arguments: a word from the
dictionary, and the data associated with that word. It is safe to
assume the dictionary entries will be traversed in alphabetical
order."
  
  (if (dictree--lookup-only dict)
      (maphash function (dictree--lookup-hash dict))
    ;; need to "rename" `function' or we hit a nasty dynamic scoping problem,
    ;; since `tstree-map' also binds the symbol `function'
    (let ((dictree-map-function function))
      (tstree-map
       (lambda (word data)
	 (funcall dictree-map-function word (dictree--get-data data)))
       (dictree--tstree dict) t)))
)



(defun dictree-mapcar (function dict)
  "Apply FUNCTION to all entries in dictionary DICT,
and make a list of the results.

FUNCTION will be passed two arguments: a word from the
dictionary, and the data associated with that word. It is safe to
assume the dictionary entries will be traversed in alphabetical
order."
  
  (if (dictree--lookup-only dict)
      (let (result)
	(maphash `(lambda function (word data)
		    (cons (,function word data) result))
		 (dictree--lookup-hash dict))
	result)
    ;; need to "rename" `function' or we hit a nasty dynamic scoping problem,
    ;; since `tstree-map' also binds the symbol `function'
    (let ((dictree-map-function function))
      (tstree-map
       (lambda (word data)
	 (funcall dictree-map-function word (dictree--get-data data)))
       (dictree--tstree dict) t t)))
)



(defun dictree-size (dict)
  "Return the number of entries in dictionary DICT."
  (interactive (list (read-dict "Dictionary: ")))

  (if (dictree--lookup-only dict)
      (hash-table-size dict)
    (let ((count 0))
      (tstree-map (lambda (&rest dummy) (setq count (1+ count)))
		  (dictree--tstree dict))
      (when (interactive-p)
	(message "Dictionary %s contains %d entries" (dictree--name dict) count))
      count))
)



(defun dictree-complete (dict string &optional maxnum all filter no-cache)
  "Return an alist containing all completions of STRING found in
dictionary DICT, along with their associated data, in alphabetial
order. If no completions are found, return nil.

DICT can also be a list of dictionaries, in which case
completions are sought in all dictionaries in the list, as though
they were one large dictionary.

STRING can be a single string or a list of strings. If a list is
supplied, completions of all elements of the list are returned.

The optional numerical argument MAXNUM limits the results to the
first MAXNUM completions. If it is absent or nil, all completions
are included in the returned alist.

Normally, only the remaining characters needed to complete STRING
are returned. If the optional argument ALL is non-nil, the entire
completion is returned.

The FILTER argument sets a filter function for the
completions. If supplied, it is called for each possible
completion with two arguments: the completion, and its associated
data. If the filter function returns nil, the completion is not
included in the results.

If the optional argument NO-CACHE is non-nil, it prevents caching
of the result."
  
  (let* ((dictlist (if (dictree-p dict) (list dict) dict))
	 dic)
    (cond

     ;; if a filter was supplied, look in the ternary search tree since we
     ;; don't cache filtered searches
     (filter
      ;; redefine filter to deal with data wrapping
      (setq filter `(lambda (str data) (,filter str (dictree--get-data data))))
      
      (let (treelist)
	(while dictlist
	  (setq dic (pop dictlist))
	  ;; better check that none of the dictionaries in the list are
	  ;; lookup-only
	  (when (dictree--lookup-only dic)
	    (error "Dictionary is lookup-only. Completion disabled."))
	  (setq treelist (append (dictree--tstree dic) treelist)))
	;; search the ternary search tree
	(tstree-complete treelist string maxnum all filter)))
     

     ;; if no filter was supplied...
     (t
      (let (completions
	    strlist str
	    cache cmpl
	    time speed)
	;; search each dictionary in the list
	(while dictlist
	  (setq dic (pop dictlist))
	  ;; throw a wobbly if dictionary is lookup-only
	  (when (dictree--lookup-only dic)
	    (error "Dictionary is lookup-only. Completion disabled."))
	  
	  ;; search each string in the list
	  (setq strlist (if (stringp string) (list string) string))
	  (while strlist
	    (setq str (pop strlist))
	    
	    ;; look in completion cache first
	    (setq cache (if (dictree--completion-speed dic)
			    (gethash str (dictree--completion-hash dic))
			  nil))
	    
	    ;; if we've found a cached result with enough completions...
	    (if (and cache (or (null (dictree--cache-maxnum cache))
			       (and (not (null maxnum))
				    (<= maxnum (dictree--cache-maxnum cache)))))
		(progn
		  (setq cmpl (dictree--cache-completions cache))
		  ;; drop any excess cached completions
		  (when (and maxnum (> (length cmpl) maxnum))
		    (setcdr (nthcdr (1- maxnum) cmpl) nil)))
	      
	      ;; if nothing was in the cache or the cached result contained
	      ;; fewer completions than asked for, look in the ternary search
	      ;; tree and time it
	      (setq time (float-time))
	      (setq cmpl (tstree-complete (dictree--tstree dic) str maxnum))
	      (setq time (- (float-time) time))
	      ;; if the completion function was slower than the dictionary's
	      ;; completion speed, add the results to the completion hash and
	      ;; set the dictionary's modified flag
	      (when (and (not no-cache)
			 (setq speed (dictree--completion-speed dic))
			 (or (eq speed t) (> time speed)))
		(dictree--set-modified dic t)
		(puthash str (dictree--cache-create cmpl maxnum)
			 (dictree--completion-hash dic))))
	    
	    ;; unwrap data, and add string to the fronts of the completions if
	    ;; ALL is set
	    ;;  and add string to the fronts of the completions if ALL is set
	    (when all
	      (setq cmpl
		    (mapcar (lambda (s) (cons (concat str (car s)) (cdr s)))
			    cmpl)))
	    ;; merge the cached completions with those already found
	    (setq completions
		  (merge 'list completions cmpl
			 (lambda (a b) (string< (car a) (car b)))))
	    ;; drop any excess completions
	    (when (and maxnum (> (length completions) maxnum))
	      (setcdr (nthcdr (1- maxnum) completions) nil))
	    ))
	;; return the completions list, unwrapping the data
	(mapcar (lambda (c) (cons (car c) (dictree--get-data (cdr c))))
		completions)
	))))
)





(defun dictree-complete-ordered
  (dict string &optional maxnum all rank-function filter no-cache)
  "Return an alist containing all completions of STRING found in
dictionary DICT, along with their associated data. If no
completions are found, return nil.

Note that `dictree-complete' is significantly more efficient than
`dictree-complete-ordered', especially when a maximum number of
completions is specified. Always use `dictree-complete' when you
don't care about the ordering of the completions, or you need the
completions ordered alphabetically.

DICT can also be a list of dictionaries, in which case
completions are sought in all trees in the list. If RANK-FUCTION
is ot specified, the rank function of the first dictionary in the
list is used. All the dictionaries' rank functions had better be
compatible, otherwise at best you will get unexpected results, at
worst errors.

STRING must either be a single string, or a list of strings. If a
list is supplied, completions of all elements of the list are
included in the returned alist.

The optional numerical argument MAXNUM limits the results to the
\"best\" MAXNUM completions. If nil, all completions are
returned.

Normally, only the remaining characters needed to complete STRING
are returned. If the optional argument ALL is non-nil, the entire
completion is returned.

The optional argument RANK-FUNCTION over-rides the dictionary's
default rank function. It should take two arguments, each a cons
whose car is a string referencing data in the tree, and whose cdr
is the data at that reference. It should return non-nil if the
first argument is \"better than\" the second, nil otherwise. The
elements of the returned list are sorted according to this
rank-function, in descending order.

The FILTER argument sets a filter function for the
completions. If supplied, it is called for each possible
completion with two arguments: the completion, and its associated
data. If the filter function returns nil, the completion is not
included in the results.

If the optional argument NO-CACHE is non-nil, it prevents caching
of the result."
  
  (let ((dictlist (if (dictree-p dict) (list dict) dict))
	dic rankfun)
    (cond

     ;; if the default rank function has been over-ridden or a filter
     ;; supplied, look in the ternary search tree since we don't cache
     ;; non-default rank functions or filtered searches
     ((or rank-function filter)
      ;; redefine the rank function and filter to deal with data wrapping
      (setq rankfun (eval (macroexpand `(dictree--wrap-rankfun ,rank-function))))
      (setq filter (eval (macroexpand `(dictree--wrap-filter ,filter))))
      
      (let (treelist)
	(while dictlist
	  (setq dic (pop dictlist))
	  ;; better check that none of the dictionaries in the list are
	  ;; lookup-only
	  (when (dictree--lookup-only dic)
	    (error "Dictionary is lookup-only. Completion disabled."))
	  (setq treelist (append (dictree--tstree dic) treelist)))
	;; search the ternary search tree
	(tstree-complete-ordered treelist string maxnum all
				 rankfun filter)))
     
     
     ;; if we're using the dictionary's default rank-function...
     ;; (Note: we use the rank function of first dict in list, and hope it's
     ;;        compatible with the data in the other dictionaries)
     (t
      (let ((rankfun (dictree--rankfun (car dictlist)))
	     completions
	     strlist str
	     cache cmpl
	     time speed)
	
	;; search each dictionary in the list
	(while dictlist
	  (setq dic (pop dictlist))
          ;; throw a wobbly if dictionary is lookup-only
	  (when (dictree--lookup-only dic)
	    (error "Dictionary is lookup-only. Completion disabled."))
	  
          ;; search each string in the list
	  (setq strlist (if (stringp string) (list string) string))
	  (while strlist
	    (setq str (pop strlist))

	    
	    ;; look in completion cache first
	    (setq cache (if (dictree--ordered-speed dic)
			    (gethash str (dictree--ordered-hash dic))
			  nil))
	    
	    ;; if we've found a cached result with enough completions...
	    (if (and cache (or (null (dictree--cache-maxnum cache))
			       (and (not (null maxnum))
				    (<= maxnum (dictree--cache-maxnum cache)))))
		(progn
		  (setq cmpl (dictree--cache-completions cache))
	          ;; drop any excess cached completions
		  (when (and maxnum (> (length cmpl) maxnum))
		    (setcdr (nthcdr (1- maxnum) cmpl) nil)))
	      
	      ;; if nothing was in the cache or the cached result didn't
	      ;; contain enough completions, search tree and time the search
	      (setq time (float-time))
	      (setq cmpl (tstree-complete-ordered (dictree--tstree dic)
						  str maxnum nil rankfun))
	      (setq time (- (float-time) time))
	      ;; if the completion function was slower than the dictionary's
	      ;; completion speed, add the results to the completion hash and
	      ;; set the dictionary's modified flag
	      (when (and (not no-cache)
			 (setq speed (dictree--ordered-speed dic))
			 (or (eq speed t) (> time speed)))
		(dictree--set-modified dic t)
		(puthash str (dictree--cache-create cmpl maxnum)
			 (dictree--ordered-hash dic))))
	    
	    ;;  and add string to the fronts of the completions if ALL is set
	    (when all
	      (setq cmpl
		    (mapcar (lambda (s) (cons (concat str (car s)) (cdr s)))
			    cmpl)))
	    ;; merge the cached completions with those already found
	    (setq completions (merge 'list completions cmpl rankfun))
	    ;; drop any excess completions
	    (when (and maxnum (> (length completions) maxnum))
	      (setcdr (nthcdr (1- maxnum) completions) nil))
	    ))
	
        ;; return the completions list, unwrapping the data
	(mapcar (lambda (c) (cons (car c) (dictree--get-data (cdr c))))
		completions)
	))))
)




(defun dictree-populate-from-file (dict file)
  "Populate dictionary DICT from the word list in file FILE. Each
line of the file should contain a word, delimeted by \"\". Use
the escape sequence \\\" to include a \" in the string. If a line
does not contain a delimeted string, it is silently ignored. The
words should ideally be sorted alphabetically.

Each line can also include data to be associated with the word,
separated from the word by whitespace. Anything after the
whitespace is considered data. String data should be
\"\"-delimited, and must be on a single line. However, the escape
sequence \"\\n\" can be used to include a newline, the escape
sequence \\\" can again be used to include a \", and the escape
sequence \\\\ must be used to include a \\.


Technicalities:

The word and data can actually be separated by any character that
is not a word-constituent according to the standard syntax
table. However, you're safest sticking to whitespace.

The data is read as a lisp expression and evaluated, so can be
more complex than a simple constant. However, it must be entirely
on one line. The symbol \"_word\" can be used to refer to the
word associated with the data.

The word list is read from the middle outwards, i.e. first the
middle word is read, then the word directly after it, then the
word directly before it, then the one two lines after the middle,
and so on. Assuming the words in the file are sorted
alphabetically, this helps produce a reasonably efficient
dictionary. However, it may have implications if the data is a
lisp expression that has side-effects."
  
  (save-excursion
    (let ((buff (generate-new-buffer " *dictree-populate*")))
      ;; insert the word list into a temporary buffer
      (set-buffer buff)
      (insert-file-contents file)
      
      ;; insert the words starting from the median to ensure a well-balanced
      ;; tree
      (let* ((lines (count-lines (point-min) (point-max)))
	     (midpt (+ (/ lines 2) (mod lines 2)))
	     entry)
        ;; insert the median word and set the dictionary's modified flag
	(goto-line midpt)
	(when (setq entry (dictree-read-line))
	  (dictree-insert dict (car entry) (nth 1 entry))
	  (dictree-set-meta-data dict (car entry) (nth 2 entry)))
	(message "Inserting words in %s...(1 of %d)" (dictree--name dict) lines)
        ;; insert words successively further away from the median in both
        ;; directions
	(dotimes (i (1- midpt))
	  (goto-line (+ midpt i 1))
	  (when (setq entry (dictree-read-line))
	    (dictree-insert dict (car entry) (nth 1 entry))
	    (dictree-set-meta-data dict (car entry) (nth 2 entry)))
	  (when (= 49 (mod i 50))
	    (message "Inserting words in %s...(%d of %d)"
		     (dictree--name dict) (+ (* 2 i) 2) lines))
	  (goto-line (- midpt i 1))
	  (when (setq entry (dictree-read-line))
	    (dictree-insert dict (car entry) (nth 1 entry))
	    (dictree-set-meta-data dict (car entry) (nth 2 entry))))
	
        ;; if file contains an even number of words, we still have to add
        ;; the last one
	(when (= 0 (mod lines 2))
	  (goto-line lines)
	  (when (setq entry (dictree-read-line))
	    (dictree-insert dict (car entry) (nth 1 entry))
	    (dictree-set-meta-data dict (car entry) (nth 2 entry))))
	(message "Inserting words in %s...done" (dictree--name dict)))
      
      (kill-buffer buff)))
)



;;; FIXME: doesn't fail gracefully if file has invalid format
(defun dictree-read-line ()
  "Return a cons containing the word and data \(if any, otherwise
nil\) at the current line of the current buffer. Returns nil if
line is in wrong format."
  
  (save-excursion
    (let (_word data meta-data)
      ;; search for text between quotes "", ignoring escaped quotes \"
      (beginning-of-line)
      (setq _word (read (current-buffer)))
      ;; if there is anything after the quoted text, use it as data
      (if (eq (line-end-position) (point))
	  (list _word)
	(setq data (eval (read (current-buffer))))
	(if (eq (line-end-position) (point))
	    (list _word data)
	  (setq meta-data (read (current-buffer)))
	  ;; return the word and data
	  (list _word data meta-data)))
      ))
)




(defun dictree-save (dict)
  "Save dictionary DICT to it's associated file.
Use `dictree-write' to save to a different file."
  (interactive (list (read-dict "Dictionary to save: ")))
  
  (let* ((filename (dictree--filename dict)))
    
    ;; if dictionary has no associated file, prompt for one
    (unless (and filename (> (length filename) 0))
      (setq filename
	    (read-file-name (format "Save %s to file: " (dictree--name dict)))))
    
    ;; if filename is blank, don't save
    (if (string= filename "")
	(message "Dictionary %s NOT saved" (dictree--name dict))
      ;; otherwise write dictionary to file without requiring confirmation
      (dictree-write dict filename t)))
)




(defun dictree-write (dict filename &optional overwrite uncompiled)
  "Write dictionary DICT to file FILENAME.

If optional argument OVERWRITE is non-nil, no confirmation will
be asked for before overwriting an existing file.

If optional argument UNCOMPILED is set, an uncompiled copy of the
dictionary will be created.

Interactivley, DICT and FILENAME are read from the minibuffer,
and OVERWRITE is the prefix argument."
  
  (interactive (list (read-dict "Dictionary to write: ")
		     (read-file-name "File to write to: ")
		     current-prefix-arg))

  (let* (dictname  ; saved dictionary name is constructed from the filename
	 (autosave (dictree--autosave dict))
	 (lookup-only (dictree--lookup-only dict))
	 lookup-speed completion-speed ordered-speed
	 tmpdict lookup-alist completion-alist ordered-alist
	 hashcode buff tmpfile)
    
    ;; add .el(c) extension to the filename if not already there
    (if uncompiled
	(unless (string= (substring filename -3) ".el")
	  (setq filename (concat filename ".el")))
      (unless (string= (substring filename -4) ".elc")
	(setq filename (concat filename ".elc"))))
    ;; remove .el(c) extension from filename to create saved dictionary name
    (setq dictname (if uncompiled
		       (substring (file-name-nondirectory filename) 0 -3)
		     (substring (file-name-nondirectory filename) 0 -4)))
    
    (save-excursion
      ;; create a temporary file
      (setq buff (find-file-noselect
		  (setq tmpfile (make-temp-file dictname))))
      (set-buffer buff)
      
      ;; if the dictionary is lookup only, dump the lookup cache to an alist
      (if lookup-only
	  (progn
	    (maphash (lambda (key val) (push (cons key val) lookup-alist))
		     (dictree--lookup-hash dict))
	    ;; generate code to reconstruct the lookup hash table
	    (setq hashcode
		  (concat
		   "(let ((lookup-hash (make-hash-table :test 'equal)))\n"
		   "  (mapcar (lambda (entry)\n"
		   "    (puthash (car entry) (cdr entry) lookup-hash))\n"
                   "    (dictree--lookup-hash " dictname "))\n"
		   "  (dictree--set-lookup-hash " dictname " lookup-hash)\n"))
	    ;; generate the structure to save
	    (setq tmpdict (list 'DICT dictname filename autosave
				(dictree--insfun dict) lookup-only lookup-alist)))
	
	
	;; otherwise, dump caches to alists as necessary and generate code to
	;; reonstruct the hash tables from the alists
	(setq lookup-speed (dictree--lookup-speed dict)
	      completion-speed (dictree--completion-speed dict)
	      ordered-speed (dictree--ordered-speed dict))
	
	;; create the lookup alist, if necessaru
	(when lookup-speed
	  (maphash (lambda (key val) (push (cons key val) lookup-alist))
		   (dictree--lookup-hash dict))
	  ;; generate code to reconstruct the lookup hash table
	  (setq hashcode
		(concat
		 hashcode
		 "(let ((lookup-hash (make-hash-table :test 'equal)))\n"
		 "  (mapcar (lambda (entry)\n"
		 "    (puthash (car entry) (cdr entry) lookup-hash)\n"
	         "    (dictree--lookup-hash " dictname ")))\n"
		 "  (dictree--set-lookup-hash " dictname " lookup-hash))\n")))
	
	;; create the completion alist, if necessary
	(when completion-speed
	  (maphash (lambda (key val) (push (cons key val) completion-alist))
		   (dictree--completion-hash dict))
	  ;; generate code to reconstruct the completion hash table
	  (setq hashcode
		(concat
		 hashcode
		 "(let ((completion-hash (make-hash-table :test 'equal)))\n"
		 "  (mapcar (lambda (entry)\n"
		 "    (puthash (car entry) (cdr entry) completion-hash)\n"
	         "    (dictree--completion-hash " dictname ")))\n"
		 "  (dictree--set-completion-hash " dictname " completion-hash))"
		 "\n")))
	
	;; create the ordered completion alist, if necessary
	(when ordered-speed
	  (maphash (lambda (key val) (push (cons key val) ordered-alist))
		   (dictree--ordered-hash dict))
	  ;; generate code to reconstruct the ordered hash table
	  (setq hashcode
		(concat
		 hashcode
		 "(let ((ordered-hash (make-hash-table :test 'equal)))\n"
		 "  (mapcar (lambda (entry)\n"
		 "    (puthash (car entry) (cdr entry) ordered-hash))\n"
	         "    (dictree--ordered-hash " dictname "))\n"
		 "  (dictree--set-ordered-hash " dictname " ordered-hash))\n")))
	
	;; generate the structure to save
	(setq tmpdict (list 'DICT nil nil autosave nil
			    (dictree--tstree dict) lookup-only
			    lookup-alist lookup-speed
			    completion-alist completion-speed
			    ordered-alist ordered-speed))
      )
      
      
      ;; write lisp code that generates the dictionary object
      (insert "(provide '" dictname ")\n")
      (insert "(require 'dict-tree)\n")
      (insert "(defvar " dictname " nil \"Dictionary " dictname ".\")\n")
      (insert "(setq " dictname " '" (prin1-to-string tmpdict) ")\n")
      (insert hashcode)
      (insert "(dictree--set-name " dictname " \"" dictname "\")\n")
      (insert "(dictree--set-filename " dictname
	      " (locate-library \"" dictname "\"))\n")
      (insert "(unless (memq " dictname " dictree-loaded-list)"
	      " (push " dictname " dictree-loaded-list))\n")
      (save-buffer)
      (kill-buffer buff)
	
      ;; byte-compile the code (unless uncompiled option is set) and move the
      ;; file to its final destination
      (if (or uncompiled (save-window-excursion (byte-compile-file tmpfile)))
	  (progn
	    (when (or (not (file-exists-p filename))
		      overwrite
		      (y-or-n-p
		       (format "File %s already exists. Overwrite? "
			       filename)))
	      (if uncompiled
		  (rename-file tmpfile filename t)
		(rename-file (concat tmpfile ".elc") filename t)
		(dictree--set-modified dict nil)
		;; if writing to a different name, unload dictionary under old
		;; name and reload it under new one
		(unless (string= dictname (dictree--name dict))
		  (dictree-unload dict)
		  (dictree-load filename))
		(delete-file tmpfile))
	      (message "Dictionary %s saved to %s" dictname filename)
	      t))  ; return t if dictionary was successfully saved
	;; if there were errors compiling, throw error
	(error "Error saving %s. Dictionary not saved" dictname))
      ))
)




(defun dictree-save-modified (&optional ask all)
  "Save all modified dictionaries that have a non-nil autosave flag.

If optional argument ASK is non-nil, ask for confirmation before
saving. Interactively, ASK is the prefix argument.

If optional argument ALL is non-nil, save all dictionaries, even
those without the autosave flag."
  (interactive "P")
  ;; For each loaded dictionary, check if dictionary has been modified. If so,
  ;; save it if autosave is on
  (dolist (dict dictree-loaded-list)
    (when (and (dictree--modified dict)
	       (or all (dictree--autosave dict))
	       (or (not ask) (y-or-n-p (format "Save modified dictionary %s? "
					       (dictree--filename dict)))))
      (dictree-save dict)
      (dictree--set-modified dict nil)))
)




(defun dictree-load (file)
  "Load a dictionary object from file FILE.
Returns t if successful, nil otherwise."
  (interactive "fDictionary file to load: ")
  
  ;; sort out dictionary name and file name
  (let (dictname dict)
    (when (not (string= (substring file -4) ".elc"))
      (setq file (concat file ".elc")))
    (setq dictname (substring (file-name-nondirectory file) 0 -4))
    
    ;; load the dictionary
    (load file t)
    (setq dict (eval (intern-soft dictname)))
    (when (not (dictree-p dict))
      (beep)
      (error "Error loading dictionary from %s" file))
    
    ;; ensure the dictionary name and file name associated with the dictionary
    ;; match the file it was loaded from
    (dictree--set-filename dict (expand-file-name file))
    (dictree--set-name dict dictname)
    
    ;; make sure the dictionary is in dictree-loaded-list (normally the lisp code
    ;; in the dictionary itself should do that)
    (unless (memq dict dictree-loaded-list) (push dict dictree-loaded-list))
    (message (format "Loaded dictionary %s" dictname)))
)




(defun dictree-unload (dict &optional dont-save)
  "Unload dictionary DICT.
If optional argument DONT-SAVE is non-nil, the dictionary will
NOT be saved even if its autosave flag is set."
  (interactive (list (read-dict "Dictionary to unload: ")
		     current-prefix-arg))
  
  ;; if dictionary has been modified, autosave is set and not overidden, save
  ;; it first
  (when (and (dictree--modified dict)
	     (null dont-save)
	     (or (eq (dictree--autosave dict) t)
		 (and (eq (dictree--autosave dict) 'ask)
		      (y-or-n-p
		       (format
			"Dictionary %s modified. Save before unloading? "
			(dictree--name dict))))))
    (dictree-save dict)
    (dictree--set-modified dict nil))
  
  ;; remove dictionary from list of loaded dictionaries and unload it
  (setq dictree-loaded-list (delq dict dictree-loaded-list))
  (unintern (dictree--name dict))
  (message "Dictionary %s unloaded" (dictree--name dict))
)




(defun dictree-dump-words-to-buffer (dict &optional buffer)
  "Dump words and their associated data
from dictionary DICT to BUFFER, in the same format as that used
by `dictree-populate-from-file'. If BUFFER exists, words will be
appended to the end of it. Otherwise, a new buffer will be
created. If BUFFER is omitted, the current buffer is used.

Note that if the data does not have a read syntax, the dumped
data can not be used to recreate the dictionary using
`dictree-populate-from-file'."
  
  (interactive (list (read-dict "Dictionary to dump: ")
		     (read-buffer "Buffer to dump to: "
				  (buffer-name (current-buffer)))))
  
  ;; select the buffer, creating it if necessary
  (if buffer
      (setq buffer (get-buffer-create buffer))
    (setq buffer (current-buffer)))
  (set-buffer buffer)
  
  ;; move point to end of buffer and make sure it's at start of new line
  (goto-char (point-max))
  (unless (= (point) (line-beginning-position))
    (insert "\n"))
  
  ;; dump words
  (message "Dumping words from %s to %s..."
	   (dictree--name dict) (buffer-name buffer))
  (let ((count 0) (dictsize (dictree-size dict)))
    (message "Dumping words from %s to %s...(word 1 of %d)"
	     (dictree--name dict) (buffer-name buffer) dictsize)
    ;; construct dump function
    (let ((dump-func
	   (lambda (word cell)
	     (when (= 99 (mod count 100))
	       (message "Dumping words from %s to %s...(word %d of %d)"
			(dictree--name dict) (buffer-name buffer)
			(1+ count) dictsize))
	     (insert "\"" word "\"")
	     (let (data)
	       (when (setq data (dictree--get-data cell))
		 (insert " " (prin1-to-string data)))
	       (when (setq data (dictree--get-metadata cell))
		 (insert " " (prin1-to-string data)))
	       (insert "\n"))
	     (setq count (1+ count)))))
      ;; map dump function over dictionary
      (if (dictree--lookup-only dict)
	  (maphash dump-func (dictree--lookup-hash dict))
	(tstree-map dump-func (dictree--tstree dict) t)))
    (message "Dumping words from %s to %s...done"
	     (dictree--name dict) (buffer-name buffer)))
  (switch-to-buffer buffer)
)




(defun dictree-dump-words-to-file (dict filename &optional overwrite)
  "Dump words and their associated data
from dictionary DICT to a text file FILENAME, in the same format
as that used by `dictree-populate-from-file'.

Note that if the data does not have a read syntax, the dumped
data can not be used to recreate the dictionary using
`dictree-populate-from-file'."
  
  (interactive (list (read-dict "Dictionary to dump: ")
		     (read-file-name "File to dump to: ")
		     current-prefix-arg))

  (let (buff)
    ;; create temporary buffer and dump words to it
    (setq buff (generate-new-buffer filename))
    (save-window-excursion
      (dictree-dump-words-to-buffer dict buff)
      
      ;; save file, prompting to overwrite if necessary
      (if (and (file-exists-p filename)
	       (not overwrite)
	       (not (y-or-n-p
		     (format "File %s already exists. Overwrite? " filename))))
	  (message "Word dump cancelled")
	(write-file filename))
      (kill-buffer buff)))
)



(defvar dictree-history nil
  "History list for commands that read an existing ditionary name.")


(defun read-dict (prompt &optional default)
  "Read the name of a dictionary with completion, and return it.
Prompt with PROMPT. By default, return DEFAULT."
  (let (dictlist)
    (mapc (lambda (dict)
	    (unless (or (null (dictree--name dict))
			(member (dictree--name dict) dictlist))
	      (push (dictree--name dict) dictlist)))
	  dictree-loaded-list)
    (eval (intern-soft
	   (completing-read prompt dictlist
			    nil t nil 'dictree-history default))))
)



;; Add the dictree-save-modified function to the kill-emacs-hook to save modified
;; dictionaries when exiting emacs
(add-hook 'kill-emacs-hook 'dictree-save-modified)



;;; dict-tree.el ends here
