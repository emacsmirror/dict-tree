
;;; dict-tree.el --- dictionary data structure package


;; Copyright (C) 2004-2008 Toby Cubitt

;; Author: Toby Cubitt <toby-predictive@dr-qubit.org>
;; Version: 0.12
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
;; You create a dictionary using `dictree-create', add entries to it
;; using `dictree-insert', lookup entries using `dictree-lookup', find
;; completions of sequences using `dictree-complete', find completions
;; and sort them in any order you speficy using
;; `dictree-complete-ordered', map over it using `dictree-map' and
;; `dictree-mapcar', save it to a file using `dictree-save' or
;; `dictree-write', and load from file it using
;; `dictree-load'. Various other useful functions are also provided.
;;
;; This package uses the trie package, trie.el.


;;; Change log:
;;
;; Version 0.12
;; * complete rewrite using new trie.el library
;;
;; Version 0.11.1
;; * set and restore value of `byte-compile-disable-print-circle' instead of
;;   let-binding it, to avoid warnings when compiling
;; * added `dictree-goto-line' macro to work around `goto-line' bug
;;
;; Version 0.11
;; * modified `dictree-write' so that, by default, both compiled and uncompiled
;;   versions of dictionaries are created when writing dictionaries to file
;; * fixed slow byte-compilation under Emacs 22
;;
;; Version 0.10.2
;; * very minor changes to text of some messages
;;
;; Version 0.10.1
;; * added optional DICTLIST argument to `read-dict', to allow completion from
;;   a restricted set of dictionaries
;;
;; Version 0.10
;; * finally wrote a `dictree-delete' function!
;;
;; Version 0.9.1
;; * fixed bug in `dictree-dump-words-to-buffer' (thanks to Dan Pomohaci
;;   for reporting it)
;; * replaced "word" with "key" in function arguments and docstrings,
;;   since keys don't have to be words
;; * removed "words" from dump functions' names, added TYPE argument in
;;   line with other functions, and made them non-interactive
;; * added COMPARE-FUNCTION argument to `dictree-create', which defaults
;;   to subtraction as before
;; * `dictree-read-line' reads the keys with `read', and no longer evals
;;   the data as this fails for simple, useful cases (e.g. constant lists)
;;
;; Version 0.9
;; * added meta-dictionary functionality
;; * dictionary data can now be referenced by any sequence type, not just
;;   strings
;; * removed cl dependency
;;
;; Note: version 0.8 dictionaries not compatible with version 0.9 and
;;       above
;;
;; Version 0.8.4
;; * fixed small bug in `read-dict'
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
;; * fixed nasty bug in `dict-map' and `dict-mapcar' caused by dynamic
;;   scoping
;;
;; Version 0.8
;; * changed `dict-map(car)' into functions and made them work with
;;   lookup-only dicts
;; * `dict-insert' now returns the new data value
;; * rewrote cache data structures: data is now wrapped inside a cons
;;   cell, so that cache entries can point to it instead of duplicating
;;   it. This fixes some caching bugs and makes updating cached data when
;;   inserting words much faster
;; * dictionaries (but not lookup-only) can now associate two pieces of
;;   data with each word: normal data, used to rank words returned by
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
;; * dictionaries now set their names and filenames by doing a library
;;   search for themselves when loaded using require
;; * added `read-dict' minibuffer completion function
;; * interactive commands that read a dictionary name now provide
;;   completion
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
;; Note: version 0.1 dictionaries not compatible with version 0.2 and
;;       above!
;;
;; Version 0.1
;; * initial release



;;; Code:

(eval-when-compile (require 'cl))
(require 'trie)
(require 'bytecomp)



;;; ================================================================
;;;            Replacements for CL and Elisp functions

;; copied from cl-extra.el
(defun dictree--subseq (seq start &optional end)
  "Return the subsequence of SEQ from START to END.
If END is omitted, it defaults to the length of the sequence.
If START or END is negative, it counts from the end."
  (if (stringp seq) (substring seq start end)
    (let (len)
      (and end (< end 0) (setq end (+ end (setq len (length seq)))))
      (when (< start 0)
	(setq start (+ start (or len (setq len (length seq))))))
      (cond ((listp seq)
	     (if (> start 0) (setq seq (nthcdr start seq)))
	     (if end
		 (let ((res nil))
		   (while (>= (setq end (1- end)) start)
		     (push (pop seq) res))
		   (nreverse res))
	       (copy-sequence seq)))
	    (t
	     (or end (setq end (or len (length seq))))
	     (let ((res (make-vector (max (- end start) 0) nil))
		   (i 0))
	       (while (< start end)
		 (aset res i (aref seq start))
		 (setq i (1+ i) start (1+ start)))
	       res))))))



;; `goto-line' without messing around with mark and messages
;; Note: this is a bug in simple.el; there's clearly a place for
;;       non-interactive calls to goto-line from Lisp code, and
;;       there's no warning against doing this. Yet goto-line *always*
;;       calls push-mark, which usually *shouldn't* be invoked by
;;       Lisp programs, as its docstring warns.
(defmacro dictree-goto-line (line)
  "Goto line LINE, counting from line 1 at beginning of buffer."
  `(progn
     (goto-char 1)
     (if (eq selective-display t)
	 (re-search-forward "[\n\C-m]" nil 'end (1- ,line))
       (forward-line (1- ,line)))))



;;; ====================================================================
;;;  Internal functions and variables for use in the dictionary package


(defvar dictree-loaded-list nil
  "Stores list of loaded dictionaries.")


(defsubst dictree-p (obj)
  "Return t if OBJ is a dictionary tree, nil otherwise."
  (or (dictree--p obj) (dictree--meta-dict-p obj)))


(defstruct
  (dictree-
   :named
   (:constructor nil)
   (:constructor dictree--create
		 (&optional
		  filename
		  (name (and filename
			     (file-name-sans-extension
			      (file-name-nondirectory filename))))
		  autosave
		  unlisted
		  (comparison-function '<)
		  (insert-function (lambda (a b) a))
		  (rank-function (lambda (a b) (> (cdr a) (cdr b))))
		  (cache-policy 'time)
		  (cache-update-policy 'synchronize)
		  lookup-cache-threshold
		  complete-cache-threshold
		  complete-ranked-cache-threshold
		  key-savefun key-loadfun
		  data-savefun data-loadfun
		  plist-savefun plist-loadfun
		  trie-type
		  &aux
		  (modified nil)
		  (trie (trie-create comparison-function))
		  (insfun (eval (macroexpand
				 `(dictree--wrap-insfun ,insert-function))))
		  (rankfun (eval (macroexpand
				  `(dictree--wrap-rankfun ,rank-function))))
		  (lookup-cache
		   (if lookup-cache-threshold
		       (make-hash-table :test 'equal)
		     nil))
		  (complete-cache
		   (if complete-cache-threshold
		       (make-hash-table :test 'equal)
		     nil))
		  (complete-ranked-cache
		   (if complete-ranked-cache-threshold
		       (make-hash-table :test 'equal)
		     nil))
		  (metadict-list nil)
		  ))
   (:constructor dictree--create-custom
		 (&optional
		  filename
		  (name (and filename
			     (file-name-sans-extension
			      (file-name-nondirectory filename))))
		  autosave
		  unlisted
		  (comparison-function '<)
		  (insert-function (lambda (a b) a))
		  (rank-function (lambda (a b) (> (cdr a) (cdr b))))
		  (cache-policy 'time)
		  (cache-update-policy 'synchronize)
		  lookup-cache-threshold
		  complete-cache-threshold
		  complete-ranked-cache-threshold
		  key-savefun key-loadfun
		  data-savefun data-loadfun
		  plist-savefun plist-loadfun
		  &key
		  createfun insertfun deletefun lookupfun mapfun emptyfun
		  stack-createfun stack-popfun stack-emptyfun
		  &aux
		  (modified nil)
		  (trie (trie-create-custom comparison-function
				     :createfun createfun
				     :insertfun insertfun
				     :deletefun deletefun
				     :lookupfun lookupfun
				     :mapfun mapfun
				     :emptyfun emptyfun
				     :stack-createfun stack-createfun
				     :stack-popfun stack-popfun
				     :stack-emptyfun stack-emptyfun))
		  (insfun (eval (macroexpand
				 `(dictree--wrap-insfun ,insert-function))))
		  (rankfun (eval (macroexpand
				  `(dictree--wrap-rankfun ,rank-function))))
		  (lookup-cache
		   (if lookup-cache-threshold
		       (make-hash-table :test 'equal)
		     nil))
		  (complete-cache
		   (if complete-cache-threshold
		       (make-hash-table :test 'equal)
		     nil))
		  (complete-ranked-cache
		   (if complete-ranked-cache-threshold
		       (make-hash-table :test 'equal)
		     nil))
		  (metadict-list nil)
		  ))
   (:copier nil))
  name filename autosave modified
  comparison-function insert-function insfun rank-function rankfun
  cache-policy cache-update-policy
  lookup-cache lookup-cache-threshold
  complete-cache complete-cache-threshold
  complete-ranked-cache complete-ranked-cache-threshold
  key-savefun key-loadfun
  data-savefun data-loadfun
  plist-savefun plist-loadfun
  trie meta-dict-list)



(defstruct
  (dictree--meta-dict
   :named
   (:constructor nil)
   (:constructor dictree--meta-dict-create
		 (dictionary-list
		  &optional
		  filename
		  (name (file-name-sans-extension
			 (file-name-nondirectory filename)))
		  autosave
		  unlisted
		  (combine-function '+)
		  (cache-policy 'time)
		  (cache-update-policy 'synchronize)
		  lookup-cache-threshold
		  complete-cache-threshold
		  complete-ranked-cache-threshold
		  &aux
		  (dictlist
		   (mapcar
		    (lambda (dic)
		      (cond
		       ((dictree-p dic) dic)
		       ((symbolp dic) (eval dic))
		       (t (error "Invalid object in DICTIONARY-LIST"))))
		    dictionary-list))
		  (combfun (eval (macroexpand
				  `(dictree--wrap-combfun
				    ,combine-function))))
		  ))
   (:copier nil))
  name filename autosave modified
  combine-function combfun
  cache-policy cache-update-policy
  lookup-cache lookup-cache-threshold
  complete-cache complete-cache-threshold
  complete-ranked-cache complete-ranked-cache-threshold
  dictlist meta-dict-list)


(defun dictree--trielist (dict)
  ;; Return a list of all the tries on which DICT is based. If DICT is a
  ;; meta-dict, this recursively descends the hierarchy, gathering all the
  ;; tries from the base dictionaries.
  (let (accumulate)
    (dictree--do-trielist dict)
    accumulate))

(defun dictree--do-trielist (dict)
  (declare (special accumulate))
  (if (dictree-meta-dict-p dict)
      (mapc 'dictree--do-trielist (dictree--meta-dict-dictlist dict))
    (setq accumulate (cons (dictree--trie dict) accumulate))))



(defmacro dictree--cell-create (data &optional meta-data)
  ;; INTERNAL USE ONLY
  ;; wrap the data in a cons cell
  `(cons ,data ,meta-data))

;; get data component from data cons cell
(defmacro dictree--cell-data (cell)  ; INTERNAL USE ONLY
  `(car ,cell))

;; get meta-data component of data cons cell
(defmacro dictree--cell-plist (cell)  ; INTERNAL USE ONLY
  `(cdr ,cell))

(defmacro dictree--wrap-insfun (insfun)  ; INTERNAL USE ONLY
  ;; return wrapped insfun to deal with data wrapping
  `(lambda (new old)
     (setf (dictree--cell-data old)
	   (,insfun (dictree--cell-data new)
		    (dictree--cell-data old)))
     old))

(defmacro dictree--wrap-rankfun (rankfun)  ; INTERNAL USE ONLY
  ;; return wrapped rankfun to deal with data wrapping
  `(lambda (a b)
     (,rankfun (cons (car a) (dictree--cell-data (cdr a)))
	       (cons (car b) (dictree--cell-data (cdr b))))))

(defmacro dictree--wrap-filter (filter)  ; INTERNAL USE ONLY
  ;; return wrapped filter function to deal with data wrapping
  `(lambda (key data) (,filter key (dictree--cell-data data))))

(defmacro dictree--wrap-combfun (combfun)  ; INTERNAL USE ONLY
  `(lambda (cell1 cell2)
     (cons (,combfun (dictree--cell-data cell1)
		     (dictree--cell-data cell2))
	   (append (list (dictree--cell-metadata cell1))
		   (list (dictree--cell-metadata cell2))))))

;; Construct and return a completion cache entry
(defalias 'dictree--cache-create 'cons)  ; INTERNAL USE ONLY

;; Return the completions list for cache entry CACHE
(defalias 'dictree--cache-completions 'car)  ; INTERNAL USE ONLY

;; Return the max number of completions returned for cache entry CACHE
(defalias 'dictree--cache-maxnum 'cdr)  ; INTERNAL USE ONLY

;; Set the completions list for cache entry CACHE
(defalias 'dictree--set-cache-completions 'setcar)  ; INTERNAL USE ONLY

;; Set the completions list for cache entry CACHE
(defalias 'dictree--set-cache-maxnum 'setcdr)  ; INTERNAL USE ONLY



(defun dictree--merge (list1 list2 cmpfun &optional combfun maxnum)
  ;; Destructively merge together sorted lists LIST1 and LIST2 of completions,
  ;; sorting elements according to CMPFUN. For non-null MAXNUM, only the first
  ;; MAXNUM are kept. For non-null COMBFUN, duplicate elements will be merged
  ;; by passing the two elements as arguments to COMBFUN, and using the return
  ;; value as the merged element.
  (or (listp list1) (setq list1 (append list1 nil)))
  (or (listp list2) (setq list2 (append list2 nil)))
  (let (res (i -1))

    ;; build up result list backwards
    (while (and list1 list2 (or (null maxnum) (< (incf i) maxnum)))
      ;; move smaller element to result list
      (if (funcall cmpfun (car list1) (car list2))
	  (push (pop list1) res)
	(if (funcall cmpfun (car list2) (car list1))
	    (push (pop list2) res)
	  ;; if elements are equal, merge them for non-null COMBFUN
	  (if combfun
	      (push (funcall combfun (pop list1) (pop list2))
		    res)
	    ;; otherwise, add both to result list, in order
	    (push (pop list1) res)
	    (push (pop list2) res)))))

    ;; return result if we already have MAXNUM entries
    (if (and maxnum (= i maxnum))
	(nreverse res)
      ;; otherwise, return result plus enough leftover entries to make up
      ;; MAXNUM (only one of list1 or list2 will be non-nil)
      (let (tmp)
	(or (null maxnum)
	    (and (setq tmp (nthcdr (- maxnum i 1) list1))
		 (setcdr tmp nil))
	    (and (setq tmp (nthcdr (- maxnum i 1) list2))
		 (setcdr tmp nil)))
	(nconc (nreverse res) list1 list2)))
    ))


;; (defun dictree--merge-sort (list sortfun &optional combfun)
;;   ;; Destructively sort LIST according to SORTFUN, combining identical
;;   ;; elements using COMBFUN if supplied.
;;   (dictree--do-merge-sort list (/ (length list) 2) sortfun combfun))


;; (defun dictree--do-merge-sort (list1 len sortfun combfun)
;;   ;; Merge sort LIST according to SORTFUN, combining identical elements using
;;   ;; COMBFUN.
;;   (let* ((p (nthcdr (1- len) list1))
;; 	 (list2 (cdr p)))
;;     (setcdr p nil)
;;     (dictree--merge (dictree--do-merge-sort list1 (/ len 2) sortfun combfun)
;; 		    (dictree--do-merge-sort list2 (/ len 2) sortfun combfun)
;; 		    sortfun combfun)))



;;; ================================================================
;;;      The public functions which operate on dictionaries

(defun dictree-create
  (&optional
   name filename autosave unlisted
   comparison-function insert-function rank-function
   cache-policy cache-update-policy
   lookup-cache-threshold
   complete-cache-threshold
   complete-ranked-cache-threshold
   key-savefun key-loadfun
   data-savefun data-loadfun
   plist-savefun plist-loadfun
   trie-type)
  "Create an empty dictionary and return it.

If NAME is supplied, the dictionary is stored in the variable
NAME. Defaults to FILENAME stripped of directory and
extension. (Regardless of the value of NAME, the dictionary will
be stored in the default variable name when it is reloaded from
file.)

FILENAME supplies a directory and file name to use when saving
the dictionary. If the AUTOSAVE flag is non-nil, then the
dictionary will automatically be saved to this file when it is
unloaded or when exiting Emacs.

If UNLISTED is non-nil, the dictionary will not be added to the
list of loaded dictionaries. Note that this disables autosaving.

COMPARE-FUNCTION sets the function used to compare elements of
the keys. It should take two arguments, A and B, both of the type
contained by the sequences used as keys \(e.g. if the keys will
be strings, the function will be passed two characters\). It
should return t if the first is \"less than\" the
second. Defaults to `<'.

INSERT-FUNCTION sets the function used to insert data into the
dictionary. It should take two arguments: the new data, and the
data already in the dictionary, and should return the data to
insert. Defaults to replacing any existing data with the new
data.

RANK-FUNCTION sets the function used to rank the results of
`dictree-complete'. It should take two arguments, each a cons
whose car is a dictree key (a sequence) and whose cdr is the data
associated with that key. It should return non-nil if the first
argument is \"better\" than the second, nil otherwise. It
defaults to \"lexical\" comparison of the keys, ignoring the data
\(which is not very useful, since an unranked `dictree-complete'
query already does this much more efficiently\).

CACHE-POLICY should be a symbol (time or length), which
determines which query operations are cached. The former caches
queries that take longer (in seconds) than the corresponding
CACHE-THRESHOLD value. The latter caches queries on key sequences
that are longer than the corresponding CACHE-THRESHOLD value.

CACHE-UPDATE-POLICY should be a symbol (update or delete), which
determines how the caches are updated when data is inserted or
deleted. The former updates tainted cache entries, which makes
queries faster but insertion and deleteion slower, whereas the
latter deletes any tainted cache entries, which makes queries
slower but insertion and deletion faster.

The CACHE-THRESHOLD settings set the threshold for caching the
corresponding dictionary query (lookup, completion, ranked
completion). The meaning of these values depends on the setting
of CACHE-POLICY (see above).

All CACHE-THRESHOLD's default to nil. The values nil and t are
special. If a CACHE-THRESHOLD is set to nil, no caching is done
for that type of query. If it is t, everything is cached for that
type of query \(similar behaviour can be obtained by setting the
CACHE-THRESHOLD to 0, but it is better to use t\).

KEY-SAVEFUN, DATA-SAVEFUN and PLIST-SAVEFUN are functions used to
convert keys, data and property lists into lisp objects that have
a valid read syntax, for writing to file. DATA-SAVEFUN and
PLIST-SAVEFUN are used when saving the dictionary (see
`dictree-save' and `dictree-write'), and all three functions are
used when dumping the contents of the dictionary \(see
`dictree-dump-to-buffer' and `dictree-dump-to-file'\).
KEY-SAVEFUN, DATA-SAVEFUN and PLIST-SAVEFUN should each accept
one argument: a key, data or property list from DICT,
respectively. They should return a lisp object which has a valid
read syntax. When defining these functions, be careful not to
accidentally modify the lisp object in the dictionary; usually,
you will need to make a copy before converting it.

KEY-LOADFUN, DATA-LOADFUN and PLIST-LOADFUN are used to convert
keys, data and property lists back again when loading a
dictionary (only DATA-LOADFUN and PLIST-LOADFUN, see
`dictree-save' and `dictree-write') or populating it from a
file (all three, see `dictree-populate-from-file'). They should
accept one argument: a lisp object of the type produced by the
corresponding SAVEFUN, and return a lisp object to use in the
loaded dictionary.

TRIE-TYPE sets the type of trie to use as the underlying data
structure. See `trie-create' for details."

  ;; sadly, passing null values over-rides the defaults in the defstruct
  ;; dictree--create, so we have to explicitly set the defaults again here
  (or name (setq name (and filename (file-name-sans-extension
				     (file-name-nondirectory filename)))))
  (or comparison-function (setq comparison-function '<))
  (or insert-function (setq insert-function (lambda (a b) a)))
  (or rank-function (setq rank-function (lambda (a b) (> (cdr a) (cdr b)))))
  (or cache-policy (setq cache-policy 'time))
  (or cache-update-policy (setq cache-update-policy 'synchronize))

  (let ((dict
	 (dictree--create
	  filename name autosave unlisted
	  comparison-function insert-function rank-function
	  cache-policy cache-update-policy
	  lookup-cache-threshold
	  complete-cache-threshold
	  complete-ranked-cache-threshold
	  key-savefun key-loadfun
	  data-savefun data-loadfun
	  plist-savefun plist-loadfun
	  trie-type)))
    ;; store dictionary in variable NAME
    (when name (set name dict))
    ;; add it to loaded dictionary list, unless it's unlisted
    (unless unlisted
      (push dict dictree-loaded-list)
      (provide name))
    dict))



(defun dictree-create-custom
  (&optional
   name filename autosave unlisted
   comparison-function insert-function rank-function
   cache-policy cache-update-policy
   lookup-cache-threshold
   complete-cache-threshold
   complete-ranked-cache-threshold
   key-savefun key-loadfun
   data-savefun data-loadfun
   plist-savefun plist-loadfun
   createfun insertfun deletefun lookupfun mapfun emptyfun
   stack-createfun stack-popfun stack-emptyfun)
  "Create an empty dictionary and return it.

If NAME is supplied, the dictionary is stored in the variable
NAME. Defaults to FILENAME stripped of directory and
extension. (Regardless of the value of NAME, the dictionary will
be stored in the default variable name when it is reloaded from
file.)

FILENAME supplies a directory and file name to use when saving
the dictionary. If the AUTOSAVE flag is non-nil, then the
dictionary will automatically be saved to this file when it is
unloaded or when exiting Emacs.

If UNLISTED is non-nil, the dictionary will not be added to the
list of loaded dictionaries. Note that this disables autosaving.

COMPARE-FUNCTION sets the function used to compare elements of
the keys. It should take two arguments, A and B, both of the type
contained by the sequences used as keys \(e.g. if the keys will
be strings, the function will be passed two characters\). It
should return t if the first is \"less than\" the
second. Defaults to `<'.

INSERT-FUNCTION sets the function used to insert data into the
dictionary. It should take two arguments: the new data, and the
data already in the dictionary, and should return the data to
insert. Defaults to replacing any existing data with the new
data.

RANK-FUNCTION sets the function used to rank the results of
`dictree-complete'. It should take two arguments, each a cons
whose car is a dictree key (a sequence) and whose cdr is the data
associated with that key. It should return non-nil if the first
argument is \"better\" than the second, nil otherwise. It
defaults to \"lexical\" comparison of the keys, ignoring the data
\(which is not very useful, since the `dictree-complete' function
already does this much more efficiently\).

CACHE-POLICY should be a symbol (time or length), which
determines which query operations are cached. The former caches
queries that take longer (in seconds) than the corresponding
CACHE-THRESHOLD value. The latter caches queries on key sequences that
are longer than the corresponding CACHE-THRESHOLD value.

CACHE-UPDATE-POLICY should be a symbol (update or delete), which
determines how the caches are updated when data is inserted or
deleted. The former updates tainted cache entries, which makes
queries faster but insertion and deleteion slower, whereas the
latter deletes any tainted cache entries, which makes queries
slower but insertion and deletion faster.

The CACHE-THRESHOLD settings set the threshold for caching the
corresponding dictionary query (lookup, completion, ranked
completion). The meaning of these values depends on the setting
of CACHE-POLICY (see above).

All CACHE-THRESHOLD's default to nil. The values nil and t are
special. If a CACHE-THRESHOLD is set to nil, no caching is done for
that type of query. If it is t, everything is cached for that
type of query \(similar behaviour can be obtained by setting the
CACHE-THRESHOLD to 0, but it is better to use t\).

KEY-SAVEFUN, DATA-SAVEFUN and PLIST-SAVEFUN are functions used to
convert keys, data and property lists into lisp objects that have
a valid read syntax, for writing to file. DATA-SAVEFUN and
PLIST-SAVEFUN are used when saving the dictionary (see
`dictree-save' and `dictree-write'), and all three functions are
used when dumping the contents of the dictionary \(see
`dictree-dump-to-buffer' and `dictree-dump-to-file'\).
KEY-SAVEFUN, DATA-SAVEFUN and PLIST-SAVEFUN should each accept
one argument: a key, data or property list from DICT,
respectively. They should return a lisp object which has a valid
read syntax. When defining these functions, be careful not to
accidentally modify the lisp object in the dictionary; usually,
you will need to make a copy before converting it.

KEY-LOADFUN, DATA-LOADFUN and PLIST-LOADFUN are used to convert
keys, data and property lists back again when loading a
dictionary (only DATA-LOADFUN and PLIST-LOADFUN, see
`dictree-save' and `dictree-write') or populating it from a
file (all three, see `dictree-populate-from-file'). They should
accept one argument: a lisp object of the type produced by the
corresponding SAVEFUN, and return a lisp object to use in the
loaded dictionary.

The remaining arguments determine the type of trie to use as the
underlying data structure. See `trie-create' for details."

  ;; sadly, passing null values over-rides the defaults in the defstruct
  ;; dictree--create, so we have to explicitly set the defaults again here
  (or name (setq name (and filename (file-name-sans-extension
				     (file-name-nondirectory filename)))))
  (or comparison-function (setq comparison-function '<))
  (or insert-function (setq insert-function (lambda (a b) a)))
  (or rank-function (setq rank-function (lambda (a b) (< (cdr a) (cdr b)))))
  (or cache-policy (setq cache-policy 'time))
  (or cache-update-policy (setq cache-update-policy 'synchronize))

  (let ((dict
	 (dictree--create-custom
	  filename name autosave unlisted
	  comparison-function insert-function rank-function
	  cache-policy cache-update-policy
	  lookup-cache-threshold
	  complete-cache-threshold
	  complete-ranked-cache-threshold
	  key-savefun key-loadfun
	  data-savefun data-loadfun
	  plist-savefun plist-loadfun
	  :createfun createfun
	  :insertfun insertfun
	  :deletefun deletefun
	  :lookupfun lookupfun
	  :mapfun mapfun
	  :emptyfun emptyfun
	  :stack-createfun stack-createfun
	  :stack-popfun stack-popfun
	  :stack-emptyfun stack-emptyfun)))
    ;; store dictionary in variable NAME
    (when name (set name dict))
    ;; add it to loaded dictionary list, unless it's unlisted
    (unless unlisted
      (push dict dictree-loaded-list)
      (provide name))
    dict))



(defun dictree-meta-dict-create
  (dictionary-list
   &optional
   name filename autosave unlisted
   combine-function
   cache-policy cache-update-policy
   lookup-cache-threshold
   complete-cache-threshold
   complete-ranked-cache-threshold)
  "Create a meta-dictionary based on the list of dictionaries
in DICTIONARY-LIST.

COMBINE-FUNCTION is used to combine data from different
dictionaries. It is passed two pieces of data, each an
association of the same key, but in different dictionaries. It
should return a combined data.

The other arguments are as for `dictree-create'."

  ;; sadly, passing null values over-rides the defaults in the defstruct
  ;; `dictree--create', so we have to explicitly set the defaults again here
  (or name (setq name (and filename (file-name-sans-extension
				     (file-name-nondirectory filename)))))
  (or combine-function (setq combine-function '+))
  (or cache-policy (setq cache-policy 'time))
  (or cache-update-policy (setq cache-update-policy 'synchronize))

  (let ((dict
	 (dictree--meta-dict-create
	  dictionary-list filename name autosave unlisted
	  combine-function
	  cache-policy cache-update-policy
	  lookup-cache-threshold
	  complete-cache-threshold
	  complete-ranked-cache-threshold)
	 ))
    ;; store dictionary in variable NAME
    (when name (set name dict))
    ;; add it to loaded dictionary list, unless it's unlisted
    (unless unlisted
      (push dict dictree-loaded-list)
      (provide name))
    ;; update meta-dict-list cells of constituent dictionaries
    (mapc
     (lambda (dic)
       (if (symbolp dic) (setq dic (eval dic)))
       (setf (dictree--meta-dict-list dic)
	     (cons dict (dictree--meta-dict-list dic))))
     dictionary-list)
    dict))


(defalias 'dictree-meta-dict-p 'dictree--meta-dict-p
  "Return t if argument is a meta-dictionary, nil otherwise.")

(defun dictree-empty-p (dict)
  "Return t if the dictionary DICT is empty, nil otherwise."
  (if (dictree--meta-dict-p dict)
      (catch 'nonempty
	(mapc (lambda (dic)
		(if (not (dictree-empty-p dic)) (throw 'nonempty t)))
	      (dictree--meta-dict-dictlist dict)))
    (trie-empty (dictree--trie dict))))

(defsubst dictree-autosave (dict)
  "Return dictionary's autosave flag."
  (if (dictree--meta-dict-p dict)
      (dictree--meta-dict-autosave dict)
    (dictree--autosave dict)))

(defsetf dictree-autosave (dict) (val)
  ;; setf method for dictionary autosave flag
  `(if (dictree--meta-dict-p ,dict)
       (setf (dictree--meta-dict-autosave ,dict) ,val)
     (setf (dictree--autosave ,dict) ,val)))

(defsubst dictree-modified (dict)
  "Return dictionary's modified flag."
  (if (dictree--meta-dict-p dict)
      (dictree--meta-dict-modified dict)
    (dictree--modified dict)))

(defsetf dictree-modified (dict) (val)
  ;; setf method for dictionary modified flag
  `(if (dictree--meta-dict-p ,dict)
       (setf (dictree--meta-dict-modified ,dict) ,val)
     (setf (dictree--modified ,dict) ,val)))

(defsubst dictree-name (dict)
  "Return dictionary DICT's name."
  (if (dictree--meta-dict-p dict)
      (dictree--meta-dict-name dict)
    (dictree--name dict)))

(defsetf dictree-name (dict) (name)
  ;; setf method for dictionary name
  `(if (dictree--meta-dict-p ,dict)
       (setf (dictree--meta-dict-name ,dict) ,name)
    (setf (dictree--name ,dict) ,name)))

(defun dictree-filename (dict)
  "Return dictionary DICT's associated file name."
  (if (dictree--meta-dict-p dict)
      (dictree--meta-dict-filename dict)
    (dictree--filename dict)))

(defsetf dictree-filename (dict) (filename)
  ;; setf method for dictionary filename
  `(if (dictree--meta-dict-p ,dict)
       (setf (dictree--meta-dict-filename ,dict) ,filename)
     (setf (dictree--filename ,dict) ,filename)))

(defun dictree-comparison-function (dict)
  "Return dictionary DICT's comparison function."
  (if (dictree--meta-dict-p dict)
      (dictree-comparison-function (car (dictree--meta-dict-dictlist dict)))
    (dictree--comparison-function dict)))

(defalias 'dictree-insert-function 'dictree--insert-function
  "Return the insertion function for dictionary DICT.")

(defun dictree-rank-function (dict)
  "Return the rank function for dictionary DICT"
  (if (dictree--meta-dict-p dict)
      (dictree-rank-function (car (dictree--meta-dict-dictlist dict)))
    (dictree--rank-function dict)))

(defun dictree-rankfun (dict)
  ;; Return the rank function for dictionary DICT
  (if (dictree--meta-dict-p dict)
      (dictree-rankfun (car (dictree--meta-dict-dictlist dict)))
    (dictree--rankfun dict)))

(defalias 'dictree-meta-dict-combine-function
  'dictree--meta-dict-combine-function
  "Return the combine function for meta-dictionary DICT.")

(defalias 'dictree-meta-dict-dictlist
  'dictree--meta-dict-dictlist
  "Return the list of constituent dictionaries for meta-dictionary DICT.")

(defun dictree-lookup-cache-threshold (dict)
  "Return the lookup cache threshold for dictionary DICT."
  (if (dictree--meta-dict-p dict)
      (dictree--meta-dict-lookup-cache-threshold dict)
    (dictree--lookup-cache-threshold dict)))

(defsetf dictree-lookup-cache-threshold (dict) (param)
  ;; setf method for lookup cache threshold
  `(if (dictree--meta-dict-p ,dict)
       (setf (dictree--meta-dict-lookup-cache-threshold ,dict) ,param)
     (setf (dictree--lookup-cache-threshold ,dict) ,param)))

(defun dictree-lookup-cache (dict)
  ;; Return the lookup cache for dictionary DICT.
  (if (dictree--meta-dict-p dict)
      (dictree--meta-dict-lookup-cache dict)
    (dictree--lookup-cache dict)))

(defun dictree-complete-cache-threshold (dict)
  "Return the completion cache threshold for dictionary DICT."
  (if (dictree--meta-dict-p dict)
      (dictree--meta-dict-complete-cache-threshold dict)
    (dictree--complete-cache-threshold dict)))

(defsetf dictree-complete-cache-threshold (dict) (param)
  ;; setf method for completion cache threshold
  `(if (dictree--meta-dict-p ,dict)
       (setf (dictree--meta-dict-complete-cache-threshold ,dict) ,param)
     (setf (dictree--complete-cache-threshold ,dict) ,param)))

(defun dictree-complete-cache (dict)
  ;; Return the completion cache for dictionary DICT.
  (if (dictree--meta-dict-p dict)
      (dictree--meta-dict-complete-cache dict)
    (dictree--complete-cache dict)))

(defun dictree-complete-ranked-cache-threshold (dict)
  "Return the ranked completion cache threshold for dictionary DICT."
  (if (dictree--meta-dict-p dict)
      (dictree--meta-dict-complete-ranked-cache-threshold dict)
    (dictree--complete-ranked-cache-threshold dict)))

(defsetf dictree-complete-ranked-cache-threshold (dict) (param)
  ;; setf method for ranked completion cache threshold
  `(if (dictree--meta-dict-p ,dict)
       (setf (dictree--meta-dict-complete-ranked-cache-threshold ,dict) ,param)
     (setf (dictree--complete-ranked-cache-threshold ,dict) ,param)))

(defun dictree-complete-ranked-cache (dict)
  ;; Return the ranked completion cache for dictionary DICT.
  (if (dictree--meta-dict-p dict)
      (dictree--meta-dict-complete-ranked-cache dict)
    (dictree--complete-ranked-cache dict)))


(defmacro dictree--query-triefun (query-type)
  ;; Return trie query function corresponding to QUERY-TYPE
  `(intern (concat "trie-" (symbol-name ,query-type))))

(defmacro dictree--query-stackfun (query-type)
  ;; Return dictree stack creation function corresponding to QUERY-TYPE
  `(intern (concat "dictree-" (symbol-name ,query-type) "-stack")))

(defmacro dictree--query-cacheparam (query-type dict ranked)
  ;; Return DICT's QUERY-TYPE cache threshold.
  `(if ,ranked
       (funcall (intern (concat "dictree-" (symbol-name ,query-type)
				"-ranked-cache-threshold"))
		,dict)
     (funcall (intern (concat "dictree-" (symbol-name ,query-type)
			      "-cache-threshold"))
	      ,dict)))

(defmacro dictree--query-cache (query-type dict ranked)
  ;; Return DICT's QUERY-TYPE cache.
  `(if ,ranked
       (funcall
	(intern (concat "dictree-" (symbol-name ,query-type) "-ranked-cache"))
	,dict)
     (funcall
      (intern (concat "dictree-" (symbol-name ,query-type) "-cache"))
      ,dict)))





;; ----------------------------------------------------------------
;;                  Inserting and deleting data

(defun dictree-insert (dict key &optional data insert-function)
  "Insert KEY and DATA into dictionary DICT.
If KEY does not already exist, this creates it. How the data is
inserted depends on the dictionary's insertion function \(see
`dictree-create'\).

The optional INSERT-FUNCTION over-rides the dictionary's own
insertion function. If KEY already exists in DICT,
INSERT-FUNCTION is called with two arguments: the data DATA, and
the data associated with KEY in the dictionary. Its return value
becomes the new association for KEY."

  ;; if dictionary is a meta-dictionary, insert key into all the
  ;; dictionaries it's based on
  (if (dictree--meta-dict-p dict)
      (mapc (lambda (dic)
	      (dictree-insert dic key data insert-function))
	    (dictree--meta-dict-dictlist dict))

    ;; otherwise...
    (let (newdata)
      ;; set the dictionary's modified flag
      (setf (dictree-modified dict) t)
      ;; insert key in dictionary's ternary search tree
      (setq newdata
	    (trie-insert
	     (dictree--trie dict) key (dictree--cell-create data)
	     (or (and insert-function
		      (eval (macroexpand
			     `(dictree--wrap-insfun ,insert-function))))
		 (dictree--insfun dict))))
      ;; update dictionary's caches
      (dictree-update-cache dict key newdata)
      ;; update cache's of any meta-dictionaries based on dict
      (mapc (lambda (dic) (dictree-update-cache dic key newdata))
	    (dictree--meta-dict-list dict))

      ;; return the new data
      (dictree--cell-data newdata))))



(defun dictree-delete (dict key &optional test)
  "Delete KEY from DICT.
Returns non-nil if KEY was deleted, nil if KEY was not in DICT.

If TEST is supplied, it should be a function that accepts three
arguments: the key being deleted, its associated data, and its
associated property list. The key will then only be deleted if
TEST returns non-nil."

  (let ((dictree--delete-test test)
	deleted del)
    (cond
     ;; if DICT is a meta-dictionary, delete KEY from all dictionaries
     ;; it's based on
     ((dictree--meta-dict-p dict)
      (dolist (dic (dictree--meta-dict-dictlist dict))
	(when (setq del (dictree-delete dic key))
	  (setq deleted (cons del deleted))))
      (setf (dictree-modified dict) (and deleted t))
      (setq deleted (nreverse deleted)))

     ;; otherwise...
     (t
      (setq deleted
	    (trie-delete (dictree--trie dict) key
			 (when dictree--delete-test
			   (lambda (k cell)
			     (funcall dictree--delete-test
				      k (dictree--cell-data cell)
				      (dictree--cell-plist cell))))))
      ;; if key was deleted, have to update the caches
      (when deleted
	(dictree-update-cache dict key nil t)
	(setf (dictree-modified dict) t)
	;; update cache's of any meta-dictionaries based on DICT
	(mapc (lambda (dic)
		(dictree-update-cache dic key nil t))
	      (dictree--meta-dict-list dict)))))

    ;; return deleted key/data pair
    (when deleted
      (cons (car deleted) (dictree--cell-data (cdr deleted))))))



;; ----------------------------------------------------------------
;;                     Cache updating

(defun dictree-update-cache (dict key newdata &optional deleted)
  "Synchronise dictionary DICT's caches,
given that the data associated with KEY has been changed to
NEWDATA, or KEY has been deleted if DELETED is non-nil (NEWDATA
is ignored in that case)."

  (let (prefix cache entry completions cmpl maxnum)

    ;; synchronise the lookup cache if dict is a meta-dictionary,
    ;; since it's not done automatically
    (when (and (dictree--meta-dict-p dict)
	       (dictree--lookup-cache-threshold dict)
	       (gethash key (dictree--lookup-cache dict)))
      (if deleted
	  (remhash key (dictree--lookup-cache dict))
	(puthash key newdata (dictree--lookup-cache dict))))


    ;; synchronize the completion cache, if it exists
    (when (dictree-complete-cache-threshold dict)
      ;; have to check every possible prefix that could be cached!
      (dotimes (i (1+ (length key)))
	(setq prefix (dictree--subseq key 0 i))
	(dolist (reverse '(nil t))
	  (when (setq cache (gethash (cons prefix reverse)
				     (dictree-complete-cache dict)))
	    (setq completions (dictree--cache-completions cache))
	    (setq maxnum (dictree--cache-maxnum cache))
	    (setq cmpl (assoc key completions))
	    (cond
	     ;; if key was deleted and was in cached result, remove cache
	     ;; entry and re-run the same completion to update the cache
	     ((and deleted cmpl)
	      (remhash (cons prefix reverse) (dictree-complete-cache dict))
	      (dictree-complete dict prefix maxnum reverse))
	     ;; if key was modified and was not in cached result, merge it
	     ;; into the completion list, retaining only the first maxnum
	     ((and (not deleted) (not cmpl))
	      (dictree--set-cache-completions
	       cache
	       (dictree--merge
		(list (cons key newdata)) completions
		`(lambda (a b)
		   (,(eval (macroexpand
			   `(trie-construct-sortfun
			     ,(dictree-comparison-function dict))))
		    (car a) (car b)))
		(when (dictree--meta-dict-p dict)
		  (dictree--meta-dict-combfun dict))
		maxnum)))
	     ;; if key was modified and was in the cached result, update the
	     ;; associated data if dict is a meta-dictionary (this is done
	     ;; automatically for a normal dict)
	     ((and (not deleted) cmpl (dictree--meta-dict-p dict))
	      (setcdr cmpl newdata))
	     ;; the final combination, deleted and not in cached result,
	     ;; requires no action
	     )))))


    ;; synchronize the ranked completion cache, if it exists
    (when (dictree--complete-ranked-cache-threshold dict)
      ;; have to check every possible prefix that could be cached!
      (dotimes (i (1+ (length key)))
	(setq prefix (dictree--subseq key 0 i))
	(dolist (reverse '(nil t))
	  (when (setq cache (gethash (cons prefix reverse)
				     (dictree-complete-ranked-cache dict)))
	    (setq completions (dictree--cache-completions cache))
	    (setq maxnum (dictree--cache-maxnum cache))
	    (setq cmpl (assoc key completions))
	    (cond
	     ;; if key was deleted and was in cached result, remove cache
	     ;; entry and re-run the same query to update the cache
	     ((and deleted cmpl)
	      (remhash (cons prefix reverse)
		       (dictree-complete-ranked-cache dict))
	      (dictree-complete dict prefix maxnum reverse nil nil 'ranked))
	     ;; if key was modified and was not in cached result, merge it
	     ;; into the completion list, retaining only the first maxnum
	     ((and (not deleted) (not cmpl))
	      (dictree--set-cache-completions
	       cache
	       (dictree--merge
		(list (cons key newdata)) completions
		(dictree-rankfun dict)
		(when (dictree--meta-dict-p dict)
		  (dictree--meta-dict-combfun dict))
		maxnum)))
	     ;; if key was modified and was in the cached result, update the
	     ;; associated data if dict is a meta-dictionary (this is done
	     ;; automatically for a normal dict), re-sort, and if key is now
	     ;; at end of list re-run the same query to update the cache
	     ((and (not deleted) cmpl)
	      (when (dictree--meta-dict-p dict) (setcdr cmpl newdata))
	      (dictree--set-cache-completions
	       cache (sort completions (dictree-rankfun dict)))
	      (when (equal key (car (last completions)))
		(remhash (cons prefix reverse)
			 (dictree-complete-ranked-cache dict))
		(dictree-complete dict prefix maxnum reverse nil nil 'ranked)))
	     ;; the final combination, deleted and not in cached result,
	     ;; requires no action
	     )))))
    ))



;; ----------------------------------------------------------------
;;                        Retrieving data

(defun dictree-lookup (dict key &optional nilflag)
  "Return the data associated with KEY in dictionary DICT,
or nil if KEY is not in the dictionary.

Optional argument NILFLAG specifies a value to return instead of
nil if KEY does not exist in TREE. This allows a non-existent KEY
to be distinguished from an element with a null association. (See
also `dictree-member-p' for testing existence alone.)"
  (let ((data (dictree--lookup dict key nilflag)))
    (unless (eq data nilflag)
      (dictree--cell-data data))))


(defalias 'dictree-member 'dictree-lookup)


(defun dictree-member-p (dict key)
  "Return t if KEY exists in DICT, nil otherwise."
  (let ((flag '(nil)))
    (not (eq flag (dictree-member dict key flag)))))



(defun dictree--lookup (dict key nilflag)
  ;; Return association of KEY in DICT, or NILFLAG if KEY does not exist. Does
  ;; not do any data/meta-data unwrapping

  (let* ((flag '(nil))
	 (data flag)
	 time)
    ;; if KEY is in the cache, then we're done
    (unless (and (dictree-lookup-cache dict)
		 (setq data (gethash key (dictree--lookup-cache dict))))

      ;; otherwise, we have to look in the dictionary itself...
      (cond
       ;; if DICT is a meta-dict, look in its constituent dictionaries
       ((dictree--meta-dict-p dict)
	(let (newdata (newflag '(nil)))
	  ;; time the lookup for caching
	  (setq time (float-time))
	  ;; look in each constituent dictionary in turn
	  (dolist (dic (dictree--meta-dict-dictlist dict))
	    (setq newdata (dictree--lookup dic key newflag))
	    ;; skip dictionary if it doesn't contain KEY
	    (unless (eq newdata newflag)
	      ;; if we haven't found KEY before, we have now!
	      (if (eq data flag)
		  (setq data newdata)
		;; otherwise, combine the previous data with the new data
		(setq data (funcall (dictree--meta-dict-combfun dict)
				    data newdata)))))
	  (setq time (- (float-time) time))))

       ;; otherwise, DICT is a normal dictionary, so look in it's trie
       (t
	;; time the lookup for caching
	(setq time (float-time))
	(setq data (trie-member (dictree--trie dict) key flag))
	(setq time (- (float-time) time))))

      ;; if lookup found something, but was slower than lookup cache-threshold,
      ;; cache the result
      (when (and (not (eq data flag))
		 (dictree-lookup-cache-threshold dict)
		 (or (eq (dictree-lookup-cache-threshold dict) t)
		     (> time (dictree-lookup-cache-threshold dict))))
	(setf (dictree-modified dict) t)
	(puthash key data (dictree-lookup-cache dict))))

    ;; return the desired data
    (if (eq data flag) nilflag data)))



;; ----------------------------------------------------------------
;;                 Getting and setting meta-data

(defun dictree-put-property (dict key property value)
  "Set PROPERTY for KEY in dictionary DICT.
PROPERTY should be a symbol. Returns VALUE if successful, nil if
KEY was not found in DICT.

Note that if DICT is a meta-dictionary, then this will set KEY's
PROPERTY to VALUE in *all* its constituent dictionaries.

Unlike the data associated with a key (cf. `dictree-insert'),
properties are not included in the results of queries on the
dictionary \(`dictree-lookup', `dictree-complete',
`dictree-complete-ordered'\), nor do they affect the outcome of
any of the queries. They merely serves to tag a key with some
additional information, and can only be retrieved using
`dictree-get-property'."

  ;; sort out arguments
  (when (symbolp dict) (setq dict (eval dict)))
  (cond
   ;; set PROPERTY for KEY in all constituent dicts of a meta-dict
   ((dictree--meta-dict-p dict)
    (warn "Setting %s property for key %s in all constituent dictionaries\
 of meta-dicttionary %s" property key (dictree-name dict))
    (setf (dictree-modified dict) t)
    (let (dictree--put-property-ret)
      (mapc (lambda (dic k p v)
	      (setq dictree--put-property-ret
		    (or dictree--put-property-ret
			(dictree-put-property dic k p v))))
	    (dictree--meta-dict-dictlist dict))
      ;; return VALUE if KEY was found in at least one constituent dict
      dictree--put-property-ret))
   (t  ;; set PROPERTY for KEY in normal dict
    (let ((cell (trie-member (dictree--trie dict) key)))
      (when cell
	(setf (dictree-modified dict) t)
	(setf (dictree--cell-plist cell)
	      (plist-put (dictree--cell-plist cell) property value))
	value)))  ; return VALUE
   ))



(defun dictree-delete-property (dict key property)
  "Delete PROPERTY from KEY in dictionary DICT.
Returns the new property list for KEY, with PROPERTY deleted.

Setting PROPERTY to nil using `dictree-put-property' is not quite
the same thing as deleting it, since null property values can
still be detected by supplying the optional argument to
`dictree-get-propery' (which see).

Note that if DICT is a meta-dictionary, then this will delete
KEY's PROPERTY in *all* its constituent dictionaries."
  ;; sort out arguments
  (when (symbolp dict) (setq dict (eval dict)))
  (cond
   ;; delete PROPERTY from KEY in all constituent dicts of a meta-dict
   ((dictree--meta-dict-p dict)
    (warn "Deleting %s property from key %s in all constituent dictionaries\
 of meta-dicttionary %s" property key (dictree-name dict))
    (setf (dictree-modified dict) t)
    (mapcar (lambda (dic k p) (dictree-delete-property dic k p))
	    (dictree--meta-dict-dictlist dict)))
   (t  ;; delete PROPERTY from KEY in normal dict
    (let* ((cell (trie-member (dictree--trie dict) key))
	   plist tail tail)
      (when (and cell
		 (setq tail
		       (plist-member (setq plist (dictree--cell-plist cell))
				     property)))
	(setf (dictree-modified dict) t)
	;; delete property and value from plist
	(setcdr tail (cddr tail))
	(setq plist (delq property plist))
	(setf (dictree--cell-plist cell) plist))))
   ))



(defun dictree-get-property (dict key property &optional nilflag)
  "Get the value of PROPERTY for KEY in dictionary DICT,
or return nil if KEY is not in the dictionary.

Optional argument NILFLAG specifies a value to return instead of
nil if KEY does not exist in TREE. This allows a non-existent KEY
to be distinguished from a key for which PROPERTY is not
set. (See also `dictree-member-p' for testing existence alone.)"
  (let ((cell (dictree--lookup dict key nilflag)))
    (unless (eq cell nilflag)
      (plist-get (dictree--cell-plist cell) property))))




;; ----------------------------------------------------------------
;;                        Mapping functions

(defun dictree-mapc (function dict &optional type reverse)
  "Apply FUNCTION to all entries in dictionary DICT,
for side-effects only.

FUNCTION will be passed two arguments: a key of type
TYPE ('string, 'vector, or 'list, defaulting to 'vector) from the
dictionary, and the data associated with that key. The dictionary
entries will be traversed in \"lexical\" order, i.e. the order
defined by the dictionary's comparison function (cf.
`dictree-create').

If TYPE is 'string, it must be possible to apply the function
`string' to the elements of sequences stored in DICT.

FUNCTION is applied in ascending order, or descending order if
REVERSE is non-nil."

  ;; "rename" FUNCTION to something hopefully unique, to help avoid nasty
  ;; dynamical scoping bugs
  (let ((dictree-mapc--function function))
    (dictree--mapc
     (lambda (key data plist)
       (funcall dictree-mapc--function key data))
     dict type reverse)))


(defun dictree--mapc (function dict &optional type reverse)
  ;; Like `dictree-mapc', but FUNCTION is passed three arguments: the key, the
  ;; data, and the property list, instead of just key and data.

  ;; "rename" FUNCTION to something hopefully unique, to help avoid nasty
  ;; dynamical scoping bugs
  (let ((dictree--mapc--function function))
    ;; for a normal dictionary, map the function over its trie
    (if (not (dictree--meta-dict-p dict))
	(trie-mapc
	 (lambda (key cell)
	   (funcall dictree--mapc--function
		    key
		    (dictree--cell-data cell)
		    (dictree--cell-plist cell)))
	 (dictree--trie dict)
	 type reverse)
      ;; for a meta-dict, use a dictree-stack
      (let ((stack (dictree-stack dict))
	    entry)
	(while (setq entry (dictree--stack-pop stack))
	  (funcall dictree--mapc--function
		   (car entry)
		   (dictree--cell-data (cdr entry))
		   (dictree--cell-plist (cdr entry)))))
      )))


(defun dictree-mapf (function combinator dict &optional type reverse)
  "Apply FUNCTION to all entries in dictionary DICT,
and combine the results using COMBINATOR.

FUNCTION should take two arguments: a key sequence from the
dictionary and its associated data.

Optional argument TYPE (one of the symbols vector, lisp or
string; defaults to vector) sets the type of sequence passed to
FUNCTION. If TYPE is 'string, it must be possible to apply the
function `string' to the individual elements of key sequences
stored in DICT.

The FUNCTION will be applied and the results combined in
asscending \"lexical\" order (i.e. the order defined by the
dictionary's comparison function; cf. `dictree-create'), or
descending order if REVERSE is non-nil."

  ;; "rename" functions to something hopefully unique, to help avoid nasty
  ;; dynamical scoping bugs
  (let ((dictree-mapf--function function)
	(dictree-mapf--combinator combinator))

    ;; for a normal dictionary, map the function over its trie
    (if (not (dictree--meta-dict-p dict))
	(trie-mapf
	 `(lambda (key data)
	    (,dictree-mapf--function key (dictree--cell-data data)))
	 dictree-mapf--combinator (dictree--trie dict) type reverse)

      ;; for a meta-dict, use a dictree-stack
      (let ((dictree-mapf--stack (dictree-stack dict))
	    dictree-mapf--entry
	    dictree-mapf--accumulate)
	(while (setq dictree-mapf--entry
		     (dictree-stack-pop dictree-mapf--stack))
	  (setq dictree-mapf--accumulate
		(funcall dictree-mapf--combinator
			 (funcall dictree-mapf--function
				  (car dictree-mapf--entry)
				  (cdr dictree-mapf--entry))
			 dictree-mapf--accumulate)))
	dictree-mapf--accumulate))))



(defun dictree-mapcar (function dict &optional type reverse)
  "Apply FUNCTION to all entries in dictionary DICT,
and make a list of the results.

FUNCTION should take two arguments: a key sequence from the
dictionary and its associated data.

Optional argument TYPE (one of the symbols vector, lisp or
string; defaults to vector) sets the type of sequence passed to
FUNCTION. If TYPE is 'string, it must be possible to apply the
function `string' to the individual elements of key sequences
stored in DICT.

The FUNCTION will be applied and the results combined in
asscending \"lexical\" order \(i.e. the order defined by the
dictionary's comparison function; cf. `dictree-create'\), or
descending order if REVERSE is non-nil.

Note that if you don't care about the order in which FUNCTION is
applied, just that the resulting list is in the correct order,
then

  (trie-mapf function 'cons trie type (not reverse))

is more efficient."
  (nreverse (dictree-mapf function 'cons dict type)))



(defun dictree-size (dict)
  "Return the number of entries in dictionary DICT."
  (interactive (list (read-dict "Dictionary: ")))
  (let ((count 0))
    (dictree-mapc (lambda (&rest dummy) (incf count)) dict)
    (when (interactive-p)
      (message "Dictionary %s contains %d entries"
	       (dictree--name dict) count))
    count))



;; ----------------------------------------------------------------
;;                        Using dictrees as stacks

;; A dictree--meta-stack is the meta-dict version of a dictree-stack (the
;; ordinary version is just a single trie-stack). It consists of a heap of
;; trie-stacks for its constituent tries, where the heap order is the usual
;; lexical order over the keys at the top of the trie-stacks.
(defstruct
  (dictree--meta-stack
   (:constructor nil)
   (:constructor dictree--meta-stack-create
		 (dict &optional (type 'vector) reverse
		  &aux
		  (combfun (dictree--meta-dict-combfun dict))
		  (sortfun (eval (macroexpand
				  `(trie-construct-sortfun
				    ,(dictree-comparison-function dict)))))
		  (heap (heap-create
			 (eval (macroexpand
				`(dictree--construct-meta-stack-heapfun
				  ,sortfun)))
			 (length (dictree--trielist dict))))
		  (dummy (mapc
			  (lambda (dic)
			    (heap-add heap (trie-stack dic type reverse)))
			  (dictree--trielist dict)))))
   (:constructor dictree--complete-meta-stack-create
		 (dict prefix &optional reverse
		  &aux
		  (combfun (dictree--meta-dict-combfun dict))
		  (sortfun (eval (macroexpand
				  `(trie-construct-sortfun
				    ,(dictree-comparison-function dict)))))
		  (heap (heap-create
			 (eval (macroexpand
				`(dictree--construct-meta-stack-heapfun
				  ,sortfun
				  ,reverse)))
			 (length (dictree--trielist dict))))
		  (dummy (mapc
			  (lambda (trie)
			    (let ((stack (trie-complete-stack
					  trie prefix reverse)))
			      (unless (trie-stack-empty-p stack)
				(heap-add heap stack))))
			  (dictree--trielist dict)))))
   (:copier nil))
  combfun sortfun heap)


(defmacro dictree--construct-meta-stack-heapfun (sortfun &optional reverse)
  ;; Wrap SORTFUN, which sorts keys, so it can act on dictree--meta-stack
  ;; elements.
  (if reverse
      `(lambda (a b) (,sortfun (car (dictree-stack-first b))
			       (car (dictree-stack-first a))))
    `(lambda (a b) (,sortfun (car (dictree-stack-first a))
			     (car (dictree-stack-first b))))))


(defun dictree-stack (dict &optional type reverse)
  "Create an object that allows DICT to be accessed as if it were a stack.

The stack is sorted in \"lexical\" order, i.e. the order defined
by the DICT's comparison function, or in reverse order if REVERSE
is non-nil. Calling `dictree-stack-pop' pops the top element (a
key and its associated data) from the stack.

Optional argument TYPE (one of the symbols vector, lisp or
string) sets the type of sequence used for the keys.

Note that any modification to DICT *immediately* invalidates all
dictree-stacks created before the modification (in particular,
calling `dictree-stack-pop' will give unpredictable results).

Operations on dictree-stacks are significantly more efficient
than constructing a real stack from the dictionary and using
standard stack functions. As such, they can be useful in
implementing efficient algorithms on dictionaries. However, in
cases where mapping functions `dictree-mapc', `dictree-mapcar' or
`dictree-mapf' would be sufficient, it is better to use one of
those instead."
  (if (dictree--meta-dict-p dict)
      (dictree--meta-stack-create dict type reverse)
    (trie-stack (dictree--trie dict) type reverse)))


(defun dictree-complete-stack (dict prefix &optional reverse)
  "Return an object that allows completions of PREFIX to be accessed
as if they were a stack.

The stack is sorted in \"lexical\" order, i.e. the order defined
by DICT's comparison function, or in reverse order if REVERSE is
non-nil. Calling `dictree-stack-pop' pops the top element (a key
and its associated data) from the stack.

PREFIX must be a sequence (vector, list or string) that forms the
initial part of a TRIE key. (If PREFIX is a string, it must be
possible to apply `string' to individual elements of TRIE keys.)
The completions returned in the alist will be sequences of the
same type as KEY. If PREFIX is a list of sequences, completions
of all sequences in the list are included in the stack. All
sequences in the list must be of the same type.

Note that any modification to DICT *immediately* invalidates all
trie-stacks created before the modification (in particular,
calling `dictree-stack-pop' will give unpredictable results).

Operations on dictree-stacks are significantly more efficient
than constructing a real stack from completions of PREFIX in DICT
and using standard stack functions. As such, they can be useful
in implementing efficient algorithms on tries. However, in cases
where `dictree-complete' or `dictree-complete-ordered' is
sufficient, it is better to use one of those instead."
  (if (dictree--meta-dict-p dict)
      (dictree--complete-meta-stack-create dict prefix reverse)
    (trie-complete-stack (dictree--trie dict) prefix reverse)))


(defun dictree-stack-pop (dictree-stack)
  "Pop the first element from the DICTREE-STACK.
Returns nil if the stack is empty."
  (let ((popped (dictree--stack-pop dictree-stack)))
    (when popped (cons (car popped) (dictree--cell-data (cdr popped))))))


(defun dictree--stack-pop (dictree-stack)
  ;; Pop the raw first element from DICTREE-STACK. Returns nil if the stack is
  ;; empty.

  ;; dictree-stack for normal dictionaries is a trie-stack
  (if (trie-stack-p dictree-stack)
      (trie-stack-pop dictree-stack)

    ;; meta-dictionary dictree-stack...more work!
    (let ((heap (dictree--meta-stack-heap dictree-stack))
	  (sortfun (dictree--meta-stack-sortfun dictree-stack))
	  stack curr next cell)
      (unless (heap-empty heap)
	;; remove the first dictree-stack from the heap, pop it's first
	;; element, and add it back to the heap (note that it will almost
	;; certainly not end up at the root again)
	(setq stack (heap-delete-root heap))
	(setq curr (dictree--stack-pop stack))
	(unless (dictree-stack-empty-p stack) (heap-add heap stack))
	;; peek at the first element of the new stack at the root of the heap
	(unless (heap-empty heap)
	  (setq next (dictree--stack-first (heap-root heap)))
	  ;; repeat this as long as we keep finding elements with the same key,
	  ;; combining them together as we go
	  (when (dictree--meta-stack-combfun dictree-stack)
	    (while (and (null (funcall sortfun (car curr) (car next)))
			(null (funcall sortfun (car next) (car curr))))
	      (setq stack (heap-delete-root heap))
	      (setq next (dictree--stack-pop stack))
	      (setq curr
		    (cons (car curr)
			  (dictree--cell-create
			   (funcall (dictree--meta-stack-combfun dictree-stack)
				    (dictree--cell-data (cdr curr))
				    (dictree--cell-data (cdr next)))
			   (append (dictree--cell-plist (cdr curr))
				   (dictree--cell-plist (cdr next))))))
	      (heap-add heap stack)
	      (setq next (dictree--stack-first (heap-root heap))))))
	;; return the combined dictionary element
	curr))))


(defun dictree--stack-first (dictree-stack)
  "Return the first element from DICTREE-STACK, without removing it.
Returns nil if the stack is empty."
  (if (trie-stack-p dictree-stack)
      ;; normal dict
      (trie-stack-first dictree-stack)
    ;; meta-dict
    (dictree--stack-first
     (heap-root (dictree--meta-stack-heap dictree-stack)))))


(defun dictree-stack-first (dictree-stack)
  "Return the first element from DICTREE-STACK, without removing it.
Returns nil if the stack is empty."
  (let ((first (dictree--stack-first dictree-stack)))
    (cons (car first) (dictree--cell-data (cdr first)))))


(defun dictree-stack-empty-p (dictree-stack)
  "Return t if DICTREE-STACK is empty, nil otherwise."
  (if (trie-stack-p dictree-stack)
      (trie-stack-empty-p dictree-stack)  ; normal dict
    (heap-empty (dictree--meta-stack-heap dictree-stack))))  ; meta--dict




;; ----------------------------------------------------------------
;;                        Advanced queries

(defun dictree--query (query-type dict arg
		       &optional
		       rank-function maxnum reverse no-cache filter)
  ;; Return results of QUERY-TYPE (currently, only 'complete is implemented)
  ;; on DICT. If RANK-FUNCTION is non-nil, return results ordered accordingly.

  ;; wrap DICT in a list if necessary
  (when (dictree-p dict) (setq dict (list dict)))

  (let (cache completions cmpl)
    ;; map over all dictionaries in list
    (dolist (dic dict)
      (cond
       ;; If FILTER or custom RANK-FUNCTION was specified, look in trie since
       ;; we don't cache custom searches. We pass a slightly redefined filter
       ;; to `trie-complete' to deal with data wrapping.
       ((or filter
	    (and rank-function
		 (not (eq rank-function (dictree-rank-function dic)))))
	(setq cmpl
	      (dictree--do-query
	       query-type dic arg rank-function maxnum reverse
	       (when filter
		 (eval (macroexpand `(dictree--wrap-filter ,filter)))))))


       ;; if there's a cached result with enough completions, use it
       ((and (setq cache
		   (if (dictree--query-cacheparam query-type dic
						  rank-function)
		       (gethash (cons arg reverse)
				(dictree--query-cache
				 query-type dic rank-function))
		     nil))
	     (or (null (dictree--cache-maxnum cache))
		 (and maxnum (<= maxnum (dictree--cache-maxnum cache)))))
	(setq cmpl (dictree--cache-completions cache))
	;; drop any excess completions
	(when (and maxnum
		   (or (null (dictree--cache-maxnum cache))
		       (> (dictree--cache-maxnum cache) maxnum)))
	  (setcdr (nthcdr (1- maxnum) completions) nil)))

       ;; if there was nothing useful in the cache, do query and time it
       (t
	(let (time)
	  (setq time (float-time))
	  (setq cmpl (dictree--do-query
		      query-type dic arg rank-function maxnum reverse nil))
	  (setq time (- (float-time) time))
	  ;; if we took longer than dictionary's completion cache threshold,
	  ;; cache the result
	  (when (and (not no-cache)
		     (dictree--query-cacheparam query-type dic rank-function)
		   (or (eq (dictree--query-cacheparam
			    query-type dic rank-function)
			   t)
		       (> time (dictree--query-cacheparam
				query-type dic rank-function))))
	  (setf (dictree-modified dic) t)
	  (puthash (cons arg reverse)
		   (dictree--cache-create cmpl maxnum)
		   (dictree--query-cache query-type dic rank-function))))))

      ;; merge new completion into completions list
      (setq completions
	    (dictree--merge
	     completions cmpl
	     (if rank-function
		 (eval (macroexpand `(dictree--wrap-rankfun ,rank-function)))
	       `(lambda (a b)
		  (,(eval (macroexpand
			   `(trie-construct-sortfun
			     ,(dictree-comparison-function (car dict)))))
		   (car a) (car b))))
	     nil maxnum))
      )
    completions))



(defun dictree--do-query (query-type dict arg
			  &optional
			  rank-function maxnum reverse filter)
  ;; Return first MAXNUM results of running QUERY-TYPE on DICT that satisfy
  ;; FILTER, ordered according to RANK-FUNCTION (defaulting to "lexical"
  ;; order).

  ;; for a meta-dict, use a dictree-stack
  (if (dictree--meta-dict-p dict)
      (let ((stack (funcall (dictree--query-stackfun query-type)
			    dict arg reverse))
	    (heap (when rank-function
		    (heap-create     ; heap order is inverse of rank order
			(if reverse
			    rank-function
			  (lambda (a b) (not (funcall rank-function a b))))
			(1+ maxnum))))
	    (i 0) cmpl completions)
	;; pop MAXNUM completions from the stack
	(while (and (or (null maxnum) (< i maxnum))
		    (setq cmpl (dictree-stack-pop stack)))
	  ;; check completion passes FILTER
	  (when (or (null filter) (funcall filter cmpl))
	    (if rank-function
		(heap-add heap cmpl)   ; for ranked query, add to heap
	      (push cmpl completions)) ; for lexical query, add to list
	    (incf i)))
	(if (null rank-function)
	    ;; for lexical query, reverse and return completion list (we built
	    ;; it backwards)
	    (nreverse completions)
	  ;; for ranked query, pass rest of completions through heap
	  (while (setq cmpl (dictree-stack-pop stack))
	    (heap-add heap cmpl)
	    (heap-delete-root heap))
	  ;; extract completions from heap
	  (while (setq cmpl (heap-delete-root heap))
	    (push cmpl completions))
	  completions))  ; return completion list

    ;; for a normal dict, call corresponding trie function on dict's trie
    ;; Note: could use a dictree-stack here too - would it be more efficient?
    (funcall (dictree--query-triefun query-type)
	     (dictree--trie dict) arg
	     (when rank-function
	       (eval (macroexpand `(dictree--wrap-rankfun ,rank-function))))
	     maxnum reverse filter)))



;; ----------------------------------------------------------------
;;                        Completing

(defun dictree-complete (dict prefix
			 &optional
			 rank-function maxnum reverse no-cache filter
			 strip-data)
  "Return an alist containing all completions of sequence PREFIX
from dictionary DICT, along with their associated data, sorted
according to RANK-FUNCTION (defaulting to \"lexical\" order, i.e. the
order defined by the dictionary's comparison function,
cf. `dictree-create'). If no completions are found, return nil.

PREFIX can also be a list of sequences, in which case completions of
all elements in the list are returned, merged together in a
single sorted alist.

DICT can also be a list of dictionaries, in which case
completions are sought in all dictionaries in the list. (Note
that if the same key appears in multiple dictionaries, the alist
may contain the same key multiple times, each copy associated
with the data from a different dictionary. If you want to combine
identical keys, use a meta-dictionary; see
`dictree-meta-dict-create'.)

If optional argument RANK-FUNCTION is any non-nil value that is
not a function, the completions are sorted according to the
dictionary's rank-function (see `dictree-create'). Any non-nil
value that *is* a function over-rides this. In that case,
RANK-FUNCTION should accept two arguments, both cons cells. The
car of each contains a sequence from the trie (of the same type
as PREFIX), the cdr contains its associated data. The
RANK-FUNCTION should return non-nil if first argument is ranked
strictly higher than the second, nil otherwise.

The optional integer argument MAXNUM limits the results to the
first MAXNUM completions.

If the optional argument NO-CACHE is non-nil, it prevents caching
of the result. Ignored for dictionaries that do not have
completion caching enabled.

The FILTER argument sets a filter function for the
completions. For each potential completion, it is passed two
arguments: the completion, and its associated data. If the filter
function returns nil, the completion is not included in the
results, and doesn't count towards MAXNUM.

If STRIP-DATA is non-nil, a list of completions is
returned (rather than an alist), without the data."
  ;; run completion query
  (let ((completions
	 (dictree--query
	  'complete dict prefix
	  (when rank-function
	    (if (functionp rank-function)
		rank-function
	      (dictree-rank-function (if (listp dict) (car dict) dict))))
	  maxnum reverse no-cache filter)))
    (if strip-data
	(mapcar 'car completions)
      completions)))



(defun dictree-collection-function (dict string predicate all)
  "Function for use in `try-completion', `all-completions',
and `completing-read'. To complete from dictionary DICT, use the
following as the COLLECTION argument of any of those functions:

  (lambda (string predicate all)
    (dictree-collection-function dict string predicate all))

Note that PREDICATE will be called with two arguments: the
completion, and its associated data."
  (let ((completions
	 (dictree-complete dict string nil nil nil nil predicate t)))
    (if all
	completions
      (try-completion "" completions))))





;; ----------------------------------------------------------------
;;                    Persistent storage

(defun dictree-save (dict &optional compilation)
  "Save dictionary DICT to it's associated file.
Use `dictree-write' to save to a different file.

Optional argument COMPILATION determines whether to save the
dictionary in compiled or uncompiled form. The default is to save
both forms. See `dictree-write'."

  (let* ((filename (dictree--filename dict)))

    ;; if dictionary has no associated file, prompt for one
    (unless (and filename (> (length filename) 0))
      (setq filename
	    (read-file-name
	     (format "Save %s to file (leave blank to NOT save): "
		     (dictree--name dict))))
      (setf (dictree-filename dict) filename))

    ;; if filename is blank, don't save
    (if (string= filename "")
	(message "No file supplied. Dictionary %s NOT saved" (dictree--name dict))
      ;; otherwise write dictionary to file without requiring confirmation
      (dictree-write dict filename t compilation))))



(defun dictree-write (dict filename &optional overwrite compilation)
  "Write dictionary DICT to file FILENAME.

If optional argument OVERWRITE is non-nil, no confirmation will
be asked for before overwriting an existing file.

The default is to create both compiled and uncompiled versions of
the dictionary, with extensions .elc and .el respectively (if
FILENAME has either of these extensions, they are stripped off
before proceeding). The compiled version is always used in
preference to the uncomplied version, as it loads
faster. However, only the uncompiled version is portable between
different Emacs versions.

If optional argument COMPILATION is the symbol 'compiled, only
the compiled version will be created, whereas if it is the symbol
'uncompiled, only the uncompiled version will be created."

  (let (dictname buff tmpfile)
    ;; add .el(c) extension to the filename if not already there
    (cond
     ((string= (substring filename -3) ".el")
      (setq filename (substring filename 0 -3)))
     ((string= (substring filename -4) ".elc")
      (setq filename (substring filename 0 -4))))

    ;; remove .el(c) extension from filename to create saved dictionary
    ;; name
    (setq dictname (file-name-nondirectory filename))

    (save-excursion
      ;; create a temporary file
      (setq buff
	    (find-file-noselect (setq tmpfile (make-temp-file dictname))))
      (set-buffer buff)
      ;; call the appropriate write function to write the dictionary code
      (if (dictree--meta-dict-p dict)
	  (dictree--write-meta-dict-code dict dictname)
	(dictree--write-dict-code dict dictname))
      (save-buffer)
      (kill-buffer buff))

    ;; prompt to overwrite if necessary
    (when (or overwrite
	      (and
	       (or (eq compilation 'compiled)
		   (not (file-exists-p (concat filename ".el"))))
	       (or (eq compilation 'uncompiled)
		   (not (file-exists-p (concat filename ".elc")))))
	      (y-or-n-p
	       (format "File %s already exists. Overwrite? "
		       (concat filename ".el(c)"))))
      (condition-case nil
	  (progn
	    ;; move the uncompiled version to its final destination
	    (unless (eq compilation 'compiled)
	      (copy-file tmpfile (concat filename ".el") t))
	    ;; byte-compile and move the compiled version to its final
	    ;; destination
	    (unless (eq compilation 'uncompiled)
	      (if (save-window-excursion
		    (let ((restore byte-compile-disable-print-circle)
			  err)
		      (setq byte-compile-disable-print-circle t)
		      (setq err (byte-compile-file tmpfile))
		      (setq byte-compile-disable-print-circle restore)
		      err))
		  (rename-file (concat tmpfile ".elc")
			       (concat filename ".elc") t)
		(error))))
	(error (error "Error saving. Dictionary %s NOT saved" dictname)))

      ;; if writing to a different name, unload dictionary under old name and
      ;; reload it under new one
      (setf (dictree-modified dict) nil)
      (unless (string= dictname (dictree-name dict))
	(dictree-unload dict)
	(dictree-load filename)))

    (delete-file tmpfile)
    (message "Dictionary %s saved to %s" dictname filename)
    t))  ; return t to indicate dictionary was successfully saved



(defun dictree-save-modified (&optional dict ask compilation)
  "Save all modified dictionaries that have a non-nil autosave flag.

If optional argument DICT is a list of dictionaries or a single
dictionary, only save those (even if their autosave flags are not
set). If DICT is non-nil but not a list of dictionaries, save all
dictionaries, irrespective of their autosave flag. Interactively,
this can be set by supplying a prefix argument.

If optional argument ASK is non-nil, ask for confirmation before
saving.

Optional argument COMPILATION determines whether to save the
dictionaries in compiled or uncompiled form. The default is to
save both forms. See `dictree-write'."

  ;; sort out DICT argument
  (cond
   ((dictree-p dict) (setq dict (list dict)))
   ((and (listp dict) (dictree-p (car dict))))
   (dict (setq dict 'all)))

  ;; For each dictionary in list / each loaded dictionary, check if dictionary
  ;; has been modified. If so, save it if autosave is on or if saving all
  (dolist (dic (if (or (null dict) (eq dict 'all))
		    dictree-loaded-list
		  dict))
    (when (and (dictree-modified dic)
	       (or (eq dict 'all) (dictree-autosave dic))
	       (or (not ask)
		   (y-or-n-p (format "Save modified dictionary %s? "
				     (dictree-filename dic)))))
      (dictree-save dic compilation)
      (setf (dictree-modified dic) nil))))


;; Add the dictree-save-modified function to the kill-emacs-hook to save
;; modified dictionaries when exiting emacs
(add-hook 'kill-emacs-hook 'dictree-save-modified)



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

    ;; ensure the dictionary name and file name associated with the
    ;; dictionary match the file it was loaded from
    (setf (dictree-filename dict) (expand-file-name file))
    (setf (dictree-name dict) dictname)

    ;; make sure the dictionary is in dictree-loaded-list (normally the lisp
    ;; code in the dictionary itself should do this, but just to make sure...)
    (unless (memq dict dictree-loaded-list)
      (push dict dictree-loaded-list))
    (message (format "Loaded dictionary %s" dictname))))



(defun dictree-unload (dict &optional dont-save)
  "Unload dictionary DICT.
If optional argument DONT-SAVE is non-nil, the dictionary will
NOT be saved even if its autosave flag is set."
  (interactive (list (read-dict "Dictionary to unload: ")
		     current-prefix-arg))

  ;; if dictionary has been modified, autosave is set and not overidden,
  ;; save it first
  (when (and (dictree-modified dict)
	     (null dont-save)
	     (or (eq (dictree-autosave dict) t)
		 (and (eq (dictree-autosave dict) 'ask)
		      (y-or-n-p
		       (format
			"Dictionary %s modified. Save before unloading? "
			(dictree-name dict))))))
    (dictree-save dict)
    (setf (dictree-modified dict) nil))

  ;; if unloading a meta-dict, remove reference to it from constituent
  ;; dictionaries' meta-dict-list cell
  (when (dictree--meta-dict-p dict)
    (mapc
     (lambda (dic)
       (setf (dictree--meta-dict-list dic)
	     (delq dict (dictree--meta-dict-list dic))))
     (dictree--meta-dict-dictlist dict)))

  ;; remove dictionary from list of loaded dictionaries and unload it
  (setq dictree-loaded-list (delq dict dictree-loaded-list))
  (unintern (dictree-name dict))
  (message "Dictionary %s unloaded" (dictree-name dict)))



(defun dictree--write-dict-code (dict dictname)
  ;; Write code for normal dictionary DICT to current buffer, giving it the
  ;; name DICTNAME.
  (let (hashcode tmpdict tmptrie
	lookup-alist complete-alist complete-ranked-alist)

    ;; --- convert trie data ---
    ;; if dictionary doesn't use any custom save functions, write dictionary's
    ;; trie directly as is
    (setq tmptrie (dictree--trie dict))
    ;; otherwise, create a temporary trie and populate it with the converted
    ;; contents of the dictionary's trie
    (when (or (dictree--data-savefun dict) (dictree--plist-savefun dict))
      (setq tmptrie
	    (trie-create-custom
	     (trie-comparison-function tmptrie)
	     :createfun (trie--createfun tmptrie)
	     :insertfun (trie--insertfun tmptrie)
	     :deletefun (trie--deletefun tmptrie)
	     :lookupfun (trie--lookupfun tmptrie)
	     :mapfun (trie--mapfun tmptrie)
	     :emptyfun (trie--emptyfun tmptrie)
	     :stack-createfun (trie--stack-createfun tmptrie)
	     :stack-popfun (trie--stack-popfun tmptrie)
	     :stack-emptyfun (trie--stack-emptyfun tmptrie)))
      (trie-mapc
       (lambda (key cell)
	 (trie-insert tmptrie key
		      (dictree--cell-create
		       (funcall (or (dictree--data-savefun dict) 'identity)
				(dictree--cell-data cell))
		       (funcall (or (dictree--plist-savefun dict) 'identity)
				(dictree--cell-plist cell)))))
       (dictree--trie dict)))
    ;; generate code to convert contents of trie back to original form
    (cond
     ;; convert both data and plist
     ((and (dictree--data-loadfun dict) (dictree--plist-loadfun dict))
      (setq hashcode
	    (concat
	     hashcode
	     "(trie-map\n"
	     " (lambda (key cell)\n"
	     "    (dictree--cell-create\n"
	     "     (funcall (dictree--data-loadfun " dictname ")\n"
	     "              (dictree--cell-data cell))\n"
	     "     (funcall (dictree--plist-loadfun " dictname ")\n"
	     "              (dictree--cell-plist cell))))\n"
	     " (dictree--trie " dictname "))\n")))
     ;; convert only data
     ((dictree--data-loadfun dict)
      (setq hashcode
	    (concat
	     hashcode
	     "(trie-map\n"
	     " (lambda (key cell)\n"
	     "    (dictree--cell-create\n"
	     "     (funcall (dictree--data-loadfun " dictname ")\n"
	     "              (dictree--cell-data cell))\n"
	     "     (dictree--cell-plist cell)))\n"
	     " (dictree--trie " dictname "))\n")))
     ;; convert only plist
     ((dictree--plist-loadfun dict)
      (setq hashcode
	    (concat
	     hashcode
	     "(trie-map\n"
	     " (lambda (key cell)\n"
	     "    (dictree--cell-create\n"
	     "     (dictree--cell-data cell)\n"
	     "     (funcall (dictree--plist-loadfun " dictname ")\n"
	     "              (dictree--cell-plist cell))))\n"
	     " (dictree--trie " dictname "))\n"))))


    ;; --- convert hash tables to alists ---
    ;; convert lookup cache hash table to alist, if it exists
    (when (dictree--lookup-cache-threshold dict)
      (maphash
       (lambda (key val)
	 (push
	  (cons key
		(cons (mapcar 'car (dictree--cache-completions val))
		      (dictree--cache-maxnum val)))
	  lookup-alist))
       (dictree--lookup-cache dict))
      ;; generate code to reconstruct the lookup hash table
      (setq hashcode
	    (concat
	     hashcode
	     "(let ((lookup-cache (make-hash-table :test 'equal))\n"
	     "      (trie (dictree--trie " dictname ")))\n"
	     "  (mapc\n"
	     "   (lambda (entry)\n"
	     "     (puthash\n"
	     "      (car entry)\n"
	     "      (dictree--cache-create\n"
	     "       (mapcar\n"
	     "        (lambda (key)\n"
	     "          (cons key (trie-member trie key)))\n"
	     "        (dictree--cache-completions (cdr entry)))\n"
	     "       (dictree--cache-maxnum (cdr entry)))\n"
	     "      lookup-cache))\n"
	     "   (dictree--lookup-cache " dictname "))\n"
	     "  (setf (dictree--lookup-cache " dictname ")\n"
	     "        lookup-cache))\n"
	     )))

    ;; convert completion cache hash table to alist, if it exists
    (when (dictree--complete-cache-threshold dict)
      (maphash
       (lambda (key val)
	 (push
	  (cons key
		(cons (mapcar 'car (dictree--cache-completions val))
		      (dictree--cache-maxnum val)))
	  complete-alist))
       (dictree-complete-cache dict))
      ;; generate code to reconstruct the completion hash table
      (setq
       hashcode
       (concat
	hashcode
	"(let ((complete-cache (make-hash-table :test 'equal))\n"
	"      (trie (dictree--trie " dictname ")))\n"
	"  (mapc\n"
	"   (lambda (entry)\n"
	"     (puthash\n"
	"      (car entry)\n"
	"      (dictree--cache-create\n"
	"       (mapcar\n"
	"        (lambda (key)\n"
	"          (cons key (trie-member trie key)))\n"
	"        (dictree--cache-completions (cdr entry)))\n"
	"       (dictree--cache-maxnum (cdr entry)))\n"
	"      complete-cache))\n"
	"   (dictree--complete-cache " dictname "))\n"
	"  (setf (dictree--complete-cache " dictname ")\n"
	"        complete-cache))\n"
	)))

    ;; convert ranked completion cache hash table to alist, if it exists
    (when (dictree--complete-ranked-cache-threshold dict)
      (maphash
       (lambda (key val)
	 (push
	  (cons key
		(cons (mapcar 'car (dictree--cache-completions val))
		      (dictree--cache-maxnum val)))
	  complete-ranked-alist))
       (dictree--complete-ranked-cache dict))
      ;; generate code to reconstruct the ordered hash table
      (setq hashcode
	    (concat
	     hashcode
	     "(let ((complete-ranked-cache (make-hash-table :test 'equal))\n"
	     "      (trie (dictree--trie " dictname ")))\n"
	     "  (mapc\n"
	     "   (lambda (entry)\n"
	     "     (puthash\n"
	     "      (car entry)\n"
	     "      (dictree--cache-create\n"
	     "       (mapcar\n"
	     "        (lambda (key)\n"
	     "          (cons key (trie-member trie key)))\n"
	     "        (dictree--cache-completions (cdr entry)))\n"
	     "       (dictree--cache-maxnum (cdr entry)))\n"
	     "      complete-ranked-cache))\n"
	     "   (dictree--complete-ranked-cache " dictname "))\n"
	     "  (setf (dictree--complete-ranked-cache " dictname ")\n"
	     "        complete-ranked-cache))\n"
	     )))


    ;; --- write to file ---
    ;; generate the structure to save
    (setq tmpdict (dictree-create))
    (setf (dictree--name tmpdict) dictname)
    (setf (dictree--filename tmpdict) nil)  ; filename gets set on loading
    (setf (dictree--autosave tmpdict) (dictree--autosave dict))
    (setf (dictree--modified tmpdict) nil)
    (setf (dictree--comparison-function tmpdict)
	  (dictree--comparison-function dict))
    (setf (dictree--insert-function tmpdict)
	  (dictree--insert-function dict))
    (setf (dictree--insfun tmpdict)
	  (dictree--insfun dict))
    (setf (dictree--rank-function tmpdict)
	  (dictree--rank-function dict))
    (setf (dictree--rankfun tmpdict)
	  (dictree--rankfun dict))
    (setf (dictree--cache-policy tmpdict)
	  (dictree--cache-policy dict))
    (setf (dictree--cache-update-policy tmpdict)
	  (dictree--cache-update-policy dict))
    (setf (dictree--lookup-cache tmpdict) lookup-alist)
    (setf (dictree--lookup-cache-threshold tmpdict)
	  (dictree--lookup-cache-threshold dict))
    (setf (dictree--complete-cache tmpdict) complete-alist)
    (setf (dictree--complete-cache-threshold tmpdict)
	  (dictree--complete-cache-threshold dict))
    (setf (dictree--complete-ranked-cache tmpdict) complete-ranked-alist)
    (setf (dictree--complete-ranked-cache-threshold tmpdict)
	  (dictree--complete-ranked-cache-threshold dict))
    (setf (dictree--trie tmpdict) tmptrie)
    (setf (dictree--key-savefun tmpdict) (dictree--key-savefun dict))
    (setf (dictree--key-loadfun tmpdict) (dictree--key-loadfun dict))
    (setf (dictree--data-savefun tmpdict) (dictree--data-savefun dict))
    (setf (dictree--data-loadfun tmpdict) (dictree--data-loadfun dict))
    (setf (dictree--plist-savefun tmpdict) (dictree--plist-savefun dict))
    (setf (dictree--plist-loadfun tmpdict) (dictree--plist-loadfun dict))
    (setf (dictree--meta-dict-list tmpdict) nil)

    ;; write lisp code that generates the dictionary object
    (insert "(eval-when-compile (require 'cl))\n")
    (insert "(require 'dict-tree)\n")
    (insert "(defvar " dictname " nil \"Dictionary " dictname ".\")\n")
    (insert "(setq " dictname " '" (prin1-to-string tmpdict) ")\n")
    (insert hashcode)
    (insert "(setf (dictree-filename " dictname ")\n"
	    "      (locate-library \"" dictname "\"))\n")
    (insert "(unless (memq " dictname " dictree-loaded-list)\n"
	    "  (push " dictname " dictree-loaded-list))\n")
    (insert "(provide '" dictname ")\n")))




(defun dictree--write-meta-dict-code (dict dictname)
  "Write code for meta-dictionary DICT to current buffer,
giving it the name DICTNAME."

  (let (hashcode tmpdict lookup-alist complete-alist
		 complete-ranked-alist)

    ;; dump caches to alists as necessary and generate code to reconstruct
    ;; the hash tables from the alists

    ;; create the lookup alist, if necessary
    (when (dictree--lookup-cache-threshold dict)
      (maphash (lambda (key val)
		 (push (cons key (mapcar 'car val)) lookup-alist))
	       (dictree--meta-dict-lookup-cache dict))
      ;; generate code to reconstruct the lookup hash table
      (setq hashcode
	    (concat
	     hashcode
	     "(let ((lookup-cache (make-hash-table :test 'equal)))\n"
	     "  (mapc (lambda (entry)\n"
	     "    (puthash (car entry) (cdr entry) lookup-cache))\n"
	     "    (dictree--meta-dict-lookup-cache " dictname "))\n"
	     "  (setf (dictree--meta-dict-lookup-cache " dictname ")"
	            " lookup-cache))\n")))

    ;; create the completion alist, if necessary
    (when (dictree--complete-cache-threshold dict)
      (maphash (lambda (key val)
		 (push (cons key (mapcar 'car val)) complete-alist))
	       (dictree--meta-dict-complete-cache dict))
      ;; generate code to reconstruct the completion hash table
      (setq hashcode
	    (concat
	     hashcode
	     "(let ((complete-cache (make-hash-table :test 'equal)))\n"
	     "  (mapc (lambda (entry)\n"
	     "    (puthash (car entry) (cdr entry) complete-cache))\n"
	     "    (dictree--meta-dict-complete-cache " dictname "))\n"
	     "  (setf (dictree--meta-dict-complete-cache " dictname ")"
	            " complete-cache))\n")))

    ;; create the ordered completion alist, if necessary
    (when (dictree--complete-ranked-cache-threshold dict)
      (maphash (lambda (key val)
		 (push (cons key val) complete-ranked-alist))
	       (dictree--meta-dict-complete-ranked-cache dict))
      ;; generate code to reconstruct the ordered hash table
      (setq hashcode
	    (concat
	     hashcode
	     "(let ((complete-ranked-cache (make-hash-table :test 'equal)))\n"
	     "  (mapc (lambda (entry)\n"
	     "    (puthash (car entry) (cdr entry) complete-ranked-cache))\n"
	     "    (dictree--meta-dict-complete-ranked-cache " dictname "))\n"
	     "  (setf (dictree--meta-dict-complete-ranked-cache " dictname ")"
	            " complete-ranked-cache))\n")))


    ;; generate the structure to save
    (setq tmpdict (dictree-create))
    (setf (dictree--meta-dict-name tmpdict) dictname)
    (setf (dictree--meta-dict-filename tmpdict) nil)  ; set on loading
    (setf (dictree--meta-dict-autosave tmpdict) (dictree--autosave dict))
    (setf (dictree--meta-dict-modified tmpdict) nil)
    (setf (dictree--meta-dict-combine-function tmpdict)
	  (dictree--meta-dict-combine-function dict))
    (setf (dictree--meta-dict-combfun tmpdict)
	  (dictree--meta-dict-combfun dict))
    (setf (dictree--meta-dict-cache-policy tmpdict)
	  (dictree--meta-dict-cache-policy dict))
    (setf (dictree--meta-dict-cache-update-policy tmpdict)
	  (dictree--meta-dict-cache-update-policy dict))
    (setf (dictree--meta-dict-lookup-cache tmpdict)
	  lookup-alist)
    (setf (dictree--meta-dict-lookup-cache-threshold tmpdict)
	  (dictree--meta-dict-lookup-cache-threshold dict))
    (setf (dictree--meta-dict-complete-cache tmpdict)
	  complete-alist)
    (setf (dictree--meta-dict-complete-cache-threshold tmpdict)
	  (dictree--meta-dict-complete-cache-threshold dict))
    (setf (dictree--meta-dict-complete-ranked-cache tmpdict)
	  complete-ranked-alist)
    (setf (dictree--meta-dict-complete-ranked-cache-threshold tmpdict)
	  (dictree--meta-dict-complete-ranked-cache-threshold dict))
    (setf (dictree--meta-dict-dictlist tmpdict)
	  (dictree--meta-dict-dictlist dict))
    (setf (dictree--meta-dict-meta-dict-list tmpdict) nil)

    ;; write lisp code that generates the dictionary object
    (insert "(eval-when-compile (require 'cl))\n")
    (insert "(require 'dict-tree)\n")
    (mapc (lambda (name) (insert "(require '" name ")\n"))
	  (dictree--meta-dict-dictlist tmpdict))
    (insert "(defvar " dictname " nil \"Dictionary " dictname ".\")\n")
    (insert "(setq " dictname " '" (prin1-to-string tmpdict) ")\n")
    (insert "(dictree--meta-dict-dictlist\n"
	    " " dictname "\n"
	    " (mapcar (lambda (name) (eval (intern-soft name)))\n"
	    "         (dictree--meta-dict-dictlist " dictname " )))\n")
    (insert hashcode)
    (insert "(setf (dictree-filename " dictname ")"
	    " (locate-library \"" dictname "\"))\n")
    (insert "(unless (memq " dictname " dictree-loaded-list)"
	    " (push " dictname " dictree-loaded-list))\n")
        (insert "(provide '" dictname ")\n")))




;; ----------------------------------------------------------------
;;                Dumping and restoring contents

(defun dictree-populate-from-file (dict file)
  "Populate dictionary DICT from the key list in file FILE.

Each line of the file should contain a key, either a string
\(delimeted by \"\), a vector or a list. (Use the escape sequence
\\\" to include a \" in a string.) If a line does not contain a
key, it is silently ignored. The keys should ideally be sorted
\"lexically\", as defined by the dictionary's comparison-function
\(see `dictree-create'\).

Each line can optionally include data and meta-data to be
associated with the key, in that order, and separated from each
other and the key by whitespace.


Technicalities:

The key, data and property list are read as lisp expressions
using `read', and are read from the middle outwards, i.e. first
the middle key is read, then the key directly after it, then the
key directly before it, then the one two lines after the middle,
then the one two lines before, and so on. Assuming the keys in
the file are sorted \"lexically\", for some types of dictionary
this can help produce an efficient data-structure."

  (save-excursion
    (let ((buff (generate-new-buffer " *dictree-populate*")))
      ;; insert the key list into a temporary buffer
      (set-buffer buff)
      (insert-file-contents file)

      ;; insert the keys starting from the median to ensure a reasonably
      ;; well-balanced tree
      (let* ((lines (count-lines (point-min) (point-max)))
	     (midpt (+ (/ lines 2) (mod lines 2)))
	     entry)
        ;; insert the median key and set the dictionary's modified flag
	(dictree-goto-line midpt)
	(when (setq entry
		    (condition-case nil
			(dictree--read-line dict)
		      (error (error "Error reading line %d of %s"
				    midpt file))))
	  (dictree-insert dict (car entry) (nth 1 entry))
	  (setf (dictree--cell-plist (dictree--lookup dict (car entry) nil))
		(nth 2 entry)))
	(message "Inserting keys in %s...(1 of %d)"
		 (dictree-name dict) lines)
        ;; insert keys successively further away from the median in both
        ;; directions
	(dotimes (i (1- midpt))
	  (dictree-goto-line (+ midpt i 1))
	  (when (setq entry
		      (condition-case nil
			  (dictree--read-line dict)
			(error (error "Error reading line %d of %s"
				      (+ midpt i 1) file))))
	    (dictree-insert dict (car entry) (nth 1 entry))
	    (setf (dictree--cell-plist (dictree--lookup dict (car entry) nil))
		  (nth 2 entry)))
	  (when (= 49 (mod i 50))
	    (message "Inserting keys in %s...(%d of %d)"
		     (dictree-name dict) (+ (* 2 i) 2) lines))
	  (dictree-goto-line (- midpt i 1))
	  (when (setq entry
		      (condition-case nil
			  (dictree--read-line dict)
			(error (error "Error reading line %d of %s"
				      (- midpt i 1) file))))
	    (dictree-insert dict (car entry) (nth 1 entry))
	    (setf (dictree--cell-plist (dictree--lookup dict (car entry) nil))
		  (nth 2 entry))))

        ;; if file contains an even number of keys, we still have to add
        ;; the last one
	(when (= 0 (mod lines 2))
	  (dictree-goto-line lines)
	  (when (setq entry
		      (condition-case nil
			  (dictree--read-line dict)
			(error (error "Error reading line %d of %s"
				      lines file))))
	    (dictree-insert dict (car entry) (nth 1 entry))
	    (setf (dictree--cell-plist (dictree--lookup dict (car entry) nil))
		  (nth 2 entry))))
	(message "Inserting keys in %s...done" (dictree-name dict)))

      (kill-buffer buff))))



(defun dictree--read-line (dict)
  ;; Return a list containing the key, data (if any, otherwise nil) and
  ;; property list (ditto) at the current line of the current buffer, for
  ;; dictionary DICT.
  (save-excursion
    (let (key data plist)
      ;; read key
      (beginning-of-line)
      (setq key (read (current-buffer)))
      (when (dictree--key-loadfun dict)
	(setq key (funcall (dictree--key-loadfun dict) key)))
      ;; if there's anything after the key, use it as data
      (if (eq (line-end-position) (point))
	  (list key)
	(setq data (read (current-buffer)))
	(when (dictree--data-loadfun dict)
	  (setq data (funcall (dictree--data-loadfun dict) data)))
	(if (eq (line-end-position) (point))
	    (list key data)
	  ;; if there's anything after the data, use is as the property list
	  (setq plist (read (current-buffer)))
	  (when (dictree--plist-loadfun dict)
	    (funcall (dictree--plist-loadfun dict) plist))
	  ;; return the key and data
	  (list key data plist))))))



(defun dictree-dump-to-buffer (dict &optional buffer type)
  "Dump keys and their associated data
from dictionary DICT to BUFFER, in the same format as that used
by `dictree-populate-from-file'. If BUFFER exists, data will be
appended to the end of it. Otherwise, a new buffer will be
created. If BUFFER is omitted, the current buffer is used.

TYPE determines the type of sequence to use to represent the
keys, and should be one of 'string, 'vector or 'list. The default
is 'vector.

Note that if the data does not have a read syntax, the dumped
data can not be used to recreate the dictionary using
`dictree-populate-from-file'."

  ;; select the buffer, creating it if necessary
  (if buffer
      (setq buffer (get-buffer-create buffer))
    (setq buffer (current-buffer)))
  (set-buffer buffer)

  ;; move point to end of buffer and make sure it's at start of new line
  (goto-char (point-max))
  (unless (= (point) (line-beginning-position))
    (insert "\n"))

  ;; dump keys
  (message "Dumping keys from %s to %s..."
	   (dictree-name dict) (buffer-name buffer))
  (let ((count 0) (dictsize (dictree-size dict)))
    (message "Dumping keys from %s to %s...(key 1 of %d)"
	     (dictree-name dict) (buffer-name buffer) dictsize)

    ;; map dump function over dictionary
    (dictree--mapc
     (lambda (key data plist)
       (when (= 99 (mod count 100))
	 (message "Dumping keys from %s to %s...(key %d of %d)"
		  (dictree-name dict) (buffer-name buffer)
		  (1+ count) dictsize))
       (insert (prin1-to-string
		(funcall (or (dictree--key-savefun dict) 'identity) key)))
       (when (setq data
		   (funcall (or (dictree--data-savefun dict) 'identity) data))
	 (insert " " (prin1-to-string data)))
       (when (setq plist
		   (funcall (or (dictree--plist-savefun dict) 'identity) plist))
	 (unless data (insert " nil"))
	 (insert " " (prin1-to-string plist)))
       (insert "\n")
       (setq count (1+ count)))
     dict type)  ; dictree-mapc target

    (message "Dumping keys from %s to %s...done"
	     (dictree-name dict) (buffer-name buffer)))
  (switch-to-buffer buffer))



(defun dictree-dump-to-file (dict filename &optional type overwrite)
  "Dump keys and their associated data
from dictionary DICT to a text file FILENAME, in the same format
as that used by `dictree-populate-from-file'. Prompts to overwrite
FILENAME if it already exists, unless OVERWRITE is non-nil.

TYPE determines the type of sequence to use to represent the
keys, and should be one of 'string, 'vector or 'list. The default
is 'vector.

Note that if the data does not have a read syntax, the dumped
data can not be used to recreate the dictionary using
`dictree-populate-from-file'."

  ;; check if file exists, and prompt to overwrite it if necessary
  (if (and (file-exists-p filename)
	   (not overwrite)
	   (not (y-or-n-p
		 (format "File %s already exists. Overwrite? "
			 filename))))
      (message "Key dump cancelled")

    (let (buff)
      ;; create temporary buffer, dump keys to it, and save to FILENAME
      (setq buff (generate-new-buffer filename))
      (save-window-excursion
	(dictree-dump-to-buffer dict buff type)
	(write-file filename))
      (kill-buffer buff))))




;; ----------------------------------------------------------------
;;                     Minibuffer completion

(defvar dictree-history nil
  "History list for commands that read an existing ditionary name.")


(defun read-dict (prompt &optional default dictlist)
  "Read the name of a dictionary with completion, and return it.

Prompt with PROMPT. By default, return DEFAULT. If DICTLIST is
supplied, only complete on dictionaries in that list."
  (let (dictnames)
    (mapc (lambda (dict)
	    (unless (or (null (dictree-name dict))
			(member (dictree-name dict) dictnames))
	      (push (list (dictree-name dict)) dictnames)))
	  (or dictlist dictree-loaded-list))
    (eval (intern-soft
	   (completing-read prompt dictnames
			    nil t nil 'dictree-history default)))))



(provide 'dict-tree)

;;; dict-tree.el ends here
