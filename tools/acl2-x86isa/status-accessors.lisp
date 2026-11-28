;;; Read after including the pinned certified machine book.
(in-package "ACL2")

(defun c3-status-symbol (spelling)
  (or (find-symbol spelling "X86ISA") (error "Missing X86ISA::~a" spelling)))

(defun c3-cached-absstobj (node stobj)
  (when (consp node)
    (if (and (eq (car node) 'defabsstobj-events) (consp (cdr node)) (eq (cadr node) stobj))
        node
      (or (c3-cached-absstobj (car node) stobj)
          (c3-cached-absstobj (cdr node) stobj)))))

(defun c3-status-function (symbol world)
  (unless (and (function-symbolp symbol world) (logicp symbol world))
    (error "Missing logical declaration ~s" symbol))
  (let ((body (c3-property symbol 'unnormalized-body world)))
    (list symbol (arity symbol world)
          (formals symbol world) body (remove-guard-holders body world)
          (guard symbol t world)
          (stobjs-in symbol world) (stobjs-out symbol world)
          (symbol-class symbol world) (getpropc symbol 'stobj-function nil world))))

(defun c3-status-obligations (methods st foundation corr world)
  (loop for (name logic exec) in methods
        for formals = (subst st (car (formals logic world)) (formals logic world))
        for theorem = (find-symbol (concatenate 'string (symbol-name name) "{CORRESPONDENCE}")
                                   "X86ISA")
        collect
        (progn
          (unless (and theorem (equal (guard logic t world) *t*)
                       (eql (arity logic world) 1)
                       (equal (stobjs-in exec world) (list foundation))
                       (equal (stobjs-out exec world) '(nil)))
            (error "Unsupported correspondence signature for ~s" name))
          (list theorem (absstobj-correspondence-formula
                         logic exec corr formals *t* st foundation world)))))

(defun c3-export-status-accessors (root output root-sha commit tree state-book state-sha)
  (let* ((state *the-live-state*)
         (world (w state))
         (st (c3-status-symbol "X86"))
         (foundation (c3-status-symbol "X86$C"))
         (samples (f-get-global 'c3-status-samples state))
         (expansions (c3-logical-certificate state-book state))
         (cached (c3-cached-absstobj expansions st))
         (tuples (car (absstobj-tuples-lst st world)))
         (methods (mapcar (lambda (name) (assoc (c3-status-symbol name) tuples))
                          '("FAULT" "MS")))
         (event (cddr cached))
         (corr (getf event :corr-fn)))
    (c3-logical-certificate root state)
    (unless (and (eq (getf event :foundation) foundation) corr (= (length samples) 6))
      (error "Missing certified abstract stobj event or status samples"))
    (dolist (method methods)
      (destructuring-bind (name logic exec) method
        (unless (equal (assoc name (getf event :exports)) (list name :logic logic :exec exec))
          (error "The cached event and live abstract-stobj tuple disagree for ~s" name))))
    (with-open-file (out output :direction :output :if-exists :error :external-format :utf-8)
      (format out "{~%")
      (loop for (key value) in
            `(("schema" 1)
              ("acl2_commit" ,commit)
              ("acl2_tree" ,tree)
              ("x86isa_exec" "nil")
              ("root" "projects/x86isa/machine/x86.lisp")
              ("root_sha256" ,root-sha)
              ("source" "projects/x86isa/machine/state.lisp")
              ("source_sha256" ,state-sha)
              ("abstract_stobj" ,st)
              ("foundation" ,foundation)
              ("correspondence_relation" ,corr)
              ("accessor_tuples" ,methods)
              ("recognizer_tuple" ,(first tuples))
              ("creator_tuple" ,(second tuples))
              ("correspondence_obligations" ,(c3-status-obligations methods st foundation corr world))
              ("functions"
               ,(mapcar (lambda (name) (c3-status-function (c3-status-symbol name) world))
                        '("FAULT" "FAULT$A" "FAULT$C" "MS" "MS$A" "MS$C"
                          "XR" "X86REC-GET" "X86REC-TO-MTR" "X86REC-P" "X86REC-P1" "X86REC-GET1"
                          "X86-ELEM-DEFAULT-TOP" "X86-ELEM-DEFAULT" "X86REC-BAD-PART" "X86$AP"))))
            do (c3-field key value out) (format out ",~%"))
      (c3-field "samples" samples out)
      (format out "~%}~%"))))
