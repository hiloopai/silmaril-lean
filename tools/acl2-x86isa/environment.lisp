;;; Export the translated logical environment recognizer from the certified world.
(in-package "ACL2")

(defun c3-export-environment (root output root-sha commit tree state-book state-sha axioms-sha)
  (let* ((state *the-live-state*)
         (world (w state))
         (samples (f-get-global 'c3-environment-samples state))
         (helpers (f-get-global 'c3-environment-helper-samples state))
         (functions '(x86isa::env-alistp x86isa::rip-ret-alistp x86isa::i48p$inline
                      alistp len assoc-equal true-listp endp atom eq not
                      signed-byte-p integer-range-p expt)))
    (c3-logical-certificate root state)
    (c3-logical-certificate state-book state)
    (unless (and samples helpers) (error "Missing environment observations"))
    (with-open-file (out output :direction :output :if-exists :error :external-format :utf-8)
      (format out "{~%")
      (loop for (key value) in
            `(("schema" 1)
              ("acl2_commit" ,commit)
              ("acl2_tree" ,tree)
              ("x86isa_exec" "nil")
              ("source_sha256" (("axioms.lisp" ,axioms-sha)
                                ("books/projects/x86isa/machine/state.lisp" ,state-sha)
                                ("books/projects/x86isa/machine/x86.lisp" ,root-sha)))
              ("functions" ,(mapcar (lambda (name) (c3-status-function name world)) functions))
              ("arities"
               ,(mapcar (lambda (name) (list name (arity name world)))
                        '(equal consp car cdr binary-+ integerp < unary-- zip = fix binary-* unary-/)))
              ("termination"
               ,(mapcar (lambda (name) (list name (termination-theorem name world)))
                        '(x86isa::rip-ret-alistp alistp len assoc-equal true-listp)))
              ("helper_observations" ,helpers))
            do (c3-field key value out) (format out ",~%"))
      (c3-field "observations" samples out)
      (format out "~%}~%"))))
