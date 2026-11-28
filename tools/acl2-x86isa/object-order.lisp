;;; Export the logical order and record recognizer from the certified world.
(in-package "ACL2")

(defun c3-export-object-order (root output root-sha commit tree state-book state-sha axioms-sha order-sha tty-sha)
  (let* ((state *the-live-state*)
         (world (w state))
         (samples (f-get-global 'c3-order-samples state))
         (entries (f-get-global 'c3-entry-samples state)))
    (c3-logical-certificate root state)
    (c3-logical-certificate state-book state)
    (unless (and samples entries) (error "Missing order and entry-list observations"))
    (with-open-file (out output :direction :output :if-exists :error :external-format :utf-8)
      (format out "{~%")
      (loop for (key value) in
            `(("schema" 1)
              ("acl2_commit" ,commit)
              ("acl2_tree" ,tree)
              ("x86isa_exec" "nil")
              ("source_sha256" (("axioms.lisp" ,axioms-sha) ("books/misc/total-order.lisp" ,order-sha)
                                ("books/projects/x86isa/machine/state.lisp" ,state-sha)
                                ("books/projects/x86isa/machine/tty.lisp" ,tty-sha)
                                ("books/projects/x86isa/machine/x86.lisp" ,root-sha)))
              ("functions"
               ,(mapcar (lambda (name) (c3-status-function name world))
                        '(<< lexorder alphorder symbol< string< string<= string<-l char< endp
                          bad-atom
                          x86isa::x86rec-p1 x86isa::x86-elem-default-top
                          x86isa::x86-elem-default x86isa::x86-elem-p-top x86isa::x86-elem-p
                          x86isa::tty-bufferp)))
              ("primitive_arities"
               ,(mapcar (lambda (name) (list name (arity name world)))
                        '(< = equal atom not consp car cdr null
                          rationalp complex-rationalp stringp symbolp characterp
                          char-code realpart imagpart symbol-name symbol-package-name
                          coerce length binary-+ eql bad-atom<=
                          booleanp keywordp natp signed-byte-p unsigned-byte-p
                          x86isa::env-alistp x86isa::tlbp)))
              ("order_laws"
               ,(mapcar (lambda (name) (list name (c3-property name 'theorem world)))
                        '(<<-irreflexive <<-transitive <<-asymmetric <<-trichotomy)))
              ("order_observations" ,samples))
            do (c3-field key value out) (format out ",~%"))
      (c3-field "entry_observations" entries out)
      (format out "~%}~%"))))
