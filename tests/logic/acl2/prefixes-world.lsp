;;; Read logical definition metadata after the certified structures include.
(in-package "ACL2")

(defun export-prefixes (source output)
  (let* ((state *the-live-state*)
         (world (w state))
         (observations (f-get-global 'prefix-projection-samples state)))
    (c3-logical-certificate source state)
    (unless observations (error "Missing pure projection observations"))
    (with-open-file (out output :direction :output :if-exists :error :external-format :utf-8)
      (c3-json-term
       (list
        (loop for fn in '(loghead$inline bitops::part-select-width-low$inline
                          x86isa::prefixes-fix$inline x86isa::prefixes->adr$inline
                          x86isa::prefixes->num$inline x86isa::prefixes->nxt$inline)
              for body = (getpropc fn 'unnormalized-body nil world)
              collect (progn
                        (unless (and body (function-symbolp fn world) (logicp fn world))
                          (error "Missing logical definition for ~s" fn))
                        (list fn (arity fn world) (formals fn world) (remove-guard-holders body world))))
        observations)
       out)
      (terpri out))))
