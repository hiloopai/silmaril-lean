;;; Read metadata after including the certified pure Bitops book in ACL2.
(in-package "ACL2")

(defun export-bit-selection (source output)
  (let* ((state *the-live-state*)
         (world (w state)))
    (multiple-value-bind (expansions pre post live)
        (c1-certificate-evidence source state)
      (declare (ignore expansions))
      (dolist (entry (append pre post live))
        (let* ((book (if (eq (car entry) 'local) (cadr entry) entry))
               (annotations (fourth book)))
          (dolist (key '(:skipped-proofsp :axiomsp :ttags))
            (when (cdr (assoc key annotations))
              (error "Unexpected ~s annotation in ~s" key (car book)))))))
    (with-open-file (out output :direction :output :if-exists :error :external-format :utf-8)
      (c3-json-term
       (list
        (loop for fn in '(expt2$inline ifloor$inline imod$inline loghead$inline logtail$inline
                          bitops::part-select-width-low$inline bitops::part-select-low-high$inline)
              for body = (getpropc fn 'unnormalized-body nil world)
              collect (progn
                        (unless (and body (function-symbolp fn world) (logicp fn world))
                          (error "Missing logical definition for ~s" fn))
                        (list fn (arity fn world) (formals fn world) (remove-guard-holders body world))))
        (f-get-global 'bit-selection-samples state))
       out)
      (terpri out))))
