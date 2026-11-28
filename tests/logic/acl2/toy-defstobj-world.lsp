; Read the admitted translated bodies and proved observations from the live world.
(in-package "ACL2")

(defun defstobj-logical-row (fn world)
  (let ((body (c3-property fn 'unnormalized-body world)))
    (unless (and body (function-symbolp fn world) (logicp fn world))
      (error "Missing logical definition for ~s" fn))
    (list fn (arity fn world) (formals fn world)
          (stobjs-in fn world) (stobjs-out fn world)
          (remove-guard-holders body world))))

(defun export-toy-defstobj (output)
  (let ((world (w *the-live-state*)))
    (with-open-file (out output :direction :output :if-exists :error :external-format :utf-8)
      (c3-json-term
       (list
        (loop for fn in '(len length = endp nth update-nth update-nth-array make-list-ac
                          toy-scalarp toy-cellsp sil-toyp create-sil-toy
                          toy-scalar update-toy-scalar toy-cellsi update-toy-cellsi)
              collect (defstobj-logical-row fn world))
        (loop for name in '(toy-create toy-valid toy-bad-scalar toy-bad-size toy-long-record
                            toy-dotted-cells toy-cell-type toy-read-scalar toy-write-scalar
                            toy-read-index toy-write-index toy-read-negative toy-write-noninteger
                            toy-read-past-end toy-write-past-end toy-write-atom toy-write-dotted
                            toy-write-invalid-type)
              collect (list name (c3-property name 'theorem world))))
       out)
      (terpri out))))
