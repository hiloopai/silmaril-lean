;;; Inspect the immediate translated source of an exact list of frontier roots.
(in-package "ACL2")

(defun c3-frontier-symbol (package spelling arity world)
  (let ((fn (find-symbol spelling package)))
    (unless (and fn (equal (symbol-package-name fn) package)
                 (function-symbolp fn world) (logicp fn world)
                 (eql (arity fn world) arity))
      (error "Missing exact logical identity ~a::~a/~a" package spelling arity))
    fn))

(defun c3-export-frontier-dependencies (source output roots)
  (let* ((state *the-live-state*)
         (world (w state))
         (bodies
          (loop for (package spelling arity) in roots
                for fn = (c3-frontier-symbol package spelling arity world)
                for body = (c3-dependency-body fn world)
                collect (append body
                                (list (stobjs-in fn world) (stobjs-out fn world)
                                      (getpropc fn 'stobj-function nil world)
                                      (getpropc fn 'recursivep nil world)))))
         (names (remove-duplicates (append (mapcar #'first bodies)
                                           (mapcan (lambda (row) (copy-list (fourth row))) bodies))
                                   :test #'eq)))
    (c3-logical-certificate source state)
    (with-open-file (out output :direction :output :if-exists :error :external-format :utf-8)
      (c3-json-term (list bodies (mapcar (lambda (fn) (c3-dependency-world-row fn world)) names)) out)
      (terpri out))))
