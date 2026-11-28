;;; Read the logical definitions from the initial stock ACL2 world.
(in-package "ACL2")

(defun silmaril-write-symbol-part (part out)
  (write-char #\| out)
  (loop for c across part do
    (when (or (char= c #\|) (char= c #\\)) (write-char #\\ out))
    (write-char c out))
  (write-char #\| out))

(defun silmaril-write-export (datum out &optional nil-as-symbol)
  ;; Inside the translated body, NIL occurs as a quoted object.
  (cond ((null datum)
         (write-string (if nil-as-symbol "|COMMON-LISP|::|NIL|" "()") out))
        ((symbolp datum)
         (let ((package (symbol-package datum)))
           (unless package (error "Uninterned symbol in export: ~s" datum))
           (silmaril-write-symbol-part (package-name package) out)
           (write-string "::" out)
           (silmaril-write-symbol-part (symbol-name datum) out)))
        ((consp datum)
         (unless (true-listp datum) (error "Dotted list in export: ~s" datum))
         (write-char #\( out)
         (loop for (element . rest) on datum
               do (silmaril-write-export element out t)
               when rest do (write-char #\Space out))
         (write-char #\) out))
        ((or (integerp datum) (stringp datum)) (prin1 datum out))
        (t (error "Unsupported datum in export: ~s" datum))))

(defun silmaril-definition (name world)
  (let ((body (getpropc name 'unnormalized-body :missing world)))
    (unless (and (logicp name world) (not (eq body :missing))
                 (equal body (remove-guard-holders body world)))
      (error "Missing guard-free logical body for ~s" name))
    (list name (arity name world) (getpropc name 'formals :missing world) body)))

(defun silmaril-export-recursive (name helpers calls output commit tree source-sha)
  (let* ((world (w *the-live-state*))
         (justification (getpropc name 'justification nil world)))
    (unless justification (error "Missing justification for ~s" name))
    (with-open-file (out output :direction :output :if-exists :error :external-format :utf-8)
      (write-char #\( out)
      (dolist (datum
               (append (list "silmaril-acl2-recursive-v1" commit tree source-sha
                             (silmaril-definition name world))
                       (mapcar (lambda (helper) (silmaril-definition helper world)) helpers)
                       (list (access justification justification :measure)
                             (access justification justification :mp)
                             (access justification justification :rel)
                             (mapcar (lambda (fn) (list fn (arity fn world))) calls))))
        (silmaril-write-export datum out)
        (format out "~% "))
      (format out ")~%"))))
