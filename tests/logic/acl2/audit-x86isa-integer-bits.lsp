; Read-only call and measure audit of certified ACL2 8.7 machine/x86 dependencies.
(in-package "ACL2")
(include-book "projects/x86isa/machine/instructions/and-spec" :dir :system :uncertified-okp nil)
(include-book "projects/x86isa/machine/instructions/xor-spec" :dir :system :uncertified-okp nil)
(include-book "projects/x86isa/machine/instructions/shifts-spec" :dir :system :uncertified-okp nil)
(include-book "projects/x86isa/machine/register-readers-and-writers" :dir :system :uncertified-okp nil)
(include-book "projects/x86isa/machine/application-level-memory" :dir :system :uncertified-okp nil)
:q
(in-package "ACL2")

(defun silmaril-qualified (symbol)
  (format nil "~a::~a" (symbol-package-name symbol) (symbol-name symbol)))

(defun silmaril-print-calls (name property calls)
  (format t "~&ACL2-USES ~a ~a~{ ~a~}~%" name property
          (sort (mapcar #'silmaril-qualified calls) #'string<)))

(let* ((world (w *the-live-state*))
       (sample '("GPR-AND-SPEC-1$INLINE" "GPR-XOR-SPEC-1$INLINE" "SHLX-SPEC-32"
                 "VEX-VVVV-REG-INDEX" "RVM16$INLINE" "GENERAL-PF-SPEC-FN$INLINE" "BITCOUNT8$INLINE")))
  (dolist (symbol '(binary-logand binary-logior binary-logxor lognot ash logbitp integer-length
                    logand logior logxor integerp binary-+))
    (format t "~&ACL2-KIND ~a ~a~%" (silmaril-qualified symbol)
            (cond ((assoc symbol *primitive-formals-and-guards*) :primitive)
                  ((getpropc symbol 'macro-body nil world) :macro)
                  ((getpropc symbol 'unnormalized-body nil world) :defined)
                  (t (error "Missing ACL2 declaration for ~a" symbol)))))
  (dolist (name sample)
    (let* ((symbol (find-symbol name "X86ISA"))
           (body (and symbol (getpropc symbol 'unnormalized-body nil world)))
           (justification (and body (getpropc symbol 'justification nil world))))
      (unless (and body (not (eq (getpropc symbol 'symbol-class nil world) :program)))
        (error "Missing logical body for ~a" name))
      (silmaril-print-calls (silmaril-qualified symbol) "body"
                            (all-fnnames (remove-guard-holders body world)))
      (when justification
        (silmaril-print-calls (silmaril-qualified symbol) "measure"
                              (all-fnnames (access justification justification :measure)))))))
(sb-ext:exit)
