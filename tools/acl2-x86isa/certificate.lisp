;;; Run in the pinned ACL2 image after including the audited book.
(in-package "ACL2")

(defun c1-dependency-rows (phase entries output state)
  (dolist (entry entries)
    (let* ((local (eq (car entry) 'local))
           (book (if local (cadr entry) entry))
           (annotations (fourth book)))
      (format output "~a~c~a~c~a~c~a~c~a~c~{~a~^,~}~%"
              phase #\Tab (if local "local-only" "visible") #\Tab
              (book-name-to-filename (car book) (w state) 'c1-audit) #\Tab
              (cdr (assoc :skipped-proofsp annotations)) #\Tab
              (cdr (assoc :axiomsp annotations)) #\Tab
              (mapcar #'car (cdr (assoc :ttags annotations)))))))

(defun c1-world-sample (path expansions world)
  (with-open-file (out path :direction :output :if-exists :supersede)
    (let ((*package* (find-package "KEYWORD"))
          (*print-circle* t)
          (*print-pretty* nil))
      (format out "; ACL2 world properties. The body and theorem are translated terms.~%")
      (format out "; Certificate expansion entries for this root: ~d~%" (length expansions))
      (dolist (entry '(("X86-RUN" unnormalized-body)
                       ("X86-FETCH-DECODE-EXECUTE" unnormalized-body)
                       ("ONE-BYTE-OPCODE-EXECUTE" unnormalized-body)
                       ("CREATE-UNDEF" constraint-lst-etc)
                       ("X86-RUN-HALTED" theorem)))
        (destructuring-bind (name required-property) entry
          (let ((symbol (find-symbol name "X86ISA")))
            (unless (and symbol (getpropc symbol required-property nil world))
              (error "Missing ~a for world symbol ~a" required-property name))
            (write (cons symbol
                         (loop for property in '(formals unnormalized-body guard stobjs-in stobjs-out
                                                 symbol-class justification constraint-lst-etc theorem)
                               for term = (getpropc symbol property :absent world)
                               unless (eq term :absent) collect (cons property term)))
                   :stream out :readably t)
            (terpri out)))))))

(defun c1-certificate-evidence (source state)
  (let ((live (global-val 'include-book-alist (w state))))
    (unless (member source live :test #'equal
                    :key (lambda (entry)
                           (book-name-to-filename (car entry) (w state) 'c1-audit)))
      (error "Book was not included in the live world: ~a" book))
    (mv-let (channel certificate state)
      (certificate-file-and-input-channel1 source t state)
      (unless channel (error "Missing certificate ~a" certificate))
      (mv-let (erp fields state)
        (with-reckless-readtable
         (mv-let (erp commands state)
           (get-cmds-from-portcullis1 nil channel 'c1-audit state nil)
           (declare (ignore commands))
           (if erp
               (mv erp nil state)
             (read-file-into-template '(:expansion-alist :cert-data nil nil nil :pcert-info)
                                      channel state nil))))
        (close-input-channel channel state)
        (when erp (error "Could not read ACL2 certificate ~a (~a)" certificate erp))
        (destructuring-bind (expansions cert-data pre post checksum pcert-info) fields
          (declare (ignore cert-data checksum))
          (unless (and (not pcert-info) (include-book-alistp pre nil)
                       (include-book-alistp post t) post
                       (equal (book-name-to-filename (caar post) (w state) 'c1-audit) source))
            (error "Expected a completed ACL2 certificate for ~a" source))
          (values expansions pre post live))))))

(defun c1-audit (book dependencies sample)
  (let ((state *the-live-state*))
    (multiple-value-bind (expansions pre post live)
        (c1-certificate-evidence (concatenate 'string book ".lisp") state)
      (with-open-file (out dependencies :direction :output :if-exists :supersede)
        (c1-dependency-rows "pre" pre out state)
        (c1-dependency-rows "post" post out state)
        (c1-dependency-rows "live" live out state))
      (c1-world-sample sample expansions (w state)))))
