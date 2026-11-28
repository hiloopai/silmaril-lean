(in-package "ACL2")
; Only logical data, including malformed objects, are evaluated here.
(set-guard-checking :none)

(defun c3-environment-sample (label env)
  (let* ((entries (list (cons '(:env) env) '((:fault) . 42) '((:ms) . 40)))
         (record (cons entries nil)))
    (list label env (x86isa::env-alistp env) entries (x86isa::x86rec-p1 entries)
          (x86isa::x86$ap record) (x86isa::ms$a record) (x86isa::fault$a record))))

(assign c3-environment-samples
  (list (c3-environment-sample :nil nil)
        (c3-environment-sample :atom 7)
        (c3-environment-sample :empty-fields '((:file-descriptors) (:file-contents) (:oracle)))
        (c3-environment-sample :permuted '((:oracle (-3 :ok)) (:file-contents (1 . "data"))
                                           (:file-descriptors (:fd . t))))
        (c3-environment-sample :signed-limits
          '((:file-descriptors) (:file-contents) (:oracle (-140737488355328) (140737488355327 :ok))))
        (c3-environment-sample :below-signed-limit
          '((:file-descriptors) (:file-contents) (:oracle (-140737488355329 :bad))))
        (c3-environment-sample :above-signed-limit
          '((:file-descriptors) (:file-contents) (:oracle (140737488355328 :bad))))
        (c3-environment-sample :noninteger-address
          '((:file-descriptors) (:file-contents) (:oracle (1/2 :bad))))
        (c3-environment-sample :dotted-oracle-result
          '((:file-descriptors) (:file-contents) (:oracle (1 . :bad))))
        (c3-environment-sample :dotted-oracle
          '((:file-descriptors) (:file-contents) (:oracle (1) . :bad)))
        (c3-environment-sample :bad-file-contents '((:file-descriptors) (:file-contents :bad) (:oracle)))
        (c3-environment-sample :dotted-descriptors '((:file-descriptors (:fd) . :bad) (:file-contents) (:oracle)))
        (c3-environment-sample :duplicate '((:file-descriptors) (:file-descriptors) (:oracle)))
        (c3-environment-sample :wrong-package '((file-descriptors) (:file-contents) (:oracle)))
        (c3-environment-sample :extra '((:file-descriptors) (:file-contents) (:oracle) (:extra)))
        (c3-environment-sample :dotted-environment '((:file-descriptors) (:file-contents) (:oracle) . :bad))))

(defun c3-environment-helper-sample (key obj)
  (list key obj (assoc-equal key obj) (len obj) (alistp obj) (true-listp obj)
        (x86isa::rip-ret-alistp obj)))

(assign c3-environment-helper-samples
  (list (c3-environment-helper-sample nil '(:atom (nil . 8)))
        (c3-environment-helper-sample :a '((:a . 1) (:a . 2) . :bad))
        (c3-environment-helper-sample :absent '((:a . 1) . :bad))
        (c3-environment-helper-sample :absent :bad)
        (c3-environment-helper-sample 1 '((1 :a) (1 :b)))
        (c3-environment-helper-sample :absent nil)))
