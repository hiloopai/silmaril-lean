(in-package "X86ISA")

(defthm c3-rwx-floor-mod
  (implies (unsigned-byte-p 46 key)
           (equal (tlb-key->r-w-x key) (mod (floor key 64) 4)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory '(tlb-key->r-w-x$inline tlb-key-p tlb-key-fix-when-tlb-key-p
                        bitops::part-select-width-low$inline acl2::loghead$inline acl2::logtail$inline
                        acl2::ifloor$inline acl2::imod$inline acl2::expt2$inline
                        (:executable-counterpart expt) (:executable-counterpart acl2::nfix)
                        (:definition acl2::ifix) unsigned-byte-p acl2::integer-range-p
                        (:type-prescription floor)))))

(in-package "ACL2")
(set-guard-checking :none)

(defun c3-tlb-arithmetic-sample (n d)
  (list n d (nonnegative-integer-quotient n d) (floor n d) (mod n d)))

(assign c3-tlb-arithmetic-samples
  (list (c3-tlb-arithmetic-sample 0 64) (c3-tlb-arithmetic-sample 17 0)
        (c3-tlb-arithmetic-sample 63 64) (c3-tlb-arithmetic-sample 64 64)
        (c3-tlb-arithmetic-sample 65 64) (c3-tlb-arithmetic-sample 192 64)
        (c3-tlb-arithmetic-sample 193 64) (c3-tlb-arithmetic-sample 7 4)
        (c3-tlb-arithmetic-sample 5 1) (c3-tlb-arithmetic-sample -193 64)
        (c3-tlb-arithmetic-sample -192 64) (c3-tlb-arithmetic-sample -17 0)))

(defun c3-tlb-key-sample (key)
  (list key (x86isa::tlb-key-p key) (x86isa::good-tlb-key-p key)
        (if (x86isa::tlb-key-p key) (x86isa::tlb-key->r-w-x key) nil)))

(assign c3-tlb-key-samples
  (list (c3-tlb-key-sample -1) (c3-tlb-key-sample 1/2) (c3-tlb-key-sample :bad)
        (c3-tlb-key-sample '(0)) (c3-tlb-key-sample 0) (c3-tlb-key-sample 63)
        (c3-tlb-key-sample 64) (c3-tlb-key-sample 128) (c3-tlb-key-sample 191)
        (c3-tlb-key-sample 192) (c3-tlb-key-sample 255) (c3-tlb-key-sample 256)
        (c3-tlb-key-sample (- (expt 2 46) 65)) (c3-tlb-key-sample (- (expt 2 46) 1))
        (c3-tlb-key-sample (expt 2 46))))

(defun c3-tlb-sample (buffer)
  (let* ((env '((:file-descriptors) (:file-contents) (:oracle (0 :ok))))
         (entries (list (cons '(:env) env) '((:fault) . 42) '((:ms) . 40) (cons '(:tlb) buffer)))
         (state (cons entries nil)))
    (list buffer (x86isa::tlbp buffer) entries (x86isa::x86rec-p1 entries)
          (x86isa::x86$ap state) (x86isa::ms$a state) (x86isa::fault$a state))))

(assign c3-tlb-samples
  (list (c3-tlb-sample :tlb) (c3-tlb-sample 'tlb) (c3-tlb-sample nil)
        (c3-tlb-sample '((0 . 0) . :tlb)) (c3-tlb-sample '((128 . 1099511627775) (0 . 1) . :tlb))
        (c3-tlb-sample '((0 . 1099511627776) . :tlb)) (c3-tlb-sample '((0 . -1) . :tlb))
        (c3-tlb-sample '((0 . 1/2) . :tlb)) (c3-tlb-sample '((192 . 1) . :tlb))
        (c3-tlb-sample '((1/2 . 1) . :tlb)) (c3-tlb-sample '((0 . 1)))
        (c3-tlb-sample '(17 . :tlb))))
