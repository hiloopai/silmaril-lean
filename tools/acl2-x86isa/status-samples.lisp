; These observations use only the logical record operations and guards are off.
(set-guard-checking :none)
(assign c3-status-samples
  (let* ((empty (x86isa::create-x86$a))
         (ms-only (x86isa::!ms$a 40 empty))
         (both (x86isa::!fault$a 42 ms-only))
         (wrong-order '((((:ms) . 40) ((:fault) . 42))))
         (bad-tail '((((:fault) . 19) ((:ms) . 17)) . :bad)))
    (list
     (list :empty empty (x86isa::x86$ap empty) (x86isa::ms$a empty) (x86isa::fault$a empty))
     (list :both both (x86isa::x86$ap both) (x86isa::ms$a both) (x86isa::fault$a both))
     (list :ms-only ms-only (x86isa::x86$ap ms-only) (x86isa::ms$a ms-only) (x86isa::fault$a ms-only))
     (list :atom :bad (x86isa::x86$ap :bad) (x86isa::ms$a :bad) (x86isa::fault$a :bad))
     (list :wrong-order wrong-order (x86isa::x86$ap wrong-order)
           (x86isa::ms$a wrong-order) (x86isa::fault$a wrong-order))
     (list :bad-tail bad-tail (x86isa::x86$ap bad-tail)
           (x86isa::ms$a bad-tail) (x86isa::fault$a bad-tail)))))
