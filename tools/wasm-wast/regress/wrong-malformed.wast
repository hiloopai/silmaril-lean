;; `gen.py regress`: a deliberately wrong `assert_malformed` (the bytes are the empty module).
;; wasmtime must reject this file, on the line marked WRONG.
(assert_malformed (module binary "\00asm" "\02\00\00\00") "unknown binary version")
(assert_malformed (module binary "\00asm" "\01\00\00\00") "unknown binary version") ;; WRONG
