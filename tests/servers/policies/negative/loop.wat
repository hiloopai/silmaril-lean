  ;; Negative case (d), after common.wat: the handler never returns (and never answers).
  ;; Divergence is not observable; the runner records a bounded timeout.
  (func (export "wasi:http/incoming-handler@0.2.12#handle") (param $r i32) (param $o i32)
    (loop $l (br $l)))
