;; Async exports of an interface (stackful), one with a record result through task.return.
;; The memory is not needed by the canonical ABI here (the record is passed flat to task.return),
;; but wit-component 0.262 requires it.
(module
  (import "[export]test:ia/svc" "[task-return]get" (func $ret_get (param i32)))
  (import "[export]test:ia/svc" "[task-return]pt" (func $ret_pt (param i32 i32)))
  (memory (export "memory") 1)
  (func (export "[async-lift-stackful]test:ia/svc#get") (param i32)
    (call $ret_get (i32.mul (local.get 0) (i32.const 10))))
  (func (export "[async-lift-stackful]test:ia/svc#pt") (param i32)
    (call $ret_pt (local.get 0) (i32.add (local.get 0) (i32.const 1))))
)
