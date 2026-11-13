;; An async export (stackful ABI) that returns at once with task.return.
(module
  (import "[export]$root" "[task-return]add" (func $task_return (param i32)))
  (func (export "[async-lift-stackful]add") (param i32 i32)
    (call $task_return (i32.add (local.get 0) (local.get 1))))
)
