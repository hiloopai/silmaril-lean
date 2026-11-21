(module
  (type $pair (func (param i32) (result i32 i32)))
  (type $rec (func (param i32) (result i32)))
  (type $choose (func (param i32) (result i64 i32 i32)))
  (global (export "log") (mut i32) (i32.const 0))
  (func $record (type $rec) (param i32) (result i32)
    global.get 0
    i32.const 10
    i32.mul
    local.get 0
    i32.add
    global.set 0
    local.get 0)
  (func (export "choose") (type $choose) (param i32) (result i64 i32 i32)
    i64.const 99
    i32.const 4
    local.get 0
    if (type $pair)
      call $record
      i32.const 5
      call $record
    else
      i32.const 7
    end))
(assert_return (invoke "choose" (i32.const 0)) (i64.const 99) (i32.const 4) (i32.const 7))
(assert_return (get "log") (i32.const 0))
(assert_return (invoke "choose" (i32.const 1)) (i64.const 99) (i32.const 4) (i32.const 5))
(assert_return (get "log") (i32.const 45))
