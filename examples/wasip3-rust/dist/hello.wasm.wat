(component
  (type $ty-wasi:cli/types@0.3.0 (;0;)
    (instance
      (type (;0;) (enum "io" "illegal-byte-sequence" "pipe"))
      (export (;1;) "error-code" (type (eq 0)))
    )
  )
  (import "wasi:cli/types@0.3.0" (instance $wasi:cli/types@0.3.0 (;0;) (type $ty-wasi:cli/types@0.3.0)))
  (alias export $wasi:cli/types@0.3.0 "error-code" (type $error-code (;1;)))
  (type $ty-wasi:cli/stdin@0.3.0 (;2;)
    (instance
      (alias outer 1 $error-code (type (;0;)))
      (export (;1;) "error-code" (type (eq 0)))
    )
  )
  (import "wasi:cli/stdin@0.3.0" (instance $wasi:cli/stdin@0.3.0 (;1;) (type $ty-wasi:cli/stdin@0.3.0)))
  (alias export $wasi:cli/types@0.3.0 "error-code" (type $"#type3 error-code" (@name "error-code") (;3;)))
  (type $ty-wasi:cli/stdout@0.3.0 (;4;)
    (instance
      (alias outer 1 $"#type3 error-code" (type (;0;)))
      (export (;1;) "error-code" (type (eq 0)))
      (type (;2;) (stream u8))
      (type (;3;) (result (error 1)))
      (type (;4;) (future 3))
      (type (;5;) (func (param "data" 2) (result 4)))
      (export (;0;) "write-via-stream" (func (type 5)))
    )
  )
  (import "wasi:cli/stdout@0.3.0" (instance $wasi:cli/stdout@0.3.0 (;2;) (type $ty-wasi:cli/stdout@0.3.0)))
  (core module $main (;0;)
    (type (;0;) (func (param i32 i32) (result i32)))
    (type (;1;) (func (param i32)))
    (type (;2;) (func (param i32) (result i32)))
    (type (;3;) (func (param i32 i32)))
    (type (;4;) (func (param i32 i32 i32 i32) (result i32)))
    (type (;5;) (func (param i32 i32 i32) (result i32)))
    (type (;6;) (func (result i32)))
    (type (;7;) (func))
    (type (;8;) (func (result i64)))
    (type (;9;) (func (param i32 i32 i32 i32 i32)))
    (type (;10;) (func (param i32 i32 i32)))
    (type (;11;) (func (param i32 i32 i32 i32)))
    (type (;12;) (func (param i32 i32 i32 i32 i32 i32)))
    (import "$root" "[context-get-0]" (func $_RNvNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10task_state3get3get (;0;) (type 6) (result i32)))
    (import "$root" "[context-set-0]" (func $_RNvNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10task_state3set3set (;1;) (type 1) (param i32)))
    (import "[export]$root" "[task-cancel]" (func $_RNvNvXs6_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB7_16TaskCancelOnDropNtNtNtCshQUFA83YM6w_4core3ops4drop4Drop4drop6cancel (;2;) (type 7)))
    (import "wasi:cli/stdin@0.3.0" "[stream-new-0]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports3new (;3;) (type 8) (result i64)))
    (import "wasi:cli/stdout@0.3.0" "write-via-stream" (func $_RNvNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli6stdout16write_via_stream11wit_import0 (;4;) (type 2) (param i32) (result i32)))
    (import "[export]wasi:cli/run@0.3.0" "[task-return]run" (func $_RNvNCNvNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run16__export_run_cabi011wit_import2 (;5;) (type 1) (param i32)))
    (import "wasi:cli/stdin@0.3.0" "[async-lower][future-write-1]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports11start_write (;6;) (type 0) (param i32 i32) (result i32)))
    (import "wasi:cli/stdin@0.3.0" "[async-lower][future-read-1]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports10start_read (;7;) (type 0) (param i32 i32) (result i32)))
    (import "wasi:cli/stdin@0.3.0" "[future-cancel-write-1]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports12cancel_write (;8;) (type 2) (param i32) (result i32)))
    (import "wasi:cli/stdin@0.3.0" "[future-cancel-read-1]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports11cancel_read (;9;) (type 2) (param i32) (result i32)))
    (import "wasi:cli/stdin@0.3.0" "[future-drop-writable-1]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports13drop_writable (;10;) (type 1) (param i32)))
    (import "wasi:cli/stdin@0.3.0" "[future-drop-readable-1]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports13drop_readable (;11;) (type 1) (param i32)))
    (import "wasi:cli/stdin@0.3.0" "[future-new-1]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports3new (;12;) (type 8) (result i64)))
    (import "wasi:cli/stdin@0.3.0" "[async-lower][stream-write-0]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports11start_write (;13;) (type 5) (param i32 i32 i32) (result i32)))
    (import "wasi:cli/stdin@0.3.0" "[async-lower][stream-read-0]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports10start_read (;14;) (type 5) (param i32 i32 i32) (result i32)))
    (import "wasi:cli/stdin@0.3.0" "[stream-cancel-write-0]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports12cancel_write (;15;) (type 2) (param i32) (result i32)))
    (import "wasi:cli/stdin@0.3.0" "[stream-cancel-read-0]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports11cancel_read (;16;) (type 2) (param i32) (result i32)))
    (import "wasi:cli/stdin@0.3.0" "[stream-drop-writable-0]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports13drop_writable (;17;) (type 1) (param i32)))
    (import "wasi:cli/stdin@0.3.0" "[stream-drop-readable-0]read-via-stream" (func $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports13drop_readable (;18;) (type 1) (param i32)))
    (import "$root" "[waitable-set-drop]" (func $_RNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12waitable_set4drop (;19;) (type 1) (param i32)))
    (import "$root" "[waitable-set-new]" (func $_RNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12waitable_set3new (;20;) (type 6) (result i32)))
    (import "$root" "[waitable-join]" (func $_RNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12waitable_set4join (;21;) (type 3) (param i32 i32)))
    (import "$root" "[waitable-set-poll]" (func $_RNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12waitable_set4poll (;22;) (type 0) (param i32 i32) (result i32)))
    (table (;0;) 29 29 funcref)
    (memory (;0;) 17)
    (global $__stack_pointer (;0;) (mut i32) i32.const 1048576)
    (global $__memory_base (;1;) i32 i32.const 0)
    (global $__table_base (;2;) i32 i32.const 1)
    (export "memory" (memory 0))
    (export "[async-lift]wasi:cli/run@0.3.0#run" (func $"[async-lift]wasi:cli/run@0.3.0#run"))
    (export "[callback][async-lift]wasi:cli/run@0.3.0#run" (func $"[callback][async-lift]wasi:cli/run@0.3.0#run"))
    (export "cabi_realloc" (func $cabi_realloc))
    (elem (;0;) (i32.const 1) func $_RNvMs1_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB5_15SharedTaskState24cabi_waitable_unregister $_RNvMs1_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB5_15SharedTaskState22cabi_waitable_register $_RNvNvMs2_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitableINtB7_17WaitableOperationpE14register_waker9cabi_wake $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueNCINvNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run16__export_run_cabiNtCsgR5kJmH8IIE_5hello5HelloE0EB1Z_ $_RNCINvNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run16__export_run_cabiNtCsgR5kJmH8IIE_5hello5HelloE0B1n_ $_RNvNtCs8o6ThntBNTu_6wasip37command40___link_custom_section_describing_imports $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable05lower $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable013dealloc_lists $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable04lift $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable011start_write $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable010start_read $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable012cancel_write $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable011cancel_read $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable013drop_writable $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable013drop_readable $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable03new $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable011start_write $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable010start_read $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable012cancel_write $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable011cancel_read $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable013drop_writable $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable013drop_readable $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable03new $_RNvMs1_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB5_15SharedTaskState10cabi_clone $_RINvNvNtCsiqQVI2xHy0t_5alloc4task9raw_waker10drop_wakerNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support15SharedTaskStateEBX_ $_RINvNvNtCsiqQVI2xHy0t_5alloc4task9raw_waker11clone_wakerNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support15SharedTaskStateEBY_ $_RINvNvNtCsiqQVI2xHy0t_5alloc4task9raw_waker4wakeNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support15SharedTaskStateEBQ_ $_RINvNvNtCsiqQVI2xHy0t_5alloc4task9raw_waker11wake_by_refNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support15SharedTaskStateEBY_)
    (func $__wasm_call_ctors (;23;) (type 7))
    (func $"[async-lift]wasi:cli/run@0.3.0#run" (;24;) (type 6) (result i32)
      (local i32 i32 i32)
      block ;; label = @1
        global.get $__memory_base
        i32.const 1049301
        i32.add
        i32.load8_u
        br_if 0 (;@1;)
        global.get $__memory_base
        local.set 0
        call $__wasm_call_ctors
        local.get 0
        i32.const 1049301
        i32.add
        i32.const 1
        i32.store8
      end
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            i32.const 244
            call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCskAuRjb5C0Ki_4p3rt
            local.tee 1
            i32.eqz
            br_if 0 (;@3;)
            local.get 1
            i32.const 0
            i32.store8 offset=240
            i32.const 36
            call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCskAuRjb5C0Ki_4p3rt
            local.tee 0
            i32.eqz
            br_if 0 (;@3;)
            local.get 0
            i32.const 0
            i32.store offset=32
            local.get 0
            i64.const 0
            i64.store offset=24 align=4
            local.get 0
            i32.const 0
            i32.store8 offset=20
            local.get 0
            i32.const 0
            i32.store offset=16
            local.get 0
            i32.const 0
            i32.store offset=8
            local.get 0
            i64.const 4294967298
            i64.store align=4
            i32.const 1
            i32.eqz
            br_if 1 (;@2;)
            i32.const 20
            call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCskAuRjb5C0Ki_4p3rt
            local.tee 2
            i32.eqz
            br_if 0 (;@3;)
            local.get 2
            local.get 1
            i32.store offset=12
            local.get 2
            local.get 0
            i32.const 8
            i32.add
            i32.store offset=8
            local.get 2
            local.get 0
            i32.store
            local.get 2
            global.get $__memory_base
            local.tee 0
            i32.const 1048596
            i32.add
            i32.store offset=16
            local.get 2
            local.get 0
            i32.const 1049284
            i32.add
            i32.store offset=4
            call $_RNvNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10task_state3get3get
            br_if 2 (;@1;)
            local.get 2
            call $_RNvNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10task_state3set3set
            i32.const 0
            i32.const 0
            i32.const 0
            call $_RNvNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8callback
            return
          end
          call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
        end
        unreachable
      end
      i32.const 45
      call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
      unreachable
    )
    (func $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCskAuRjb5C0Ki_4p3rt (;25;) (type 2) (param i32) (result i32)
      (local i32 i32 i32 i32 i32 i32 i32 i32 i64)
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  local.get 0
                  i32.const 245
                  i32.lt_u
                  br_if 0 (;@6;)
                  i32.const 0
                  local.set 1
                  local.get 0
                  i32.const -48
                  global.get $__memory_base
                  i32.const 1048612
                  i32.add
                  i32.load offset=452
                  i32.sub
                  i32.const -9
                  i32.and
                  i32.const -3
                  i32.add
                  local.tee 2
                  i32.const -64
                  local.get 2
                  i32.const -64
                  i32.lt_u
                  select
                  i32.ge_u
                  br_if 5 (;@1;)
                  local.get 0
                  i32.const 11
                  i32.add
                  local.tee 2
                  i32.const -8
                  i32.and
                  local.set 3
                  global.get $__memory_base
                  i32.const 1048612
                  i32.add
                  i32.load offset=412
                  local.tee 4
                  i32.eqz
                  br_if 4 (;@2;)
                  i32.const 31
                  local.set 5
                  block ;; label = @7
                    local.get 0
                    i32.const 16777204
                    i32.gt_u
                    br_if 0 (;@7;)
                    local.get 3
                    i32.const 38
                    local.get 2
                    i32.const 8
                    i32.shr_u
                    i32.clz
                    local.tee 0
                    i32.sub
                    i32.shr_u
                    i32.const 1
                    i32.and
                    local.get 0
                    i32.const 1
                    i32.shl
                    i32.or
                    i32.const 62
                    i32.xor
                    local.set 5
                  end
                  i32.const 0
                  local.get 3
                  i32.sub
                  local.set 2
                  global.get $__memory_base
                  i32.const 1048612
                  i32.add
                  local.get 5
                  i32.const 2
                  i32.shl
                  i32.add
                  i32.load
                  local.tee 0
                  i32.eqz
                  br_if 1 (;@5;)
                  i32.const 0
                  local.set 6
                  local.get 3
                  i32.const 0
                  i32.const 25
                  local.get 5
                  i32.const 1
                  i32.shr_u
                  i32.sub
                  i32.const 31
                  i32.and
                  local.get 5
                  i32.const 31
                  i32.eq
                  select
                  i32.shl
                  local.set 7
                  i32.const 0
                  local.set 1
                  loop ;; label = @7
                    block ;; label = @8
                      local.get 0
                      local.tee 0
                      i32.load offset=4
                      i32.const -8
                      i32.and
                      local.tee 8
                      local.get 3
                      i32.lt_u
                      br_if 0 (;@8;)
                      local.get 8
                      local.get 3
                      i32.sub
                      local.tee 8
                      local.get 2
                      i32.ge_u
                      br_if 0 (;@8;)
                      local.get 0
                      local.set 6
                      local.get 8
                      local.set 2
                      local.get 8
                      br_if 0 (;@8;)
                      i32.const 0
                      local.set 2
                      local.get 0
                      local.set 6
                      br 4 (;@4;)
                    end
                    local.get 1
                    local.get 0
                    i32.load offset=20
                    local.tee 8
                    local.get 8
                    local.get 0
                    local.get 7
                    i32.const 29
                    i32.shr_u
                    i32.const 4
                    i32.and
                    i32.add
                    i32.load offset=16
                    local.tee 0
                    i32.eq
                    select
                    local.get 1
                    local.get 8
                    select
                    local.set 1
                    local.get 7
                    i32.const 1
                    i32.shl
                    local.set 7
                    local.get 0
                    br_if 0 (;@7;)
                  end
                  block ;; label = @7
                    local.get 1
                    i32.eqz
                    br_if 0 (;@7;)
                    local.get 1
                    local.set 0
                    br 3 (;@4;)
                  end
                  local.get 6
                  i32.eqz
                  br_if 1 (;@5;)
                  br 3 (;@3;)
                end
                block ;; label = @6
                  global.get $__memory_base
                  i32.const 1048612
                  i32.add
                  i32.load offset=408
                  local.tee 6
                  i32.const 16
                  local.get 0
                  i32.const 11
                  i32.add
                  i32.const 504
                  i32.and
                  local.get 0
                  i32.const 11
                  i32.lt_u
                  select
                  local.tee 3
                  i32.const 3
                  i32.shr_u
                  local.tee 2
                  i32.shr_u
                  local.tee 0
                  i32.const 3
                  i32.and
                  i32.eqz
                  br_if 0 (;@6;)
                  block ;; label = @7
                    block ;; label = @8
                      global.get $__memory_base
                      i32.const 1048612
                      i32.add
                      local.get 0
                      i32.const -1
                      i32.xor
                      i32.const 1
                      i32.and
                      local.get 2
                      i32.add
                      local.tee 8
                      i32.const 3
                      i32.shl
                      local.tee 0
                      i32.add
                      local.tee 2
                      i32.const 144
                      i32.add
                      local.tee 3
                      local.get 2
                      i32.const 152
                      i32.add
                      i32.load
                      local.tee 2
                      i32.const 8
                      i32.add
                      local.tee 7
                      i32.load
                      local.tee 1
                      i32.eq
                      br_if 0 (;@8;)
                      local.get 1
                      local.get 3
                      i32.store offset=12
                      local.get 3
                      local.get 1
                      i32.store offset=8
                      br 1 (;@7;)
                    end
                    global.get $__memory_base
                    i32.const 1048612
                    i32.add
                    local.get 6
                    i32.const -2
                    local.get 8
                    i32.rotl
                    i32.and
                    i32.store offset=408
                  end
                  local.get 2
                  local.get 0
                  i32.const 3
                  i32.or
                  i32.store offset=4
                  local.get 2
                  local.get 0
                  i32.add
                  local.tee 0
                  local.get 0
                  i32.load offset=4
                  i32.const 1
                  i32.or
                  i32.store offset=4
                  local.get 7
                  return
                end
                local.get 3
                global.get $__memory_base
                i32.const 1048612
                i32.add
                i32.load offset=416
                i32.le_u
                br_if 3 (;@2;)
                block ;; label = @6
                  block ;; label = @7
                    local.get 0
                    br_if 0 (;@7;)
                    global.get $__memory_base
                    i32.const 1048612
                    i32.add
                    i32.load offset=412
                    local.tee 0
                    i32.eqz
                    br_if 5 (;@2;)
                    global.get $__memory_base
                    i32.const 1048612
                    i32.add
                    local.get 0
                    i32.ctz
                    i32.const 2
                    i32.shl
                    i32.add
                    i32.load
                    local.tee 1
                    i32.load offset=4
                    i32.const -8
                    i32.and
                    local.get 3
                    i32.sub
                    local.set 2
                    local.get 1
                    local.set 6
                    loop ;; label = @8
                      block ;; label = @9
                        local.get 1
                        i32.load offset=16
                        local.tee 0
                        br_if 0 (;@9;)
                        local.get 1
                        i32.load offset=20
                        local.tee 0
                        i32.eqz
                        br_if 3 (;@6;)
                      end
                      local.get 0
                      i32.load offset=4
                      i32.const -8
                      i32.and
                      local.get 3
                      i32.sub
                      local.tee 1
                      local.get 2
                      local.get 1
                      local.get 2
                      i32.lt_u
                      local.tee 1
                      select
                      local.set 2
                      local.get 0
                      local.get 6
                      local.get 1
                      select
                      local.set 6
                      local.get 0
                      local.set 1
                      br 0 (;@8;)
                    end
                  end
                  block ;; label = @7
                    block ;; label = @8
                      global.get $__memory_base
                      i32.const 1048612
                      i32.add
                      i32.const 2
                      local.get 2
                      i32.shl
                      local.tee 1
                      i32.const 0
                      local.get 1
                      i32.sub
                      i32.or
                      local.get 0
                      local.get 2
                      i32.shl
                      i32.and
                      i32.ctz
                      local.tee 5
                      i32.const 3
                      i32.shl
                      local.tee 2
                      i32.add
                      local.tee 0
                      i32.const 144
                      i32.add
                      local.tee 1
                      local.get 0
                      i32.const 152
                      i32.add
                      i32.load
                      local.tee 0
                      i32.const 8
                      i32.add
                      local.tee 8
                      i32.load
                      local.tee 7
                      i32.eq
                      br_if 0 (;@8;)
                      local.get 7
                      local.get 1
                      i32.store offset=12
                      local.get 1
                      local.get 7
                      i32.store offset=8
                      br 1 (;@7;)
                    end
                    global.get $__memory_base
                    i32.const 1048612
                    i32.add
                    local.get 6
                    i32.const -2
                    local.get 5
                    i32.rotl
                    i32.and
                    i32.store offset=408
                  end
                  local.get 0
                  local.get 3
                  i32.const 3
                  i32.or
                  i32.store offset=4
                  local.get 0
                  local.get 2
                  i32.add
                  local.get 2
                  local.get 3
                  i32.sub
                  local.tee 2
                  i32.store
                  local.get 0
                  local.get 3
                  i32.add
                  local.tee 0
                  local.get 2
                  i32.const 1
                  i32.or
                  i32.store offset=4
                  local.get 0
                  local.get 2
                  call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE10replace_dvCskAuRjb5C0Ki_4p3rt
                  local.get 8
                  return
                end
                local.get 6
                call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE18unlink_large_chunkCskAuRjb5C0Ki_4p3rt
                block ;; label = @6
                  block ;; label = @7
                    local.get 2
                    i32.const 16
                    i32.lt_u
                    br_if 0 (;@7;)
                    local.get 6
                    local.get 3
                    i32.const 3
                    i32.or
                    i32.store offset=4
                    local.get 6
                    local.get 3
                    i32.add
                    local.tee 0
                    local.get 2
                    i32.const 1
                    i32.or
                    i32.store offset=4
                    local.get 0
                    local.get 2
                    i32.add
                    local.get 2
                    i32.store
                    local.get 0
                    local.get 2
                    call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE10replace_dvCskAuRjb5C0Ki_4p3rt
                    br 1 (;@6;)
                  end
                  local.get 6
                  local.get 2
                  local.get 3
                  i32.add
                  local.tee 0
                  i32.const 3
                  i32.or
                  i32.store offset=4
                  local.get 6
                  local.get 0
                  i32.add
                  local.tee 0
                  local.get 0
                  i32.load offset=4
                  i32.const 1
                  i32.or
                  i32.store offset=4
                end
                local.get 6
                i32.const 8
                i32.add
                local.tee 1
                i32.eqz
                br_if 3 (;@2;)
                br 4 (;@1;)
              end
              i32.const 0
              local.set 6
              local.get 4
              i32.const 2
              local.get 5
              i32.shl
              local.tee 0
              i32.const 0
              local.get 0
              i32.sub
              i32.or
              i32.and
              local.tee 0
              i32.eqz
              br_if 2 (;@2;)
              global.get $__memory_base
              i32.const 1048612
              i32.add
              local.get 0
              i32.ctz
              i32.const 2
              i32.shl
              i32.add
              i32.load
              local.tee 0
              i32.eqz
              br_if 2 (;@2;)
            end
            loop ;; label = @4
              local.get 0
              i32.load offset=4
              i32.const -8
              i32.and
              local.tee 7
              local.get 3
              i32.sub
              local.tee 1
              local.get 2
              local.get 1
              local.get 2
              i32.lt_u
              select
              local.set 8
              local.get 7
              local.get 3
              i32.lt_u
              local.set 7
              local.get 6
              local.get 0
              local.get 1
              local.get 2
              i32.ge_u
              select
              local.set 5
              block ;; label = @5
                local.get 0
                i32.load offset=16
                local.tee 1
                br_if 0 (;@5;)
                local.get 0
                i32.load offset=20
                local.set 1
              end
              local.get 2
              local.get 8
              local.get 7
              select
              local.set 2
              local.get 6
              local.get 5
              local.get 7
              select
              local.set 6
              local.get 1
              local.set 0
              local.get 1
              br_if 0 (;@4;)
            end
            local.get 6
            i32.eqz
            br_if 1 (;@2;)
          end
          block ;; label = @3
            global.get $__memory_base
            i32.const 1048612
            i32.add
            i32.load offset=416
            local.tee 0
            local.get 3
            i32.lt_u
            br_if 0 (;@3;)
            local.get 2
            local.get 0
            local.get 3
            i32.sub
            i32.ge_u
            br_if 1 (;@2;)
          end
          local.get 6
          call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE18unlink_large_chunkCskAuRjb5C0Ki_4p3rt
          block ;; label = @3
            block ;; label = @4
              local.get 2
              i32.const 16
              i32.lt_u
              br_if 0 (;@4;)
              local.get 6
              local.get 3
              i32.const 3
              i32.or
              i32.store offset=4
              local.get 6
              local.get 3
              i32.add
              local.tee 0
              local.get 2
              i32.const 1
              i32.or
              i32.store offset=4
              local.get 0
              local.get 2
              i32.add
              local.get 2
              i32.store
              local.get 0
              local.get 2
              call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12insert_chunkCskAuRjb5C0Ki_4p3rt
              br 1 (;@3;)
            end
            local.get 6
            local.get 2
            local.get 3
            i32.add
            local.tee 0
            i32.const 3
            i32.or
            i32.store offset=4
            local.get 6
            local.get 0
            i32.add
            local.tee 0
            local.get 0
            i32.load offset=4
            i32.const 1
            i32.or
            i32.store offset=4
          end
          local.get 6
          i32.const 8
          i32.add
          local.tee 1
          br_if 1 (;@1;)
        end
        block ;; label = @2
          block ;; label = @3
            global.get $__memory_base
            i32.const 1048612
            i32.add
            i32.load offset=416
            local.tee 0
            local.get 3
            i32.ge_u
            br_if 0 (;@3;)
            block ;; label = @4
              global.get $__memory_base
              i32.const 1048612
              i32.add
              i32.load offset=420
              local.tee 0
              local.get 3
              i32.gt_u
              br_if 0 (;@4;)
              i32.const 0
              local.set 1
              local.get 3
              global.get $__memory_base
              i32.const 1048612
              i32.add
              i32.load offset=452
              local.tee 0
              i32.add
              i32.const 47
              i32.add
              i32.const 0
              local.get 0
              i32.sub
              i32.and
              local.tee 0
              i32.eqz
              br_if 2 (;@2;)
              global.get $__memory_base
              i32.const 1049300
              i32.add
              i32.const 1
              i32.store8
              br 2 (;@2;)
            end
            global.get $__memory_base
            i32.const 1048612
            i32.add
            local.tee 2
            local.get 0
            local.get 3
            i32.sub
            local.tee 1
            i32.store offset=420
            local.get 2
            local.get 2
            i32.load offset=428
            local.tee 0
            local.get 3
            i32.add
            local.tee 6
            i32.store offset=428
            local.get 6
            local.get 1
            i32.const 1
            i32.or
            i32.store offset=4
            local.get 0
            local.get 3
            i32.const 3
            i32.or
            i32.store offset=4
            local.get 0
            i32.const 8
            i32.add
            local.set 1
            br 2 (;@1;)
          end
          global.get $__memory_base
          i32.const 1048612
          i32.add
          i32.load offset=424
          local.set 2
          block ;; label = @3
            block ;; label = @4
              local.get 0
              local.get 3
              i32.sub
              local.tee 1
              i32.const 16
              i32.lt_u
              br_if 0 (;@4;)
              global.get $__memory_base
              i32.const 1048612
              i32.add
              local.tee 6
              local.get 1
              i32.store offset=416
              local.get 6
              local.get 2
              local.get 3
              i32.add
              local.tee 7
              i32.store offset=424
              local.get 7
              local.get 1
              i32.const 1
              i32.or
              i32.store offset=4
              local.get 2
              local.get 0
              i32.add
              local.get 1
              i32.store
              local.get 2
              local.get 3
              i32.const 3
              i32.or
              i32.store offset=4
              br 1 (;@3;)
            end
            global.get $__memory_base
            i32.const 1048612
            i32.add
            local.tee 3
            i32.const 0
            i32.store offset=424
            local.get 3
            i32.const 0
            i32.store offset=416
            local.get 2
            local.get 0
            i32.const 3
            i32.or
            i32.store offset=4
            local.get 2
            local.get 0
            i32.add
            local.tee 0
            local.get 0
            i32.load offset=4
            i32.const 1
            i32.or
            i32.store offset=4
          end
          local.get 2
          i32.const 8
          i32.add
          return
        end
        local.get 0
        i32.const 16
        i32.shr_u
        local.get 0
        i32.const 65535
        i32.and
        i32.const 0
        i32.ne
        i32.add
        local.tee 2
        memory.grow
        local.tee 0
        i32.const -1
        i32.eq
        br_if 0 (;@1;)
        i32.const 0
        local.set 1
        local.get 0
        i32.const 16
        i32.shl
        local.tee 7
        i32.eqz
        br_if 0 (;@1;)
        global.get $__memory_base
        i32.const 1048612
        i32.add
        local.tee 0
        local.get 0
        i32.load offset=432
        local.get 2
        i32.const 16
        i32.shl
        local.tee 2
        i32.const -16
        i32.add
        local.get 2
        local.get 7
        i32.const 0
        local.get 2
        i32.sub
        i32.eq
        select
        local.tee 5
        i32.add
        local.tee 2
        i32.store offset=432
        local.get 0
        local.get 2
        local.get 0
        i32.load offset=436
        local.tee 6
        local.get 2
        local.get 6
        i32.gt_u
        select
        i32.store offset=436
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  block ;; label = @7
                    block ;; label = @8
                      block ;; label = @9
                        block ;; label = @10
                          block ;; label = @11
                            local.get 0
                            i32.load offset=428
                            local.tee 2
                            i32.eqz
                            br_if 0 (;@11;)
                            global.get $__memory_base
                            i32.const 1048612
                            i32.add
                            i32.const 128
                            i32.add
                            local.set 0
                            loop ;; label = @12
                              local.get 0
                              i32.load
                              local.tee 6
                              local.get 0
                              i32.const 4
                              i32.add
                              i32.load
                              local.tee 8
                              i32.add
                              local.get 7
                              i32.eq
                              br_if 2 (;@10;)
                              local.get 0
                              i32.load offset=8
                              local.tee 0
                              br_if 0 (;@12;)
                              br 3 (;@9;)
                            end
                          end
                          global.get $__memory_base
                          i32.const 1048612
                          i32.add
                          i32.load offset=444
                          local.tee 0
                          i32.eqz
                          br_if 2 (;@8;)
                          local.get 0
                          local.get 7
                          i32.gt_u
                          br_if 2 (;@8;)
                          br 7 (;@3;)
                        end
                        local.get 0
                        i32.load offset=12
                        br_if 0 (;@9;)
                        local.get 6
                        local.get 2
                        i32.gt_u
                        br_if 0 (;@9;)
                        local.get 2
                        local.get 7
                        i32.lt_u
                        br_if 2 (;@7;)
                      end
                      global.get $__memory_base
                      i32.const 1048612
                      i32.add
                      local.tee 0
                      local.get 0
                      i32.load offset=444
                      local.tee 6
                      local.get 7
                      local.get 6
                      local.get 7
                      i32.lt_u
                      select
                      i32.store offset=444
                      local.get 7
                      local.get 5
                      i32.add
                      local.set 6
                      local.get 0
                      i32.const 128
                      i32.add
                      local.set 0
                      block ;; label = @9
                        block ;; label = @10
                          block ;; label = @11
                            block ;; label = @12
                              loop ;; label = @13
                                local.get 0
                                i32.load
                                local.tee 8
                                local.get 6
                                i32.eq
                                br_if 1 (;@12;)
                                local.get 0
                                i32.load offset=8
                                local.tee 0
                                br_if 0 (;@13;)
                                br 2 (;@11;)
                              end
                            end
                            local.get 0
                            i32.load offset=12
                            i32.eqz
                            br_if 1 (;@10;)
                          end
                          global.get $__memory_base
                          i32.const 1048612
                          i32.add
                          i32.const 128
                          i32.add
                          local.set 0
                          loop ;; label = @11
                            block ;; label = @12
                              local.get 0
                              i32.load
                              local.tee 6
                              local.get 2
                              i32.gt_u
                              br_if 0 (;@12;)
                              local.get 2
                              local.get 6
                              local.get 0
                              i32.const 4
                              i32.add
                              i32.load
                              i32.add
                              local.tee 6
                              i32.lt_u
                              br_if 3 (;@9;)
                            end
                            local.get 0
                            i32.load offset=8
                            local.set 0
                            br 0 (;@11;)
                          end
                        end
                        local.get 0
                        local.get 7
                        i32.store
                        local.get 0
                        local.get 0
                        i32.load offset=4
                        local.get 5
                        i32.add
                        i32.store offset=4
                        local.get 7
                        local.get 3
                        i32.const 3
                        i32.or
                        i32.store offset=4
                        local.get 8
                        i32.const 15
                        i32.add
                        i32.const -8
                        i32.and
                        i32.const -8
                        i32.add
                        local.tee 0
                        local.get 7
                        local.get 3
                        i32.add
                        local.tee 2
                        i32.sub
                        local.set 3
                        local.get 0
                        global.get $__memory_base
                        i32.const 1048612
                        i32.add
                        i32.load offset=428
                        i32.eq
                        br_if 3 (;@6;)
                        local.get 0
                        global.get $__memory_base
                        i32.const 1048612
                        i32.add
                        i32.load offset=424
                        i32.eq
                        br_if 4 (;@5;)
                        block ;; label = @10
                          local.get 0
                          i32.load offset=4
                          local.tee 1
                          i32.const 3
                          i32.and
                          i32.const 1
                          i32.ne
                          br_if 0 (;@10;)
                          local.get 0
                          local.get 1
                          i32.const -8
                          i32.and
                          local.tee 1
                          call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCskAuRjb5C0Ki_4p3rt
                          local.get 1
                          local.get 3
                          i32.add
                          local.set 3
                          local.get 0
                          local.get 1
                          i32.add
                          local.tee 0
                          i32.load offset=4
                          local.set 1
                        end
                        local.get 0
                        local.get 1
                        i32.const -2
                        i32.and
                        i32.store offset=4
                        local.get 2
                        local.get 3
                        i32.const 1
                        i32.or
                        i32.store offset=4
                        local.get 2
                        local.get 3
                        i32.add
                        local.get 3
                        i32.store
                        local.get 2
                        local.get 3
                        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12insert_chunkCskAuRjb5C0Ki_4p3rt
                        br 5 (;@4;)
                      end
                      global.get $__memory_base
                      i32.const 1048612
                      i32.add
                      local.tee 0
                      local.get 5
                      i32.const -40
                      i32.add
                      local.tee 8
                      i32.store offset=420
                      local.get 0
                      local.get 7
                      i32.store offset=428
                      local.get 7
                      local.get 8
                      i32.add
                      i32.const 40
                      i32.store offset=4
                      local.get 7
                      local.get 8
                      i32.const 1
                      i32.or
                      i32.store offset=4
                      local.get 0
                      i32.const 2097152
                      i32.store offset=440
                      local.get 2
                      local.get 6
                      i32.const -32
                      i32.add
                      i32.const -8
                      i32.and
                      i32.const -8
                      i32.add
                      local.tee 8
                      local.get 8
                      local.get 2
                      i32.const 16
                      i32.add
                      i32.lt_u
                      select
                      local.tee 8
                      i32.const 27
                      i32.store offset=4
                      local.get 0
                      i64.load offset=128 align=4
                      local.set 9
                      local.get 8
                      i32.const 16
                      i32.add
                      local.get 0
                      i64.load offset=136 align=4
                      i64.store align=4
                      local.get 8
                      i32.const 8
                      i32.add
                      local.tee 4
                      local.get 9
                      i64.store align=4
                      local.get 0
                      i32.const 0
                      i32.store offset=140
                      local.get 0
                      local.get 5
                      i32.store offset=132
                      local.get 0
                      local.get 7
                      i32.store offset=128
                      local.get 0
                      local.get 4
                      i32.store offset=136
                      local.get 8
                      i32.const 28
                      i32.add
                      local.set 0
                      loop ;; label = @9
                        local.get 0
                        i32.const 7
                        i32.store
                        local.get 0
                        i32.const 4
                        i32.add
                        local.tee 0
                        local.get 6
                        i32.lt_u
                        br_if 0 (;@9;)
                      end
                      local.get 8
                      local.get 2
                      i32.eq
                      br_if 6 (;@2;)
                      local.get 8
                      local.get 8
                      i32.load offset=4
                      i32.const -2
                      i32.and
                      i32.store offset=4
                      local.get 2
                      local.get 8
                      local.get 2
                      i32.sub
                      local.tee 0
                      i32.const 1
                      i32.or
                      i32.store offset=4
                      local.get 8
                      local.get 0
                      i32.store
                      local.get 2
                      local.get 0
                      call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12insert_chunkCskAuRjb5C0Ki_4p3rt
                      br 6 (;@2;)
                    end
                    global.get $__memory_base
                    i32.const 1048612
                    i32.add
                    local.get 7
                    i32.store offset=444
                    br 4 (;@3;)
                  end
                  local.get 0
                  i32.const 4
                  i32.add
                  local.get 8
                  local.get 5
                  i32.add
                  i32.store
                  global.get $__memory_base
                  i32.const 1048612
                  i32.add
                  local.tee 0
                  local.get 0
                  i32.load offset=428
                  local.tee 2
                  i32.const 15
                  i32.add
                  i32.const -8
                  i32.and
                  local.tee 6
                  i32.const -8
                  i32.add
                  local.tee 7
                  i32.store offset=428
                  local.get 0
                  local.get 2
                  local.get 6
                  i32.sub
                  local.get 0
                  i32.load offset=420
                  local.get 5
                  i32.add
                  local.tee 6
                  i32.add
                  i32.const 8
                  i32.add
                  local.tee 8
                  i32.store offset=420
                  local.get 7
                  local.get 8
                  i32.const 1
                  i32.or
                  i32.store offset=4
                  local.get 2
                  local.get 6
                  i32.add
                  i32.const 40
                  i32.store offset=4
                  local.get 0
                  i32.const 2097152
                  i32.store offset=440
                  br 4 (;@2;)
                end
                global.get $__memory_base
                i32.const 1048612
                i32.add
                local.tee 0
                local.get 2
                i32.store offset=428
                local.get 0
                local.get 0
                i32.load offset=420
                local.get 3
                i32.add
                local.tee 3
                i32.store offset=420
                local.get 2
                local.get 3
                i32.const 1
                i32.or
                i32.store offset=4
                br 1 (;@4;)
              end
              global.get $__memory_base
              i32.const 1048612
              i32.add
              local.tee 1
              local.get 2
              i32.store offset=424
              local.get 1
              local.get 1
              i32.load offset=416
              local.get 3
              i32.add
              local.tee 0
              i32.store offset=416
              local.get 2
              local.get 0
              i32.const 1
              i32.or
              i32.store offset=4
              local.get 2
              local.get 0
              i32.add
              local.get 0
              i32.store
            end
            local.get 7
            i32.const 8
            i32.add
            return
          end
          i32.const 0
          local.set 0
          global.get $__memory_base
          i32.const 1048612
          i32.add
          local.tee 2
          i32.const 0
          i32.store offset=140
          local.get 2
          local.get 5
          i32.store offset=132
          local.get 2
          local.get 7
          i32.store offset=128
          local.get 2
          local.get 2
          i32.load offset=456
          local.tee 6
          i32.const -1
          local.get 6
          select
          i32.store offset=448
          loop ;; label = @3
            global.get $__memory_base
            i32.const 1048612
            i32.add
            local.get 0
            i32.add
            local.tee 2
            i32.const 152
            i32.add
            local.get 2
            i32.const 144
            i32.add
            local.tee 6
            i32.store
            local.get 2
            i32.const 156
            i32.add
            local.get 6
            i32.store
            local.get 0
            i32.const 8
            i32.add
            local.tee 0
            i32.const 256
            i32.ne
            br_if 0 (;@3;)
          end
          global.get $__memory_base
          i32.const 1048612
          i32.add
          local.tee 0
          local.get 5
          i32.const -40
          i32.add
          local.tee 2
          i32.store offset=420
          local.get 0
          local.get 7
          i32.store offset=428
          local.get 7
          local.get 2
          i32.add
          i32.const 40
          i32.store offset=4
          local.get 7
          local.get 2
          i32.const 1
          i32.or
          i32.store offset=4
          local.get 0
          i32.const 2097152
          i32.store offset=440
        end
        global.get $__memory_base
        i32.const 1048612
        i32.add
        i32.load offset=420
        local.tee 0
        local.get 3
        i32.le_u
        br_if 0 (;@1;)
        global.get $__memory_base
        i32.const 1048612
        i32.add
        local.tee 2
        local.get 0
        local.get 3
        i32.sub
        local.tee 1
        i32.store offset=420
        local.get 2
        local.get 2
        i32.load offset=428
        local.tee 0
        local.get 3
        i32.add
        local.tee 6
        i32.store offset=428
        local.get 6
        local.get 1
        i32.const 1
        i32.or
        i32.store offset=4
        local.get 0
        local.get 3
        i32.const 3
        i32.or
        i32.store offset=4
        local.get 0
        i32.const 8
        i32.add
        return
      end
      local.get 1
    )
    (func $_RNvNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8callback (;26;) (type 5) (param i32 i32 i32) (result i32)
      (local i32 i32 i32 i32 i32 i32)
      global.get $__stack_pointer
      i32.const 48
      i32.sub
      local.tee 3
      global.set $__stack_pointer
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  block ;; label = @7
                    block ;; label = @8
                      block ;; label = @9
                        block ;; label = @10
                          call $_RNvNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10task_state3get3get
                          local.tee 4
                          i32.eqz
                          br_if 0 (;@10;)
                          i32.const 0
                          call $_RNvNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10task_state3set3set
                          block ;; label = @11
                            local.get 0
                            i32.const 6
                            i32.lt_u
                            br_if 0 (;@11;)
                            local.get 0
                            i32.const 6
                            i32.eq
                            br_if 9 (;@2;)
                            i32.const 40
                            call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                            unreachable
                          end
                          global.get $__memory_base
                          local.set 5
                          local.get 4
                          i32.load
                          local.set 6
                          local.get 3
                          local.get 5
                          i32.const 1049268
                          i32.add
                          i32.store offset=44
                          local.get 3
                          global.get $__table_base
                          local.tee 5
                          i32.const 0
                          i32.add
                          i32.store offset=40
                          local.get 3
                          local.get 5
                          i32.const 1
                          i32.add
                          i32.store offset=36
                          local.get 3
                          local.get 6
                          i32.const 8
                          i32.add
                          i32.store offset=32
                          local.get 3
                          i32.const 2
                          i32.store offset=28
                          local.get 3
                          i32.const 28
                          i32.add
                          call $wasip3_task_set
                          local.set 7
                          local.get 6
                          i32.const 1
                          i32.store offset=32
                          block ;; label = @11
                            local.get 0
                            i32.eqz
                            br_if 0 (;@11;)
                            local.get 4
                            i32.load
                            local.get 1
                            local.get 2
                            call $_RNvMs_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB4_9TaskState22deliver_waitable_event
                            local.get 4
                            i32.load
                            local.set 6
                          end
                          local.get 6
                          i32.const 0
                          i32.store offset=32
                          local.get 3
                          i32.const 0
                          i32.store offset=8
                          local.get 3
                          local.get 4
                          i32.const 4
                          i32.add
                          local.tee 0
                          i32.store offset=4
                          local.get 3
                          local.get 0
                          i32.store
                          local.get 4
                          i32.load offset=12
                          local.tee 6
                          i32.eqz
                          br_if 3 (;@7;)
                          loop ;; label = @11
                            local.get 6
                            local.get 3
                            local.get 4
                            i32.load offset=16
                            i32.load offset=12
                            call_indirect (type 0)
                            local.set 6
                            local.get 4
                            i32.load offset=12
                            local.set 5
                            block ;; label = @12
                              local.get 6
                              br_if 0 (;@12;)
                              local.get 5
                              local.get 4
                              i32.load offset=16
                              call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtB4_6option6OptionINtNtB4_3pin3PinINtNtCsiqQVI2xHy0t_5alloc5boxed3BoxDNtNtNtB4_6future6future6Futurep6OutputuEL_EEEECscNOpLhlpk4u_11wit_bindgen
                              local.get 4
                              i32.const 0
                              i32.store offset=12
                              br 5 (;@7;)
                            end
                            local.get 5
                            i32.eqz
                            br_if 2 (;@9;)
                            block ;; label = @12
                              local.get 4
                              i32.load
                              local.tee 6
                              i32.load offset=32
                              i32.const 1
                              i32.ne
                              br_if 0 (;@12;)
                              local.get 6
                              i32.load8_u offset=20
                              local.set 5
                              local.get 6
                              i32.const 1
                              i32.store8 offset=20
                              local.get 5
                              br_if 8 (;@4;)
                              local.get 6
                              i32.const 0
                              i32.store8 offset=20
                              i32.const 1
                              local.set 8
                              local.get 6
                              i32.load offset=16
                              i32.eqz
                              br_if 7 (;@5;)
                              local.get 4
                              i32.load
                              local.tee 6
                              i32.load8_u offset=28
                              local.set 5
                              local.get 6
                              i32.const 1
                              i32.store8 offset=28
                              local.get 5
                              br_if 8 (;@4;)
                              local.get 6
                              i32.load offset=24
                              local.tee 5
                              i32.eqz
                              br_if 8 (;@4;)
                              local.get 3
                              i64.const 0
                              i64.store offset=16
                              local.get 5
                              local.get 3
                              i32.const 16
                              i32.add
                              call $_RNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12waitable_set4poll
                              local.set 5
                              local.get 3
                              i32.load offset=20
                              local.set 2
                              local.get 3
                              i32.load offset=16
                              local.set 1
                              local.get 6
                              i32.const 0
                              i32.store8 offset=28
                              local.get 5
                              i32.eqz
                              br_if 7 (;@5;)
                              local.get 4
                              i32.load
                              local.get 1
                              local.get 2
                              call $_RNvMs_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB4_9TaskState22deliver_waitable_event
                              local.get 4
                              i32.load
                              i32.const 0
                              i32.store offset=32
                              local.get 3
                              i32.const 0
                              i32.store offset=8
                              local.get 3
                              local.get 0
                              i32.store offset=4
                              local.get 3
                              local.get 0
                              i32.store
                              local.get 4
                              i32.load offset=12
                              local.tee 6
                              br_if 1 (;@11;)
                              br 5 (;@7;)
                            end
                          end
                          local.get 6
                          i32.const 2
                          i32.store offset=32
                          local.get 4
                          i32.load
                          local.tee 6
                          i32.load8_u offset=20
                          local.set 0
                          local.get 6
                          i32.const 1
                          i32.store8 offset=20
                          local.get 0
                          br_if 6 (;@4;)
                          local.get 6
                          i32.const 0
                          i32.store8 offset=20
                          local.get 6
                          i32.load offset=16
                          i32.eqz
                          br_if 2 (;@8;)
                          local.get 4
                          i32.load
                          local.tee 6
                          i32.load8_u offset=28
                          local.set 0
                          local.get 6
                          i32.const 1
                          i32.store8 offset=28
                          local.get 0
                          i32.eqz
                          br_if 4 (;@6;)
                          br 6 (;@4;)
                        end
                        i32.const 34
                        call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                        unreachable
                      end
                      i32.const 38
                      call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                      unreachable
                    end
                    call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
                    unreachable
                  end
                  local.get 4
                  i32.load
                  local.tee 6
                  i32.load8_u offset=20
                  local.set 0
                  local.get 6
                  i32.const 1
                  i32.store8 offset=20
                  local.get 0
                  br_if 2 (;@4;)
                  local.get 6
                  i32.const 0
                  i32.store8 offset=20
                  local.get 6
                  i32.load offset=16
                  i32.eqz
                  br_if 3 (;@3;)
                  local.get 4
                  i32.load
                  local.tee 6
                  i32.load8_u offset=28
                  local.set 0
                  local.get 6
                  i32.const 1
                  i32.store8 offset=28
                  local.get 0
                  br_if 2 (;@4;)
                end
                local.get 6
                i32.load offset=24
                local.tee 0
                i32.eqz
                br_if 1 (;@4;)
                local.get 6
                i32.const 0
                i32.store8 offset=28
                local.get 0
                i32.const 4
                i32.shl
                i32.const 2
                i32.or
                local.set 8
              end
              local.get 7
              call $wasip3_task_set
              drop
              local.get 4
              call $_RNvNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10task_state3set3set
              br 3 (;@1;)
            end
            call $_RNvNtCshQUFA83YM6w_4core6option13unwrap_failed
            unreachable
          end
          local.get 7
          call $wasip3_task_set
          drop
        end
        block ;; label = @2
          block ;; label = @3
            local.get 4
            i32.load offset=12
            local.tee 6
            br_if 0 (;@3;)
            i32.const 0
            local.set 6
            br 1 (;@2;)
          end
          global.get $__memory_base
          local.set 0
          local.get 4
          i32.load
          local.set 5
          local.get 3
          local.get 0
          i32.const 1049268
          i32.add
          i32.store offset=44
          local.get 3
          global.get $__table_base
          local.tee 0
          i32.const 0
          i32.add
          i32.store offset=40
          local.get 3
          local.get 0
          i32.const 1
          i32.add
          i32.store offset=36
          local.get 3
          local.get 5
          i32.const 8
          i32.add
          i32.store offset=32
          local.get 3
          i32.const 2
          i32.store offset=28
          local.get 3
          i32.const 28
          i32.add
          call $wasip3_task_set
          local.set 0
          local.get 6
          local.get 4
          i32.load offset=16
          call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtB4_6option6OptionINtNtB4_3pin3PinINtNtCsiqQVI2xHy0t_5alloc5boxed3BoxDNtNtNtB4_6future6future6Futurep6OutputuEL_EEEECscNOpLhlpk4u_11wit_bindgen
          local.get 4
          i32.const 0
          i32.store offset=12
          local.get 0
          call $wasip3_task_set
          drop
          local.get 4
          i32.load offset=12
          local.set 6
        end
        local.get 6
        local.get 4
        i32.const 16
        i32.add
        i32.load
        call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtB4_6option6OptionINtNtB4_3pin3PinINtNtCsiqQVI2xHy0t_5alloc5boxed3BoxDNtNtNtB4_6future6future6Futurep6OutputuEL_EEEECscNOpLhlpk4u_11wit_bindgen
        local.get 4
        i32.load
        local.tee 6
        local.get 6
        i32.load
        local.tee 6
        i32.const -1
        i32.add
        i32.store
        block ;; label = @2
          local.get 6
          i32.const 1
          i32.ne
          br_if 0 (;@2;)
          local.get 4
          i32.load
          call $_RNvMsn_NtCsiqQVI2xHy0t_5alloc4syncINtB5_3ArcNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support15SharedTaskStateE9drop_slowBM_
        end
        local.get 4
        i32.load offset=8
        local.get 4
        i32.load offset=4
        i32.load offset=12
        call_indirect (type 1)
        local.get 4
        i32.const -4
        i32.add
        i32.load
        i32.const 20
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
        local.get 4
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt
        i32.const 0
        local.set 8
      end
      local.get 3
      i32.const 48
      i32.add
      global.set $__stack_pointer
      local.get 8
    )
    (func $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt (;27;) (type 7)
      unreachable
    )
    (func $_RNvNtCshQUFA83YM6w_4core9panicking5panic (;28;) (type 1) (param i32)
      call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
      unreachable
    )
    (func $"[callback][async-lift]wasi:cli/run@0.3.0#run" (;29;) (type 5) (param i32 i32 i32) (result i32)
      local.get 0
      local.get 1
      local.get 2
      call $_RNvNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8callback
    )
    (func $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtCs22k8fyVPmoz_12futures_util6future10maybe_done9MaybeDoneNCNCNvXCsgR5kJmH8IIE_5helloNtB1K_5HelloNtNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run5Guest3run0s0_0EEB1K_ (;30;) (type 1) (param i32)
      block ;; label = @1
        local.get 0
        i32.load
        br_if 0 (;@1;)
        block ;; label = @2
          block ;; label = @3
            local.get 0
            i32.load8_u offset=152
            br_table 1 (;@2;) 2 (;@1;) 2 (;@1;) 0 (;@3;) 2 (;@1;)
          end
          local.get 0
          i32.const 4
          i32.add
          call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueNCNvMs_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14stream_supportINtBI_15RawStreamWriterRINtBI_12StreamVtablehEE9write_all0ECsgR5kJmH8IIE_5hello
        end
        local.get 0
        i32.load offset=144
        local.get 0
        i32.load offset=140
        i32.load offset=24
        call_indirect (type 1)
      end
    )
    (func $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueNCNvMs_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14stream_supportINtBI_15RawStreamWriterRINtBI_12StreamVtablehEE9write_all0ECsgR5kJmH8IIE_5hello (;31;) (type 1) (param i32)
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              local.get 0
              i32.load8_u offset=20
              br_table 0 (;@4;) 3 (;@1;) 3 (;@1;) 1 (;@3;) 2 (;@2;) 3 (;@1;)
            end
            local.get 0
            i32.load
            local.get 0
            i32.const 4
            i32.add
            i32.load
            call $_RNvMs3_NtCsiqQVI2xHy0t_5alloc7raw_vecNtB5_11RawVecInner10deallocateCscNOpLhlpk4u_11wit_bindgen
            return
          end
          local.get 0
          i32.const 24
          i32.add
          call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14stream_support14RawStreamWriteRINtBE_12StreamVtablehEEECsgR5kJmH8IIE_5hello
          return
        end
        local.get 0
        i32.const 32
        i32.add
        call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14stream_support14RawStreamWriteRINtBE_12StreamVtablehEEECsgR5kJmH8IIE_5hello
      end
    )
    (func $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtCs22k8fyVPmoz_12futures_util6future10maybe_done9MaybeDoneNCNCNvXCsgR5kJmH8IIE_5helloNtB1K_5HelloNtNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run5Guest3run0s_0EEB1K_ (;32;) (type 1) (param i32)
      (local i32)
      block ;; label = @1
        local.get 0
        i32.load8_u
        br_if 0 (;@1;)
        block ;; label = @2
          block ;; label = @3
            local.get 0
            i32.load8_u offset=68
            br_table 0 (;@3;) 2 (;@1;) 2 (;@1;) 1 (;@2;) 2 (;@1;)
          end
          local.get 0
          i32.load offset=60
          local.tee 1
          i32.const -1
          i32.eq
          br_if 1 (;@1;)
          local.get 1
          local.get 0
          i32.load offset=56
          i32.load offset=28
          call_indirect (type 1)
          return
        end
        local.get 0
        i32.const 4
        i32.add
        call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14future_support13RawFutureReadRINtBE_12FutureVtableINtNtB4_6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEECsgR5kJmH8IIE_5hello
      end
    )
    (func $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14future_support13RawFutureReadRINtBE_12FutureVtableINtNtB4_6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEECsgR5kJmH8IIE_5hello (;33;) (type 1) (param i32)
      (local i32 i32 i64 i32 i32 i32)
      global.get $__stack_pointer
      i32.const 32
      i32.sub
      local.tee 1
      global.set $__stack_pointer
      block ;; label = @1
        local.get 0
        i32.load offset=40
        local.tee 2
        i32.const -2147483645
        i32.eq
        br_if 0 (;@1;)
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  local.get 2
                  i32.const 2147483647
                  i32.add
                  i32.const 1
                  local.get 2
                  i32.const -2147483648
                  i32.gt_u
                  select
                  br_table 1 (;@5;) 2 (;@4;) 0 (;@6;) 1 (;@5;)
                end
                call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
                unreachable
              end
              local.get 0
              i32.const 32
              i32.add
              local.tee 2
              i64.load offset=8 align=4
              local.set 3
              local.get 2
              i32.load offset=16
              local.set 4
              local.get 0
              i32.const -2147483645
              i32.store offset=40
              local.get 1
              local.get 4
              i32.store offset=24
              local.get 1
              local.get 3
              i64.store offset=16
              local.get 1
              local.get 2
              i64.load align=4
              i64.store offset=8
              local.get 3
              i32.wrap_i64
              i32.const -2147483647
              i32.eq
              br_if 1 (;@3;)
              local.get 1
              i32.const 8
              i32.add
              call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable22WaitableOperationStateINtNtBG_14future_support12FutureReadOpRINtB23_12FutureVtableINtNtB4_6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEEECsgR5kJmH8IIE_5hello
              i32.const 40
              call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
              unreachable
            end
            local.get 0
            i32.load
            local.set 2
            local.get 0
            i32.const 0
            i32.store
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  block ;; label = @7
                    block ;; label = @8
                      block ;; label = @9
                        block ;; label = @10
                          local.get 2
                          br_if 0 (;@10;)
                          local.get 0
                          i32.load offset=36
                          local.tee 2
                          i32.const -1
                          i32.eq
                          br_if 5 (;@5;)
                          block ;; label = @11
                            block ;; label = @12
                              local.get 0
                              i32.load offset=16
                              i32.const 2
                              i32.eq
                              br_if 0 (;@12;)
                              local.get 0
                              i32.const 0
                              i32.store offset=16
                              local.get 0
                              i32.load offset=28
                              local.get 2
                              local.get 0
                              i32.load offset=24
                              i32.load offset=4
                              call_indirect (type 0)
                              local.set 2
                              br 1 (;@11;)
                            end
                            i32.const 0
                            call $wasip3_task_set
                            local.tee 4
                            i32.eqz
                            br_if 2 (;@9;)
                            local.get 4
                            i32.load
                            i32.eqz
                            br_if 3 (;@8;)
                            local.get 4
                            i32.load offset=4
                            local.get 2
                            local.get 4
                            i32.load offset=12
                            call_indirect (type 0)
                            local.set 2
                            local.get 4
                            call $wasip3_task_set
                            drop
                          end
                          local.get 2
                          i32.eqz
                          br_if 4 (;@6;)
                          local.get 0
                          local.get 2
                          i32.ne
                          br_if 3 (;@7;)
                          br 4 (;@6;)
                        end
                        local.get 1
                        i32.const 8
                        i32.add
                        local.get 0
                        i32.const 0
                        i32.const 1
                        local.get 0
                        i32.load offset=4
                        call $_RNvMs2_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitableINtB5_17WaitableOperationINtNtB7_14future_support12FutureReadOpRINtB1v_12FutureVtableINtNtCshQUFA83YM6w_4core6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEE23poll_complete_with_codeCsgR5kJmH8IIE_5hello
                        local.get 1
                        i32.load8_u offset=8
                        local.tee 2
                        i32.const 253
                        i32.eq
                        br_if 3 (;@6;)
                        local.get 1
                        i32.load offset=16
                        local.set 5
                        local.get 1
                        i32.load offset=12
                        local.set 6
                        block ;; label = @10
                          local.get 2
                          i32.const 254
                          i32.ne
                          br_if 0 (;@10;)
                          local.get 5
                          local.set 2
                          local.get 6
                          local.set 4
                          br 8 (;@2;)
                        end
                        i32.const 0
                        local.set 4
                        local.get 5
                        i32.const -1
                        i32.eq
                        br_if 7 (;@2;)
                        local.get 5
                        local.get 6
                        i32.load offset=40
                        call_indirect (type 1)
                        br 7 (;@2;)
                      end
                      i32.const 33
                      call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                      unreachable
                    end
                    i32.const 57
                    call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                    unreachable
                  end
                  local.get 1
                  i32.const 28
                  i32.add
                  local.get 1
                  i32.const 8
                  i32.add
                  call $_RINvNtCshQUFA83YM6w_4core9panicking13assert_failedONtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable16CompletionStatusBM_ECs8o6ThntBNTu_6wasip3
                  unreachable
                end
                block ;; label = @6
                  local.get 0
                  i32.load offset=40
                  i32.const -2147483647
                  i32.lt_u
                  br_if 0 (;@6;)
                  i32.const 40
                  call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                  unreachable
                end
                local.get 0
                i32.load offset=36
                local.tee 2
                i32.const -1
                i32.eq
                br_if 0 (;@5;)
                local.get 1
                i32.const 8
                i32.add
                local.get 0
                i32.const 0
                i32.const 1
                local.get 2
                local.get 0
                i32.load offset=32
                i32.load offset=32
                call_indirect (type 2)
                call $_RNvMs2_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitableINtB5_17WaitableOperationINtNtB7_14future_support12FutureReadOpRINtB1v_12FutureVtableINtNtCshQUFA83YM6w_4core6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEE23poll_complete_with_codeCsgR5kJmH8IIE_5hello
                local.get 1
                i32.load8_u offset=8
                local.tee 2
                i32.const 253
                i32.eq
                br_if 1 (;@4;)
                local.get 1
                i32.load offset=16
                local.set 5
                local.get 1
                i32.load offset=12
                local.set 6
                block ;; label = @6
                  local.get 2
                  i32.const 254
                  i32.ne
                  br_if 0 (;@6;)
                  local.get 5
                  local.set 2
                  local.get 6
                  local.set 4
                  br 4 (;@2;)
                end
                i32.const 0
                local.set 4
                local.get 5
                i32.const -1
                i32.eq
                br_if 3 (;@2;)
                local.get 5
                local.get 6
                i32.load offset=40
                call_indirect (type 1)
                br 3 (;@2;)
              end
              call $_RNvNtCshQUFA83YM6w_4core6option13unwrap_failed
              unreachable
            end
            i32.const 40
            call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
            unreachable
          end
          local.get 1
          i32.load offset=12
          local.set 2
          local.get 1
          i32.load offset=8
          local.set 4
        end
        local.get 4
        i32.eqz
        br_if 0 (;@1;)
        local.get 2
        i32.const -1
        i32.eq
        br_if 0 (;@1;)
        local.get 2
        local.get 4
        i32.load offset=40
        call_indirect (type 1)
      end
      local.get 0
      i32.const 32
      i32.add
      call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable22WaitableOperationStateINtNtBG_14future_support12FutureReadOpRINtB23_12FutureVtableINtNtB4_6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEEECsgR5kJmH8IIE_5hello
      block ;; label = @1
        local.get 0
        i32.load offset=16
        local.tee 2
        i32.const 2
        i32.eq
        br_if 0 (;@1;)
        block ;; label = @2
          block ;; label = @3
            local.get 2
            i32.const 1
            i32.and
            br_if 0 (;@3;)
            local.get 0
            i32.load offset=28
            local.set 2
            local.get 0
            i32.load offset=24
            local.set 4
            br 1 (;@2;)
          end
          local.get 0
          i32.const 0
          i32.store offset=16
          local.get 0
          i32.load offset=28
          local.tee 2
          local.get 0
          i32.load offset=20
          local.get 0
          i32.load offset=24
          local.tee 4
          i32.load offset=4
          call_indirect (type 0)
          drop
        end
        local.get 2
        local.get 4
        i32.load offset=12
        call_indirect (type 1)
      end
      block ;; label = @1
        local.get 0
        i32.load offset=8
        local.tee 2
        i32.eqz
        br_if 0 (;@1;)
        local.get 0
        i32.load offset=12
        local.get 2
        i32.load offset=12
        call_indirect (type 1)
      end
      local.get 1
      i32.const 32
      i32.add
      global.set $__stack_pointer
    )
    (func $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10abi_buffer9AbiBufferRINtNtBG_14stream_support12StreamVtablehEEECsgR5kJmH8IIE_5hello (;34;) (type 1) (param i32)
      (local i32)
      global.get $__stack_pointer
      i32.const 16
      i32.sub
      local.tee 1
      global.set $__stack_pointer
      local.get 1
      i32.const 4
      i32.add
      local.get 0
      call $_RNvMNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10abi_bufferINtB2_9AbiBufferRINtNtB4_14stream_support12StreamVtablehEE8take_vecCsgR5kJmH8IIE_5hello
      local.get 1
      i32.load offset=4
      local.get 1
      i32.load offset=8
      call $_RNvMs3_NtCsiqQVI2xHy0t_5alloc7raw_vecNtB5_11RawVecInner10deallocateCscNOpLhlpk4u_11wit_bindgen
      local.get 0
      i32.load
      local.get 0
      i32.load offset=4
      call $_RNvMs3_NtCsiqQVI2xHy0t_5alloc7raw_vecNtB5_11RawVecInner10deallocateCscNOpLhlpk4u_11wit_bindgen
      block ;; label = @1
        local.get 0
        i32.load offset=12
        i32.eqz
        br_if 0 (;@1;)
        local.get 0
        i32.load offset=16
        local.get 0
        i32.load offset=20
        call $_RNvXs2_NtCscNOpLhlpk4u_11wit_bindgen2rtNtB5_7CleanupNtNtNtCshQUFA83YM6w_4core3ops4drop4Drop4drop
      end
      local.get 1
      i32.const 16
      i32.add
      global.set $__stack_pointer
    )
    (func $_RNvMNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10abi_bufferINtB2_9AbiBufferRINtNtB4_14stream_support12StreamVtablehEE8take_vecCsgR5kJmH8IIE_5hello (;35;) (type 3) (param i32 i32)
      (local i32 i32 i32 i32 i32 i32 i32 i32 i32)
      global.get $__stack_pointer
      i32.const 16
      i32.sub
      local.tee 2
      global.set $__stack_pointer
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                local.get 1
                i32.load offset=24
                local.tee 3
                i32.load offset=44
                br_if 0 (;@5;)
                local.get 1
                i32.load offset=28
                local.set 4
                local.get 1
                i32.load offset=8
                local.set 5
                local.get 1
                i32.load offset=4
                local.set 6
                br 1 (;@4;)
              end
              local.get 1
              i32.load offset=8
              local.tee 5
              local.get 1
              i32.load offset=28
              local.tee 4
              i32.lt_u
              br_if 1 (;@3;)
              local.get 1
              i32.load offset=4
              local.set 6
              local.get 5
              local.get 4
              i32.eq
              br_if 0 (;@4;)
              local.get 1
              i32.load offset=20
              i32.const 0
              local.get 1
              i32.load offset=12
              select
              local.get 3
              i32.load offset=4
              local.get 4
              i32.mul
              i32.add
              local.set 7
              local.get 5
              local.get 4
              i32.sub
              local.set 8
              local.get 6
              local.get 4
              i32.add
              local.set 9
              loop ;; label = @5
                local.get 3
                i32.load offset=44
                local.tee 10
                i32.eqz
                br_if 3 (;@2;)
                local.get 9
                local.get 7
                local.get 10
                call_indirect (type 2)
                i32.store8
                local.get 9
                i32.const 1
                i32.add
                local.set 9
                local.get 7
                local.get 3
                i32.load offset=4
                i32.add
                local.set 7
                local.get 8
                i32.const -1
                i32.add
                local.tee 8
                br_if 0 (;@5;)
              end
            end
            local.get 1
            i64.const 1
            i64.store offset=4 align=4
            local.get 1
            i32.load
            local.set 9
            local.get 1
            i32.const 0
            i32.store
            local.get 5
            local.get 4
            i32.lt_u
            br_if 2 (;@1;)
            local.get 5
            local.get 4
            i32.sub
            local.set 7
            block ;; label = @4
              local.get 4
              i32.eqz
              br_if 0 (;@4;)
              block ;; label = @5
                local.get 7
                br_if 0 (;@5;)
                i32.const 0
                local.set 7
                br 1 (;@4;)
              end
              local.get 7
              i32.eqz
              br_if 0 (;@4;)
              local.get 6
              local.get 6
              local.get 4
              i32.add
              local.get 7
              memory.copy
            end
            local.get 1
            i32.const 0
            i32.store offset=28
            block ;; label = @4
              local.get 1
              i32.load offset=12
              i32.eqz
              br_if 0 (;@4;)
              local.get 1
              i32.load offset=16
              local.get 1
              i32.load offset=20
              call $_RNvXs2_NtCscNOpLhlpk4u_11wit_bindgen2rtNtB5_7CleanupNtNtNtCshQUFA83YM6w_4core3ops4drop4Drop4drop
            end
            local.get 0
            local.get 7
            i32.store offset=8
            local.get 0
            local.get 6
            i32.store offset=4
            local.get 0
            local.get 9
            i32.store
            local.get 1
            i32.const 0
            i32.store offset=12
            local.get 2
            i32.const 16
            i32.add
            global.set $__stack_pointer
            return
          end
          local.get 4
          local.get 5
          local.get 5
          call $_RNvNtNtCshQUFA83YM6w_4core5slice5index16slice_index_fail
          unreachable
        end
        call $_RNvNtCshQUFA83YM6w_4core6option13unwrap_failed
        unreachable
      end
      i32.const 0
      local.get 4
      local.get 5
      call $_RNvNtNtCshQUFA83YM6w_4core5slice5index16slice_index_fail
      unreachable
    )
    (func $_RNvMs3_NtCsiqQVI2xHy0t_5alloc7raw_vecNtB5_11RawVecInner10deallocateCscNOpLhlpk4u_11wit_bindgen (;36;) (type 3) (param i32 i32)
      (local i32 i32)
      global.get $__stack_pointer
      i32.const 16
      i32.sub
      local.tee 2
      global.set $__stack_pointer
      block ;; label = @1
        block ;; label = @2
          local.get 0
          br_if 0 (;@2;)
          i32.const 0
          local.set 0
          local.get 2
          i32.const 12
          i32.add
          local.set 3
          br 1 (;@1;)
        end
        local.get 2
        i32.const 1
        i32.store offset=12
        local.get 2
        i32.const 8
        i32.add
        local.set 3
      end
      local.get 3
      local.get 0
      i32.store
      block ;; label = @1
        local.get 2
        i32.load offset=12
        i32.eqz
        br_if 0 (;@1;)
        local.get 2
        i32.load offset=8
        local.tee 0
        i32.eqz
        br_if 0 (;@1;)
        local.get 1
        i32.const -4
        i32.add
        i32.load
        local.get 0
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
        local.get 1
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt
      end
      local.get 2
      i32.const 16
      i32.add
      global.set $__stack_pointer
    )
    (func $_RNvXs2_NtCscNOpLhlpk4u_11wit_bindgen2rtNtB5_7CleanupNtNtNtCshQUFA83YM6w_4core3ops4drop4Drop4drop (;37;) (type 3) (param i32 i32)
      block ;; label = @1
        block ;; label = @2
          local.get 0
          br_if 0 (;@2;)
          i32.const 0
          local.set 0
          br 1 (;@1;)
        end
        local.get 0
        i32.eqz
        br_if 0 (;@1;)
        local.get 1
        i32.const 255
        local.get 0
        memory.fill
      end
      local.get 1
      i32.const -4
      i32.add
      i32.load
      local.get 0
      call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
      local.get 1
      call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt
    )
    (func $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable22WaitableOperationStateINtNtBG_14future_support12FutureReadOpRINtB23_12FutureVtableINtNtB4_6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEEECsgR5kJmH8IIE_5hello (;38;) (type 1) (param i32)
      (local i32 i32)
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            local.get 0
            i32.load offset=8
            local.tee 1
            i32.const 2147483647
            i32.add
            i32.const 1
            local.get 1
            i32.const -2147483648
            i32.gt_u
            select
            br_table 0 (;@3;) 1 (;@2;) 2 (;@1;)
          end
          local.get 0
          i32.load offset=4
          local.tee 1
          i32.const -1
          i32.eq
          br_if 1 (;@1;)
          local.get 1
          local.get 0
          i32.load
          i32.load offset=40
          call_indirect (type 1)
          return
        end
        block ;; label = @2
          local.get 0
          i32.load offset=4
          local.tee 2
          i32.const -1
          i32.eq
          br_if 0 (;@2;)
          local.get 2
          local.get 0
          i32.load
          i32.load offset=40
          call_indirect (type 1)
        end
        local.get 1
        i32.eqz
        br_if 0 (;@1;)
        local.get 0
        i32.load offset=12
        local.get 0
        i32.load offset=16
        call $_RNvXs2_NtCscNOpLhlpk4u_11wit_bindgen2rtNtB5_7CleanupNtNtNtCshQUFA83YM6w_4core3ops4drop4Drop4drop
      end
    )
    (func $_RNvMs2_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitableINtB5_17WaitableOperationINtNtB7_14future_support12FutureReadOpRINtB1v_12FutureVtableINtNtCshQUFA83YM6w_4core6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEE23poll_complete_with_codeCsgR5kJmH8IIE_5hello (;39;) (type 9) (param i32 i32 i32 i32 i32)
      (local i32 i64 i32 i32 i32 i32 i32)
      global.get $__stack_pointer
      i32.const 48
      i32.sub
      local.tee 5
      global.set $__stack_pointer
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  local.get 3
                  i32.const 1
                  i32.ne
                  br_if 0 (;@6;)
                  local.get 1
                  i32.const 32
                  i32.add
                  local.set 3
                  block ;; label = @7
                    local.get 1
                    i32.load offset=16
                    i32.const 2
                    i32.eq
                    br_if 0 (;@7;)
                    local.get 1
                    i32.const 0
                    i32.store offset=16
                  end
                  local.get 3
                  i64.load offset=8 align=4
                  local.set 6
                  local.get 3
                  i32.load offset=16
                  local.set 7
                  local.get 1
                  i32.const -2147483645
                  i32.store offset=40
                  local.get 5
                  local.get 7
                  i32.store offset=40
                  local.get 5
                  local.get 6
                  i64.store offset=32
                  local.get 5
                  local.get 3
                  i64.load align=4
                  i64.store offset=24
                  block ;; label = @7
                    local.get 6
                    i32.wrap_i64
                    local.tee 7
                    i32.const -2147483648
                    i32.gt_u
                    br_if 0 (;@7;)
                    local.get 5
                    i32.load offset=40
                    local.set 8
                    local.get 5
                    i32.load offset=36
                    local.set 9
                    local.get 5
                    i32.load offset=28
                    local.set 10
                    local.get 5
                    i32.load offset=24
                    local.set 11
                    local.get 5
                    i64.load offset=36 align=4
                    local.set 6
                    local.get 5
                    i32.const 16
                    i32.add
                    local.get 4
                    call $_RNvMs4_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB5_10ReturnCode6decode
                    local.get 5
                    i32.load offset=20
                    local.set 4
                    block ;; label = @8
                      block ;; label = @9
                        block ;; label = @10
                          local.get 5
                          i32.load offset=16
                          br_table 5 (;@5;) 1 (;@9;) 9 (;@1;) 0 (;@10;) 5 (;@5;)
                        end
                        i32.const 254
                        local.set 1
                        local.get 4
                        i32.eqz
                        br_if 1 (;@8;)
                        br 8 (;@1;)
                      end
                      local.get 4
                      br_if 7 (;@1;)
                      local.get 6
                      i64.const 32
                      i64.shr_u
                      i32.wrap_i64
                      i32.const 0
                      local.get 7
                      select
                      local.get 11
                      i32.load offset=16
                      call_indirect (type 2)
                      i32.const 255
                      i32.and
                      local.set 1
                    end
                    block ;; label = @8
                      local.get 7
                      i32.eqz
                      br_if 0 (;@8;)
                      local.get 9
                      local.get 8
                      call $_RNvXs2_NtCscNOpLhlpk4u_11wit_bindgen2rtNtB5_7CleanupNtNtNtCshQUFA83YM6w_4core3ops4drop4Drop4drop
                    end
                    local.get 0
                    local.get 10
                    i32.store offset=8
                    local.get 0
                    local.get 11
                    i32.store offset=4
                    local.get 0
                    local.get 1
                    i32.store
                    br 5 (;@2;)
                  end
                  local.get 5
                  i32.const 24
                  i32.add
                  call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable22WaitableOperationStateINtNtBG_14future_support12FutureReadOpRINtB23_12FutureVtableINtNtB4_6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEEECsgR5kJmH8IIE_5hello
                  i32.const 40
                  call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                  unreachable
                end
                local.get 1
                i32.load offset=40
                i32.const -2147483647
                i32.ge_u
                br_if 1 (;@4;)
                br 2 (;@3;)
              end
              local.get 3
              call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable22WaitableOperationStateINtNtBG_14future_support12FutureReadOpRINtB23_12FutureVtableINtNtB4_6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEEECsgR5kJmH8IIE_5hello
              local.get 1
              local.get 6
              i64.store offset=44 align=4
              local.get 1
              local.get 7
              i32.store offset=40
              local.get 1
              local.get 10
              i32.store offset=36
              local.get 1
              local.get 11
              i32.store offset=32
              br 1 (;@3;)
            end
            i32.const 40
            call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
            unreachable
          end
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  block ;; label = @7
                    local.get 2
                    i32.eqz
                    br_if 0 (;@7;)
                    local.get 1
                    i32.load offset=36
                    local.tee 4
                    i32.const -1
                    i32.eq
                    br_if 1 (;@6;)
                    local.get 5
                    i32.const 8
                    i32.add
                    local.get 2
                    i32.load
                    local.tee 3
                    i32.load offset=4
                    local.get 3
                    i32.load
                    i32.load
                    call_indirect (type 3)
                    local.get 5
                    i32.load offset=12
                    local.set 3
                    local.get 5
                    i32.load offset=8
                    local.set 2
                    block ;; label = @8
                      local.get 1
                      i32.load offset=8
                      local.tee 7
                      i32.eqz
                      br_if 0 (;@8;)
                      local.get 1
                      i32.load offset=12
                      local.get 7
                      i32.load offset=12
                      call_indirect (type 1)
                    end
                    local.get 1
                    local.get 3
                    i32.store offset=12
                    local.get 1
                    local.get 2
                    i32.store offset=8
                    i32.const 0
                    call $wasip3_task_set
                    local.tee 3
                    i32.eqz
                    br_if 2 (;@5;)
                    local.get 3
                    i32.load
                    local.tee 2
                    i32.eqz
                    br_if 3 (;@4;)
                    block ;; label = @8
                      local.get 2
                      i32.const 1
                      i32.eq
                      br_if 0 (;@8;)
                      block ;; label = @9
                        block ;; label = @10
                          block ;; label = @11
                            local.get 1
                            i32.load offset=16
                            i32.const 2
                            i32.ne
                            br_if 0 (;@11;)
                            local.get 3
                            i32.load offset=4
                            local.set 2
                            br 1 (;@10;)
                          end
                          local.get 1
                          i32.load offset=28
                          local.get 3
                          i32.load offset=4
                          local.tee 2
                          i32.eq
                          br_if 1 (;@9;)
                        end
                        local.get 2
                        local.get 3
                        i32.load offset=16
                        i32.load offset=8
                        call_indirect (type 2)
                        local.set 2
                        local.get 3
                        i32.load offset=16
                        local.set 7
                        block ;; label = @10
                          local.get 1
                          i32.load offset=16
                          local.tee 11
                          i32.const 2
                          i32.eq
                          br_if 0 (;@10;)
                          block ;; label = @11
                            block ;; label = @12
                              local.get 11
                              i32.const 1
                              i32.and
                              br_if 0 (;@12;)
                              local.get 1
                              i32.load offset=28
                              local.set 11
                              local.get 1
                              i32.load offset=24
                              local.set 10
                              br 1 (;@11;)
                            end
                            local.get 1
                            i32.const 0
                            i32.store offset=16
                            local.get 1
                            i32.load offset=28
                            local.tee 11
                            local.get 1
                            i32.load offset=20
                            local.get 1
                            i32.load offset=24
                            local.tee 10
                            i32.load offset=4
                            call_indirect (type 0)
                            drop
                          end
                          local.get 11
                          local.get 10
                          i32.load offset=12
                          call_indirect (type 1)
                        end
                        local.get 1
                        local.get 2
                        i32.store offset=28
                        local.get 1
                        local.get 7
                        i32.store offset=24
                      end
                      local.get 1
                      local.get 4
                      i32.store offset=20
                      local.get 1
                      i32.const 1
                      i32.store offset=16
                    end
                    global.get $__table_base
                    local.set 2
                    block ;; label = @8
                      local.get 3
                      i32.load offset=4
                      local.get 4
                      local.get 2
                      i32.const 2
                      i32.add
                      local.get 1
                      local.get 3
                      i32.load offset=8
                      call_indirect (type 4)
                      local.tee 2
                      i32.eqz
                      br_if 0 (;@8;)
                      local.get 1
                      local.get 2
                      i32.ne
                      br_if 5 (;@3;)
                    end
                    local.get 3
                    call $wasip3_task_set
                    drop
                  end
                  local.get 0
                  i32.const 253
                  i32.store8
                  br 4 (;@2;)
                end
                call $_RNvNtCshQUFA83YM6w_4core6option13unwrap_failed
                unreachable
              end
              i32.const 33
              call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
              unreachable
            end
            i32.const 57
            call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
            unreachable
          end
          local.get 5
          i32.const 44
          i32.add
          local.get 5
          i32.const 24
          i32.add
          call $_RINvNtCshQUFA83YM6w_4core9panicking13assert_failedONtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable16CompletionStatusBM_ECs8o6ThntBNTu_6wasip3
          unreachable
        end
        local.get 5
        i32.const 48
        i32.add
        global.set $__stack_pointer
        return
      end
      call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
      unreachable
    )
    (func $_RINvNtCshQUFA83YM6w_4core9panicking13assert_failedONtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable16CompletionStatusBM_ECs8o6ThntBNTu_6wasip3 (;40;) (type 3) (param i32 i32)
      call $_RNvNtCshQUFA83YM6w_4core9panicking19assert_failed_inner
      unreachable
    )
    (func $_RNvNtCshQUFA83YM6w_4core6option13unwrap_failed (;41;) (type 7)
      i32.const 43
      call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
      unreachable
    )
    (func $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14stream_support14RawStreamWriteRINtBE_12StreamVtablehEEECsgR5kJmH8IIE_5hello (;42;) (type 1) (param i32)
      (local i32 i32 i32 i32)
      global.get $__stack_pointer
      i32.const 80
      i32.sub
      local.tee 1
      global.set $__stack_pointer
      block ;; label = @1
        local.get 0
        i32.load offset=16
        local.tee 2
        i32.const 2
        i32.eq
        br_if 0 (;@1;)
        local.get 0
        i32.const 16
        i32.add
        local.set 3
        block ;; label = @2
          block ;; label = @3
            local.get 2
            br_if 0 (;@3;)
            local.get 1
            i32.const 40
            i32.add
            local.get 3
            i32.const 36
            memory.copy
            local.get 3
            i32.const 2
            i32.store
            block ;; label = @4
              local.get 1
              i32.load offset=40
              br_if 0 (;@4;)
              local.get 1
              local.get 0
              i64.load offset=44 align=4
              i64.store offset=32 align=4
              local.get 1
              local.get 0
              i64.load offset=36 align=4
              i64.store offset=24 align=4
              local.get 1
              local.get 0
              i64.load offset=28 align=4
              i64.store offset=16 align=4
              local.get 1
              local.get 0
              i64.load offset=20 align=4
              i64.store offset=8 align=4
              local.get 1
              i32.const 2
              i32.store
              br 2 (;@2;)
            end
            local.get 1
            i32.const 40
            i32.add
            call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable22WaitableOperationStateINtNtBG_14stream_support13StreamWriteOpRINtB23_12StreamVtablehEEEECsgR5kJmH8IIE_5hello
            i32.const 40
            call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
            unreachable
          end
          local.get 0
          i32.load
          local.set 2
          local.get 0
          i32.const 0
          i32.store
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  block ;; label = @7
                    local.get 2
                    br_if 0 (;@7;)
                    local.get 0
                    i32.load offset=68
                    i32.load offset=4
                    local.set 2
                    block ;; label = @8
                      block ;; label = @9
                        local.get 0
                        i32.load offset=52
                        i32.const 2
                        i32.eq
                        br_if 0 (;@9;)
                        local.get 0
                        i32.const 0
                        i32.store offset=52
                        local.get 0
                        i32.load offset=64
                        local.get 2
                        local.get 0
                        i32.load offset=60
                        i32.load offset=4
                        call_indirect (type 0)
                        local.set 2
                        br 1 (;@8;)
                      end
                      i32.const 0
                      call $wasip3_task_set
                      local.tee 4
                      i32.eqz
                      br_if 2 (;@6;)
                      local.get 4
                      i32.load
                      i32.eqz
                      br_if 3 (;@5;)
                      local.get 4
                      i32.load offset=4
                      local.get 2
                      local.get 4
                      i32.load offset=12
                      call_indirect (type 0)
                      local.set 2
                      local.get 4
                      call $wasip3_task_set
                      drop
                    end
                    local.get 2
                    i32.eqz
                    br_if 4 (;@3;)
                    local.get 0
                    local.get 2
                    i32.ne
                    br_if 3 (;@4;)
                    br 4 (;@3;)
                  end
                  local.get 1
                  i32.const 40
                  i32.add
                  local.get 0
                  i32.const 0
                  i32.const 1
                  local.get 0
                  i32.load offset=4
                  call $_RNvMs2_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitableINtB5_17WaitableOperationINtNtB7_14stream_support13StreamWriteOpRINtB1v_12StreamVtablehEEE23poll_complete_with_codeCsgR5kJmH8IIE_5hello
                  local.get 1
                  i32.load offset=40
                  i32.const -1
                  i32.eq
                  br_if 3 (;@3;)
                  local.get 1
                  local.get 1
                  i32.const 40
                  i32.add
                  i32.const 40
                  memory.copy
                  br 4 (;@2;)
                end
                i32.const 33
                call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                unreachable
              end
              i32.const 57
              call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
              unreachable
            end
            local.get 1
            local.get 1
            i32.const 40
            i32.add
            call $_RINvNtCshQUFA83YM6w_4core9panicking13assert_failedONtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable16CompletionStatusBM_ECs8o6ThntBNTu_6wasip3
            unreachable
          end
          block ;; label = @3
            block ;; label = @4
              local.get 3
              i32.load
              i32.const 1
              i32.ne
              br_if 0 (;@4;)
              local.get 1
              i32.const 40
              i32.add
              local.get 0
              i32.const 0
              i32.const 1
              local.get 0
              i32.load offset=68
              local.tee 2
              i32.load offset=4
              local.get 2
              i32.load
              i32.load offset=16
              call_indirect (type 2)
              call $_RNvMs2_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitableINtB5_17WaitableOperationINtNtB7_14stream_support13StreamWriteOpRINtB1v_12StreamVtablehEEE23poll_complete_with_codeCsgR5kJmH8IIE_5hello
              local.get 1
              i32.load offset=40
              i32.const -1
              i32.ne
              br_if 1 (;@3;)
              i32.const 40
              call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
              unreachable
            end
            i32.const 40
            call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
            unreachable
          end
          local.get 1
          local.get 1
          i32.const 40
          i32.add
          i32.const 40
          memory.copy
        end
        local.get 1
        i32.const 8
        i32.add
        call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10abi_buffer9AbiBufferRINtNtBG_14stream_support12StreamVtablehEEECsgR5kJmH8IIE_5hello
        local.get 3
        i32.load
        i32.const 1
        i32.gt_u
        br_if 0 (;@1;)
        local.get 0
        i32.const 20
        i32.add
        call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10abi_buffer9AbiBufferRINtNtBG_14stream_support12StreamVtablehEEECsgR5kJmH8IIE_5hello
      end
      block ;; label = @1
        local.get 0
        i32.load offset=52
        local.tee 3
        i32.const 2
        i32.eq
        br_if 0 (;@1;)
        block ;; label = @2
          block ;; label = @3
            local.get 3
            i32.const 1
            i32.and
            br_if 0 (;@3;)
            local.get 0
            i32.load offset=64
            local.set 3
            local.get 0
            i32.load offset=60
            local.set 2
            br 1 (;@2;)
          end
          local.get 0
          i32.const 0
          i32.store offset=52
          local.get 0
          i32.load offset=64
          local.tee 3
          local.get 0
          i32.load offset=56
          local.get 0
          i32.load offset=60
          local.tee 2
          i32.load offset=4
          call_indirect (type 0)
          drop
        end
        local.get 3
        local.get 2
        i32.load offset=12
        call_indirect (type 1)
      end
      block ;; label = @1
        local.get 0
        i32.load offset=8
        local.tee 3
        i32.eqz
        br_if 0 (;@1;)
        local.get 0
        i32.load offset=12
        local.get 3
        i32.load offset=12
        call_indirect (type 1)
      end
      local.get 1
      i32.const 80
      i32.add
      global.set $__stack_pointer
    )
    (func $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable22WaitableOperationStateINtNtBG_14stream_support13StreamWriteOpRINtB23_12StreamVtablehEEEECsgR5kJmH8IIE_5hello (;43;) (type 1) (param i32)
      block ;; label = @1
        local.get 0
        i32.load
        i32.const 1
        i32.gt_u
        br_if 0 (;@1;)
        local.get 0
        i32.const 4
        i32.add
        call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10abi_buffer9AbiBufferRINtNtBG_14stream_support12StreamVtablehEEECsgR5kJmH8IIE_5hello
      end
    )
    (func $_RNvMs2_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitableINtB5_17WaitableOperationINtNtB7_14stream_support13StreamWriteOpRINtB1v_12StreamVtablehEEE23poll_complete_with_codeCsgR5kJmH8IIE_5hello (;44;) (type 9) (param i32 i32 i32 i32 i32)
      (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
      global.get $__stack_pointer
      i32.const 64
      i32.sub
      local.tee 5
      global.set $__stack_pointer
      local.get 1
      i32.const 16
      i32.add
      local.set 6
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  block ;; label = @7
                    local.get 3
                    i32.const 1
                    i32.ne
                    br_if 0 (;@7;)
                    block ;; label = @8
                      local.get 1
                      i32.load offset=52
                      i32.const 2
                      i32.eq
                      br_if 0 (;@8;)
                      local.get 1
                      i32.const 0
                      i32.store offset=52
                    end
                    local.get 5
                    i32.const 24
                    i32.add
                    local.get 6
                    i32.const 36
                    memory.copy
                    local.get 1
                    i32.const 2
                    i32.store offset=16
                    block ;; label = @8
                      local.get 5
                      i32.load offset=24
                      i32.const 1
                      i32.ne
                      br_if 0 (;@8;)
                      local.get 5
                      i32.load offset=56
                      local.set 6
                      local.get 5
                      i32.load offset=52
                      local.set 3
                      local.get 5
                      i32.load offset=48
                      local.set 7
                      local.get 5
                      i32.load offset=44
                      local.set 8
                      local.get 5
                      i32.load offset=40
                      local.set 9
                      local.get 5
                      i32.load offset=36
                      local.set 10
                      local.get 5
                      i32.load offset=32
                      local.set 11
                      local.get 5
                      i32.load offset=28
                      local.set 12
                      local.get 5
                      i32.const 16
                      i32.add
                      local.get 4
                      call $_RNvMs4_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB5_10ReturnCode6decode
                      local.get 5
                      i32.load offset=20
                      local.set 13
                      block ;; label = @9
                        block ;; label = @10
                          block ;; label = @11
                            block ;; label = @12
                              local.get 5
                              i32.load offset=16
                              local.tee 14
                              br_table 8 (;@4;) 2 (;@10;) 0 (;@12;) 1 (;@11;) 8 (;@4;)
                            end
                            local.get 13
                            br_if 1 (;@10;)
                            i32.const 1
                            local.set 2
                            br 2 (;@9;)
                          end
                          local.get 13
                          br_if 0 (;@10;)
                          i32.const 2
                          local.set 2
                          br 1 (;@9;)
                        end
                        local.get 13
                        local.get 6
                        i32.add
                        local.tee 15
                        local.get 10
                        i32.gt_u
                        br_if 3 (;@6;)
                        block ;; label = @10
                          block ;; label = @11
                            local.get 3
                            i32.load offset=40
                            i32.eqz
                            br_if 0 (;@11;)
                            block ;; label = @12
                              block ;; label = @13
                                local.get 3
                                i32.load offset=44
                                i32.eqz
                                br_if 0 (;@13;)
                                local.get 7
                                i32.const 0
                                local.get 9
                                select
                                local.get 3
                                i32.load offset=4
                                local.get 6
                                i32.mul
                                i32.add
                                local.set 2
                                br 1 (;@12;)
                              end
                              local.get 11
                              local.get 6
                              i32.add
                              local.set 2
                            end
                            local.get 13
                            local.get 10
                            local.get 6
                            i32.sub
                            i32.gt_u
                            br_if 6 (;@5;)
                            local.get 13
                            i32.eqz
                            br_if 1 (;@10;)
                            local.get 13
                            local.set 6
                            loop ;; label = @12
                              block ;; label = @13
                                local.get 3
                                i32.load offset=40
                                local.tee 4
                                i32.eqz
                                br_if 0 (;@13;)
                                local.get 2
                                local.get 4
                                call_indirect (type 1)
                              end
                              local.get 2
                              local.get 3
                              i32.load offset=4
                              i32.add
                              local.set 2
                              local.get 6
                              i32.const -1
                              i32.add
                              local.tee 6
                              br_if 0 (;@12;)
                            end
                          end
                          local.get 15
                          local.set 6
                        end
                        i32.const 0
                        local.set 2
                        local.get 14
                        i32.const 2
                        i32.ne
                        br_if 0 (;@9;)
                        local.get 1
                        i32.load offset=68
                        i32.const 1
                        i32.store8 offset=8
                      end
                      local.get 0
                      local.get 6
                      i32.store offset=36
                      local.get 0
                      local.get 3
                      i32.store offset=32
                      local.get 0
                      local.get 7
                      i32.store offset=28
                      local.get 0
                      local.get 8
                      i32.store offset=24
                      local.get 0
                      local.get 9
                      i32.store offset=20
                      local.get 0
                      local.get 10
                      i32.store offset=16
                      local.get 0
                      local.get 11
                      i32.store offset=12
                      local.get 0
                      local.get 12
                      i32.store offset=8
                      local.get 0
                      local.get 13
                      i32.store offset=4
                      local.get 0
                      local.get 2
                      i32.store
                      br 7 (;@1;)
                    end
                    local.get 5
                    i32.const 24
                    i32.add
                    call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable22WaitableOperationStateINtNtBG_14stream_support13StreamWriteOpRINtB23_12StreamVtablehEEEECsgR5kJmH8IIE_5hello
                    i32.const 40
                    call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                    unreachable
                  end
                  local.get 6
                  i32.load
                  i32.const 1
                  i32.ne
                  br_if 3 (;@3;)
                  br 4 (;@2;)
                end
                i32.const 62
                call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                unreachable
              end
              i32.const 28
              call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
              unreachable
            end
            local.get 1
            local.get 6
            i32.store offset=48
            local.get 1
            local.get 3
            i32.store offset=44
            local.get 1
            local.get 7
            i32.store offset=40
            local.get 1
            local.get 8
            i32.store offset=36
            local.get 1
            local.get 9
            i32.store offset=32
            local.get 1
            local.get 10
            i32.store offset=28
            local.get 1
            local.get 11
            i32.store offset=24
            local.get 1
            local.get 12
            i32.store offset=20
            local.get 1
            i32.const 1
            i32.store offset=16
            br 1 (;@2;)
          end
          i32.const 40
          call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
          unreachable
        end
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                local.get 2
                i32.eqz
                br_if 0 (;@5;)
                local.get 1
                i32.load offset=68
                i32.load offset=4
                local.set 3
                local.get 5
                i32.const 8
                i32.add
                local.get 2
                i32.load
                local.tee 2
                i32.load offset=4
                local.get 2
                i32.load
                i32.load
                call_indirect (type 3)
                local.get 5
                i32.load offset=12
                local.set 2
                local.get 5
                i32.load offset=8
                local.set 6
                block ;; label = @6
                  local.get 1
                  i32.load offset=8
                  local.tee 4
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 1
                  i32.load offset=12
                  local.get 4
                  i32.load offset=12
                  call_indirect (type 1)
                end
                local.get 1
                local.get 2
                i32.store offset=12
                local.get 1
                local.get 6
                i32.store offset=8
                i32.const 0
                call $wasip3_task_set
                local.tee 2
                i32.eqz
                br_if 1 (;@4;)
                local.get 2
                i32.load
                local.tee 6
                i32.eqz
                br_if 2 (;@3;)
                block ;; label = @6
                  local.get 6
                  i32.const 1
                  i32.eq
                  br_if 0 (;@6;)
                  block ;; label = @7
                    block ;; label = @8
                      block ;; label = @9
                        local.get 1
                        i32.load offset=52
                        i32.const 2
                        i32.ne
                        br_if 0 (;@9;)
                        local.get 2
                        i32.load offset=4
                        local.set 6
                        br 1 (;@8;)
                      end
                      local.get 1
                      i32.load offset=64
                      local.get 2
                      i32.load offset=4
                      local.tee 6
                      i32.eq
                      br_if 1 (;@7;)
                    end
                    local.get 6
                    local.get 2
                    i32.load offset=16
                    i32.load offset=8
                    call_indirect (type 2)
                    local.set 6
                    local.get 2
                    i32.load offset=16
                    local.set 4
                    block ;; label = @8
                      local.get 1
                      i32.load offset=52
                      local.tee 13
                      i32.const 2
                      i32.eq
                      br_if 0 (;@8;)
                      block ;; label = @9
                        block ;; label = @10
                          local.get 13
                          i32.const 1
                          i32.and
                          br_if 0 (;@10;)
                          local.get 1
                          i32.load offset=64
                          local.set 13
                          local.get 1
                          i32.load offset=60
                          local.set 10
                          br 1 (;@9;)
                        end
                        local.get 1
                        i32.const 0
                        i32.store offset=52
                        local.get 1
                        i32.load offset=64
                        local.tee 13
                        local.get 1
                        i32.load offset=56
                        local.get 1
                        i32.load offset=60
                        local.tee 10
                        i32.load offset=4
                        call_indirect (type 0)
                        drop
                      end
                      local.get 13
                      local.get 10
                      i32.load offset=12
                      call_indirect (type 1)
                    end
                    local.get 1
                    local.get 6
                    i32.store offset=64
                    local.get 1
                    local.get 4
                    i32.store offset=60
                  end
                  local.get 1
                  local.get 3
                  i32.store offset=56
                  local.get 1
                  i32.const 1
                  i32.store offset=52
                end
                global.get $__table_base
                local.set 6
                block ;; label = @6
                  local.get 2
                  i32.load offset=4
                  local.get 3
                  local.get 6
                  i32.const 2
                  i32.add
                  local.get 1
                  local.get 2
                  i32.load offset=8
                  call_indirect (type 4)
                  local.tee 3
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 1
                  local.get 3
                  i32.ne
                  br_if 4 (;@2;)
                end
                local.get 2
                call $wasip3_task_set
                drop
              end
              local.get 0
              i32.const -1
              i32.store
              br 3 (;@1;)
            end
            i32.const 33
            call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
            unreachable
          end
          i32.const 57
          call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
          unreachable
        end
        local.get 5
        i32.const 60
        i32.add
        local.get 5
        i32.const 24
        i32.add
        call $_RINvNtCshQUFA83YM6w_4core9panicking13assert_failedONtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable16CompletionStatusBM_ECs8o6ThntBNTu_6wasip3
        unreachable
      end
      local.get 5
      i32.const 64
      i32.add
      global.set $__stack_pointer
    )
    (func $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueNCINvNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run16__export_run_cabiNtCsgR5kJmH8IIE_5hello5HelloE0EB1Z_ (;45;) (type 1) (param i32)
      block ;; label = @1
        local.get 0
        i32.load8_u offset=240
        i32.const 3
        i32.ne
        br_if 0 (;@1;)
        local.get 0
        call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueNCNvXCsgR5kJmH8IIE_5helloNtBG_5HelloNtNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run5Guest3run0EBG_
        call $_RNvNvXs6_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB7_16TaskCancelOnDropNtNtNtCshQUFA83YM6w_4core3ops4drop4Drop4drop6cancel
      end
    )
    (func $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueNCNvXCsgR5kJmH8IIE_5helloNtBG_5HelloNtNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run5Guest3run0EBG_ (;46;) (type 1) (param i32)
      block ;; label = @1
        local.get 0
        i32.load8_u offset=236
        i32.const 3
        i32.ne
        br_if 0 (;@1;)
        local.get 0
        i32.const 72
        i32.add
        call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtCs22k8fyVPmoz_12futures_util6future10maybe_done9MaybeDoneNCNCNvXCsgR5kJmH8IIE_5helloNtB1K_5HelloNtNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run5Guest3run0s0_0EEB1K_
        local.get 0
        call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtCs22k8fyVPmoz_12futures_util6future10maybe_done9MaybeDoneNCNCNvXCsgR5kJmH8IIE_5helloNtB1K_5HelloNtNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run5Guest3run0s_0EEB1K_
      end
    )
    (func $_RNCINvNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run16__export_run_cabiNtCsgR5kJmH8IIE_5hello5HelloE0B1n_ (;47;) (type 0) (param i32 i32) (result i32)
      (local i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
      global.get $__stack_pointer
      i32.const 128
      i32.sub
      local.tee 2
      global.set $__stack_pointer
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  block ;; label = @7
                    block ;; label = @8
                      block ;; label = @9
                        block ;; label = @10
                          block ;; label = @11
                            block ;; label = @12
                              block ;; label = @13
                                block ;; label = @14
                                  block ;; label = @15
                                    block ;; label = @16
                                      block ;; label = @17
                                        block ;; label = @18
                                          block ;; label = @19
                                            block ;; label = @20
                                              block ;; label = @21
                                                block ;; label = @22
                                                  block ;; label = @23
                                                    block ;; label = @24
                                                      local.get 0
                                                      i32.load8_u offset=240
                                                      br_table 1 (;@23;) 15 (;@9;) 9 (;@15;) 0 (;@24;) 1 (;@23;)
                                                    end
                                                    local.get 0
                                                    i32.const 236
                                                    i32.add
                                                    local.set 3
                                                    local.get 0
                                                    i32.load8_u offset=236
                                                    br_table 1 (;@22;) 14 (;@9;) 8 (;@15;) 2 (;@21;) 1 (;@22;)
                                                  end
                                                  local.get 0
                                                  i32.const 0
                                                  i32.store8 offset=236
                                                  local.get 0
                                                  i32.const 236
                                                  i32.add
                                                  local.set 3
                                                end
                                                call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports3new
                                                local.set 4
                                                local.get 0
                                                i32.const 0
                                                i32.store8 offset=224
                                                local.get 0
                                                i32.const 0
                                                i32.store8 offset=220
                                                local.get 0
                                                i32.const 0
                                                i32.store offset=72
                                                local.get 0
                                                i32.const 0
                                                i32.store8 offset=68
                                                local.get 0
                                                i32.const 0
                                                i32.store8 offset=64
                                                local.get 0
                                                local.get 4
                                                i64.store32 offset=60
                                                local.get 0
                                                i32.const 0
                                                i32.store8
                                                local.get 0
                                                local.get 0
                                                i32.const 72
                                                i32.add
                                                i32.store offset=232
                                                local.get 0
                                                local.get 4
                                                i64.const 32
                                                i64.shr_u
                                                i64.store32 offset=216
                                                local.get 0
                                                global.get $__memory_base
                                                i32.const 1049220
                                                i32.add
                                                local.tee 5
                                                i32.store offset=212
                                                local.get 0
                                                local.get 5
                                                i32.store offset=56
                                                local.get 0
                                                local.get 0
                                                i32.store offset=228
                                                local.get 0
                                                i32.const 4
                                                i32.add
                                                local.set 6
                                                local.get 0
                                                i32.const 68
                                                i32.add
                                                local.set 7
                                                local.get 0
                                                local.set 8
                                                br 1 (;@20;)
                                              end
                                              i32.const 1
                                              local.set 9
                                              local.get 0
                                              i32.load offset=228
                                              local.tee 8
                                              i32.load8_u
                                              local.tee 5
                                              i32.const 1
                                              i32.eq
                                              br_if 4 (;@16;)
                                              block ;; label = @21
                                                block ;; label = @22
                                                  local.get 5
                                                  br_table 0 (;@22;) 7 (;@15;) 1 (;@21;) 0 (;@22;)
                                                end
                                                local.get 8
                                                i32.const 4
                                                i32.add
                                                local.set 6
                                                local.get 8
                                                i32.const 68
                                                i32.add
                                                local.set 7
                                                block ;; label = @22
                                                  local.get 8
                                                  i32.load8_u offset=68
                                                  br_table 2 (;@20;) 13 (;@9;) 7 (;@15;) 0 (;@22;) 2 (;@20;)
                                                end
                                                block ;; label = @22
                                                  local.get 8
                                                  i32.load offset=44
                                                  local.tee 5
                                                  i32.const -2147483647
                                                  i32.lt_u
                                                  br_if 0 (;@22;)
                                                  local.get 5
                                                  i32.const -2147483647
                                                  i32.ne
                                                  br_if 5 (;@17;)
                                                  br 3 (;@19;)
                                                end
                                                local.get 8
                                                i32.load offset=4
                                                local.set 5
                                                local.get 8
                                                i32.const 0
                                                i32.store offset=4
                                                local.get 8
                                                i32.load offset=8
                                                local.set 10
                                                br 3 (;@18;)
                                              end
                                              i32.const 34
                                              call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                                              unreachable
                                            end
                                            local.get 8
                                            i32.load offset=60
                                            local.tee 5
                                            i32.const -1
                                            i32.eq
                                            br_if 18 (;@1;)
                                            local.get 5
                                            call $_RNvNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli6stdout16write_via_stream11wit_import0
                                            local.set 5
                                            local.get 6
                                            i32.const 0
                                            i32.store
                                            local.get 8
                                            i32.const -2147483647
                                            i32.store offset=44
                                            local.get 8
                                            local.get 5
                                            i32.store offset=40
                                            local.get 8
                                            global.get $__memory_base
                                            i32.const 1049172
                                            i32.add
                                            i32.store offset=36
                                            local.get 8
                                            i32.const 2
                                            i32.store offset=20
                                            local.get 8
                                            i32.const 0
                                            i32.store offset=12
                                          end
                                          local.get 8
                                          i64.load offset=44 align=4
                                          local.set 4
                                          local.get 8
                                          i32.const -2147483645
                                          i32.store offset=44
                                          local.get 2
                                          local.get 8
                                          i32.load offset=52
                                          i32.store offset=104
                                          local.get 2
                                          local.get 4
                                          i64.store offset=96
                                          local.get 2
                                          local.get 8
                                          i64.load offset=36 align=4
                                          i64.store offset=88
                                          block ;; label = @19
                                            local.get 4
                                            i32.wrap_i64
                                            i32.const -2147483647
                                            i32.ne
                                            br_if 0 (;@19;)
                                            local.get 2
                                            i32.load offset=92
                                            local.set 5
                                            local.get 2
                                            i32.const 88
                                            i32.add
                                            local.get 2
                                            i32.load offset=88
                                            local.tee 11
                                            i32.load
                                            local.get 11
                                            i32.load offset=4
                                            call $_RNvMs1_NtCscNOpLhlpk4u_11wit_bindgen2rtNtB5_7Cleanup3new
                                            local.get 5
                                            i32.const -1
                                            i32.eq
                                            br_if 18 (;@1;)
                                            local.get 5
                                            local.get 2
                                            i32.load offset=88
                                            local.get 11
                                            i32.load offset=24
                                            call_indirect (type 0)
                                            local.set 10
                                            local.get 2
                                            local.get 2
                                            i32.load offset=100
                                            i32.store offset=64
                                            local.get 2
                                            local.get 2
                                            i64.load offset=92 align=4
                                            i64.store offset=56
                                            local.get 8
                                            i32.const 36
                                            i32.add
                                            call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable22WaitableOperationStateINtNtBG_14future_support12FutureReadOpRINtB23_12FutureVtableINtNtB4_6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEEECsgR5kJmH8IIE_5hello
                                            local.get 8
                                            local.get 5
                                            i32.store offset=40
                                            local.get 8
                                            local.get 11
                                            i32.store offset=36
                                            local.get 8
                                            i32.const 44
                                            i32.add
                                            local.tee 5
                                            local.get 2
                                            i64.load offset=56
                                            i64.store align=4
                                            local.get 5
                                            local.get 2
                                            i32.load offset=64
                                            i32.store offset=8
                                            i32.const 1
                                            local.set 5
                                            br 1 (;@18;)
                                          end
                                          local.get 2
                                          i32.const 88
                                          i32.add
                                          call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable22WaitableOperationStateINtNtBG_14future_support12FutureReadOpRINtB23_12FutureVtableINtNtB4_6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEEECsgR5kJmH8IIE_5hello
                                          i32.const 40
                                          call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                                          unreachable
                                        end
                                        local.get 2
                                        i32.const 24
                                        i32.add
                                        local.get 6
                                        local.get 1
                                        local.get 5
                                        local.get 10
                                        call $_RNvMs2_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitableINtB5_17WaitableOperationINtNtB7_14future_support12FutureReadOpRINtB1v_12FutureVtableINtNtCshQUFA83YM6w_4core6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEE23poll_complete_with_codeCsgR5kJmH8IIE_5hello
                                        block ;; label = @18
                                          local.get 2
                                          i32.load8_u offset=24
                                          local.tee 5
                                          i32.const 253
                                          i32.eq
                                          br_if 0 (;@18;)
                                          local.get 5
                                          i32.const 254
                                          i32.eq
                                          br_if 1 (;@17;)
                                          block ;; label = @19
                                            local.get 2
                                            i32.load offset=32
                                            local.tee 11
                                            i32.const -1
                                            i32.eq
                                            br_if 0 (;@19;)
                                            local.get 11
                                            local.get 2
                                            i32.load offset=28
                                            i32.load offset=40
                                            call_indirect (type 1)
                                          end
                                          local.get 6
                                          call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14future_support13RawFutureReadRINtBE_12FutureVtableINtNtB4_6result6ResultuNtNtNtNtNtCs8o6ThntBNTu_6wasip37imports4wasi3cli5types9ErrorCodeEEEECsgR5kJmH8IIE_5hello
                                          i32.const 1
                                          local.set 9
                                          local.get 7
                                          i32.const 1
                                          i32.store8
                                          local.get 8
                                          call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtCs22k8fyVPmoz_12futures_util6future10maybe_done9MaybeDoneNCNCNvXCsgR5kJmH8IIE_5helloNtB1K_5HelloNtNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run5Guest3run0s_0EEB1K_
                                          local.get 8
                                          local.get 5
                                          i32.store8 offset=1
                                          local.get 8
                                          i32.const 1
                                          i32.store8
                                          br 2 (;@16;)
                                        end
                                        local.get 7
                                        i32.const 3
                                        i32.store8
                                        i32.const 0
                                        local.set 9
                                        br 1 (;@16;)
                                      end
                                      call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
                                      unreachable
                                    end
                                    block ;; label = @16
                                      local.get 0
                                      i32.load offset=232
                                      local.tee 5
                                      i32.load
                                      br_table 0 (;@16;) 10 (;@6;) 5 (;@11;) 0 (;@16;)
                                    end
                                    local.get 5
                                    i32.const 4
                                    i32.add
                                    local.set 12
                                    block ;; label = @16
                                      block ;; label = @17
                                        local.get 5
                                        i32.load8_u offset=152
                                        br_table 0 (;@17;) 8 (;@9;) 2 (;@15;) 1 (;@16;) 0 (;@17;)
                                      end
                                      i32.const 17
                                      local.set 13
                                      i32.const 17
                                      call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCskAuRjb5C0Ki_4p3rt
                                      local.tee 14
                                      i32.eqz
                                      br_if 6 (;@10;)
                                      local.get 14
                                      global.get $__memory_base
                                      i32.const 1048576
                                      i32.add
                                      local.tee 15
                                      i32.load8_u offset=16
                                      i32.store8 offset=16
                                      local.get 14
                                      local.get 15
                                      i64.load offset=8 align=1
                                      i64.store offset=8 align=1
                                      local.get 14
                                      local.get 15
                                      i64.load align=1
                                      i64.store align=1
                                      local.get 5
                                      i32.const 0
                                      i32.store8 offset=24
                                      local.get 5
                                      local.get 5
                                      i32.const 140
                                      i32.add
                                      local.tee 16
                                      i32.store offset=16
                                      local.get 5
                                      i32.const 17
                                      i32.store offset=12
                                      local.get 5
                                      local.get 14
                                      i32.store offset=8
                                      local.get 5
                                      i32.const 17
                                      i32.store offset=4
                                      local.get 5
                                      i32.const 24
                                      i32.add
                                      local.set 17
                                      i32.const 17
                                      local.set 18
                                      br 3 (;@13;)
                                    end
                                    local.get 5
                                    i32.const 24
                                    i32.add
                                    local.set 17
                                    local.get 5
                                    i32.load8_u offset=24
                                    br_table 1 (;@14;) 6 (;@9;) 0 (;@15;) 3 (;@12;) 7 (;@8;) 1 (;@14;)
                                  end
                                  unreachable
                                end
                                local.get 5
                                i32.load offset=12
                                local.set 13
                                local.get 5
                                i32.load offset=8
                                local.set 14
                                local.get 5
                                i32.load offset=4
                                local.set 18
                                local.get 5
                                i32.load offset=16
                                local.set 16
                              end
                              local.get 5
                              local.get 16
                              i32.store offset=20
                              block ;; label = @13
                                block ;; label = @14
                                  local.get 16
                                  i32.load
                                  local.tee 19
                                  i32.load offset=44
                                  br_if 0 (;@14;)
                                  i32.const 0
                                  local.set 20
                                  br 1 (;@13;)
                                end
                                local.get 19
                                i32.load
                                local.tee 15
                                local.get 15
                                i32.const -1
                                i32.add
                                i32.and
                                br_if 4 (;@9;)
                                local.get 19
                                i32.load offset=4
                                local.tee 7
                                local.get 13
                                i32.mul
                                local.tee 11
                                i32.const -2147483648
                                local.get 15
                                i32.sub
                                i32.gt_u
                                br_if 4 (;@9;)
                                local.get 2
                                i32.const 88
                                i32.add
                                local.get 15
                                local.get 11
                                call $_RNvMs1_NtCscNOpLhlpk4u_11wit_bindgen2rtNtB5_7Cleanup3new
                                local.get 2
                                i64.load offset=96 align=4
                                local.set 4
                                local.get 2
                                i32.load offset=92
                                local.set 20
                                local.get 13
                                i32.eqz
                                br_if 0 (;@13;)
                                local.get 19
                                i32.load offset=36
                                local.tee 10
                                i32.eqz
                                br_if 0 (;@13;)
                                local.get 2
                                i32.load offset=88
                                local.set 15
                                local.get 13
                                local.set 6
                                local.get 14
                                local.set 11
                                loop ;; label = @14
                                  local.get 11
                                  i32.load8_u
                                  local.get 15
                                  local.get 10
                                  call_indirect (type 3)
                                  local.get 15
                                  local.get 7
                                  i32.add
                                  local.set 15
                                  local.get 11
                                  i32.const 1
                                  i32.add
                                  local.set 11
                                  local.get 6
                                  i32.const -1
                                  i32.add
                                  local.tee 6
                                  br_if 0 (;@14;)
                                end
                              end
                              local.get 5
                              local.get 16
                              i32.store offset=96
                              local.get 5
                              i64.const 8589934592
                              i64.store offset=76 align=4
                              local.get 5
                              local.get 19
                              i32.store offset=72
                              local.get 5
                              local.get 4
                              i64.store offset=64 align=4
                              local.get 5
                              local.get 20
                              i32.store offset=60
                              local.get 5
                              local.get 13
                              i32.store offset=56
                              local.get 5
                              local.get 14
                              i32.store offset=52
                              local.get 5
                              local.get 18
                              i32.store offset=48
                              local.get 5
                              i32.const 0
                              i32.store offset=44
                              local.get 5
                              i32.const 0
                              i32.store offset=36
                              local.get 5
                              i32.const 0
                              i32.store offset=28
                            end
                            local.get 2
                            i32.const 88
                            i32.add
                            local.get 5
                            i32.const 28
                            i32.add
                            local.tee 11
                            local.get 1
                            call $_RNvXs3_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14stream_supportINtB5_14RawStreamWriteRINtB5_12StreamVtablehEENtNtNtCshQUFA83YM6w_4core6future6future6Future4pollCsgR5kJmH8IIE_5hello
                            block ;; label = @12
                              local.get 2
                              i32.load offset=88
                              local.tee 15
                              i32.const -1
                              i32.ne
                              br_if 0 (;@12;)
                              i32.const 3
                              local.set 15
                              br 7 (;@5;)
                            end
                            local.get 2
                            local.get 2
                            i64.load offset=96 align=4
                            i64.store offset=24
                            local.get 2
                            local.get 2
                            i64.load offset=104 align=4
                            i64.store offset=32
                            local.get 2
                            local.get 2
                            i64.load offset=112 align=4
                            i64.store offset=40
                            local.get 2
                            local.get 2
                            i64.load offset=120 align=4
                            i64.store offset=48
                            local.get 2
                            i32.load offset=92
                            local.set 6
                            local.get 11
                            call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14stream_support14RawStreamWriteRINtBE_12StreamVtablehEEECsgR5kJmH8IIE_5hello
                            local.get 5
                            local.get 6
                            i32.store offset=32
                            local.get 5
                            local.get 15
                            i32.store offset=28
                            local.get 5
                            local.get 2
                            i64.load offset=24
                            i64.store offset=108 align=4
                            local.get 5
                            local.get 2
                            i64.load offset=32
                            i64.store offset=116 align=4
                            local.get 5
                            local.get 2
                            i64.load offset=40
                            i64.store offset=124 align=4
                            local.get 5
                            local.get 2
                            i64.load offset=48
                            i64.store offset=132 align=4
                            i32.const 0
                            local.set 11
                            br 4 (;@7;)
                          end
                          i32.const 34
                          call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                          unreachable
                        end
                        i32.const 1
                        i32.const 17
                        call $_RNvNtCsiqQVI2xHy0t_5alloc7raw_vec12handle_error
                        unreachable
                      end
                      call $_RNvNtCshQUFA83YM6w_4core6result13unwrap_failed
                      unreachable
                    end
                    i32.const 1
                    local.set 11
                  end
                  loop ;; label = @7
                    block ;; label = @8
                      block ;; label = @9
                        block ;; label = @10
                          block ;; label = @11
                            block ;; label = @12
                              block ;; label = @13
                                local.get 11
                                br_table 0 (;@13;) 1 (;@12;) 1 (;@12;)
                              end
                              local.get 5
                              i32.load offset=136
                              local.set 11
                              local.get 5
                              i32.load offset=116
                              local.set 6
                              local.get 15
                              br_if 1 (;@11;)
                              local.get 6
                              local.get 11
                              i32.eq
                              br_if 2 (;@10;)
                              local.get 5
                              i32.const 0
                              i32.store offset=52
                              local.get 5
                              i32.const 0
                              i32.store offset=44
                              local.get 5
                              i32.const 0
                              i32.store offset=36
                              local.get 5
                              i32.const 2
                              i32.store offset=88
                              local.get 5
                              local.get 5
                              i64.load offset=108 align=4
                              i64.store offset=56 align=4
                              local.get 5
                              local.get 5
                              i64.load offset=116 align=4
                              i64.store offset=64 align=4
                              local.get 5
                              local.get 5
                              i64.load offset=124 align=4
                              i64.store offset=72 align=4
                              local.get 5
                              local.get 5
                              i64.load offset=132 align=4
                              i64.store offset=80 align=4
                              local.get 5
                              local.get 5
                              i32.load offset=20
                              i32.store offset=104
                              i32.const 1
                              local.set 11
                              br 5 (;@7;)
                            end
                            local.get 2
                            i32.const 88
                            i32.add
                            local.get 5
                            i32.const 36
                            i32.add
                            local.tee 11
                            local.get 1
                            call $_RNvXs3_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14stream_supportINtB5_14RawStreamWriteRINtB5_12StreamVtablehEENtNtNtCshQUFA83YM6w_4core6future6future6Future4pollCsgR5kJmH8IIE_5hello
                            block ;; label = @12
                              local.get 2
                              i32.load offset=88
                              local.tee 15
                              i32.const -1
                              i32.ne
                              br_if 0 (;@12;)
                              i32.const 4
                              local.set 15
                              br 7 (;@5;)
                            end
                            local.get 2
                            i32.load offset=92
                            local.set 6
                            local.get 2
                            local.get 2
                            i64.load offset=120 align=4
                            i64.store offset=80
                            local.get 2
                            local.get 2
                            i64.load offset=112 align=4
                            i64.store offset=72
                            local.get 2
                            local.get 2
                            i64.load offset=104 align=4
                            i64.store offset=64
                            local.get 2
                            local.get 2
                            i64.load offset=96 align=4
                            i64.store offset=56
                            local.get 11
                            call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14stream_support14RawStreamWriteRINtBE_12StreamVtablehEEECsgR5kJmH8IIE_5hello
                            local.get 5
                            local.get 6
                            i32.store offset=32
                            local.get 5
                            local.get 15
                            i32.store offset=28
                            local.get 5
                            local.get 2
                            i64.load offset=56
                            i64.store offset=108 align=4
                            local.get 5
                            local.get 2
                            i64.load offset=64
                            i64.store offset=116 align=4
                            local.get 5
                            local.get 2
                            i64.load offset=72
                            i64.store offset=124 align=4
                            local.get 5
                            local.get 2
                            i64.load offset=80
                            i64.store offset=132 align=4
                            local.get 15
                            i32.const 2
                            i32.ne
                            br_if 3 (;@8;)
                            local.get 5
                            i64.const 0
                            i64.store offset=28 align=4
                            i32.const 0
                            local.set 15
                            br 3 (;@8;)
                          end
                          local.get 15
                          i32.const 1
                          i32.eq
                          br_if 0 (;@10;)
                          local.get 6
                          local.get 11
                          i32.ne
                          br_if 1 (;@9;)
                        end
                        local.get 2
                        local.get 5
                        i64.load offset=132 align=4
                        i64.store offset=112
                        local.get 2
                        local.get 5
                        i64.load offset=124 align=4
                        i64.store offset=104
                        local.get 2
                        local.get 5
                        i64.load offset=116 align=4
                        i64.store offset=96
                        local.get 2
                        local.get 5
                        i64.load offset=108 align=4
                        i64.store offset=88
                        local.get 2
                        i32.const 12
                        i32.add
                        local.get 2
                        i32.const 88
                        i32.add
                        call $_RNvMNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10abi_bufferINtB2_9AbiBufferRINtNtB4_14stream_support12StreamVtablehEE8take_vecCsgR5kJmH8IIE_5hello
                        local.get 2
                        i32.const 88
                        i32.add
                        call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10abi_buffer9AbiBufferRINtNtBG_14stream_support12StreamVtablehEEECsgR5kJmH8IIE_5hello
                        local.get 5
                        i32.const 1
                        i32.store8 offset=24
                        local.get 2
                        i32.load offset=12
                        i32.const -1
                        i32.eq
                        br_if 5 (;@4;)
                        local.get 2
                        i32.load offset=20
                        local.set 15
                        local.get 2
                        i32.load offset=16
                        local.set 11
                        local.get 2
                        i32.load offset=12
                        local.set 6
                        local.get 12
                        call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueNCNvMs_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14stream_supportINtBI_15RawStreamWriterRINtBI_12StreamVtablehEE9write_all0ECsgR5kJmH8IIE_5hello
                        block ;; label = @10
                          local.get 15
                          i32.eqz
                          br_if 0 (;@10;)
                          i32.const 33
                          call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                          unreachable
                        end
                        local.get 5
                        i32.load offset=144
                        local.get 5
                        i32.load offset=140
                        i32.load offset=24
                        call_indirect (type 1)
                        local.get 6
                        local.get 11
                        call $_RNvMs3_NtCsiqQVI2xHy0t_5alloc7raw_vecNtB5_11RawVecInner10deallocateCscNOpLhlpk4u_11wit_bindgen
                        local.get 5
                        i32.const 1
                        i32.store8 offset=152
                        local.get 5
                        call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtCs22k8fyVPmoz_12futures_util6future10maybe_done9MaybeDoneNCNCNvXCsgR5kJmH8IIE_5helloNtB1K_5HelloNtNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run5Guest3run0s0_0EEB1K_
                        local.get 5
                        i32.const 1
                        i32.store
                        br 3 (;@6;)
                      end
                      i32.const 81
                      call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                      unreachable
                    end
                    i32.const 0
                    local.set 11
                    br 0 (;@7;)
                  end
                end
                local.get 9
                i32.eqz
                br_if 2 (;@3;)
                local.get 8
                i32.load8_u
                i32.const 1
                i32.ne
                br_if 4 (;@1;)
                local.get 8
                i32.const 2
                i32.store8
                local.get 8
                i32.load8_u offset=1
                local.tee 11
                i32.const 254
                i32.eq
                br_if 4 (;@1;)
                i32.const 1
                local.set 15
                local.get 5
                i32.load
                i32.const 1
                i32.ne
                br_if 4 (;@1;)
                local.get 5
                i32.const 2
                i32.store
                local.get 0
                i32.const 72
                i32.add
                call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtCs22k8fyVPmoz_12futures_util6future10maybe_done9MaybeDoneNCNCNvXCsgR5kJmH8IIE_5helloNtB1K_5HelloNtNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run5Guest3run0s0_0EEB1K_
                local.get 0
                call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtCs22k8fyVPmoz_12futures_util6future10maybe_done9MaybeDoneNCNCNvXCsgR5kJmH8IIE_5helloNtB1K_5HelloNtNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run5Guest3run0s_0EEB1K_
                local.get 0
                i32.const 1
                i32.store8 offset=236
                local.get 0
                call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueNCNvXCsgR5kJmH8IIE_5helloNtBG_5HelloNtNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run5Guest3run0EBG_
                local.get 11
                i32.const 255
                i32.ne
                call $_RNvNCNvNtNtNtNtNtCs8o6ThntBNTu_6wasip37command7exports4wasi3cli3run16__export_run_cabi011wit_import2
                i32.const 0
                local.set 5
                br 3 (;@2;)
              end
              local.get 17
              local.get 15
              i32.store8
            end
            local.get 5
            i32.const 3
            i32.store8 offset=152
          end
          i32.const 3
          local.set 15
          local.get 3
          i32.const 3
          i32.store8
          i32.const 1
          local.set 5
        end
        local.get 0
        local.get 15
        i32.store8 offset=240
        local.get 2
        i32.const 128
        i32.add
        global.set $__stack_pointer
        local.get 5
        return
      end
      call $_RNvNtCshQUFA83YM6w_4core6option13unwrap_failed
      unreachable
    )
    (func $_RNvMs1_NtCscNOpLhlpk4u_11wit_bindgen2rtNtB5_7Cleanup3new (;48;) (type 10) (param i32 i32 i32)
      (local i32)
      block ;; label = @1
        local.get 2
        br_if 0 (;@1;)
        local.get 0
        i64.const 0
        i64.store align=4
        return
      end
      block ;; label = @1
        block ;; label = @2
          local.get 1
          i32.const 9
          i32.lt_u
          br_if 0 (;@2;)
          local.get 1
          local.get 2
          call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE8memalignCskAuRjb5C0Ki_4p3rt
          local.set 3
          br 1 (;@1;)
        end
        local.get 2
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCskAuRjb5C0Ki_4p3rt
        local.set 3
      end
      block ;; label = @1
        local.get 3
        i32.eqz
        br_if 0 (;@1;)
        local.get 0
        local.get 3
        i32.store offset=12
        local.get 0
        local.get 2
        i32.store offset=8
        local.get 0
        local.get 1
        i32.store offset=4
        local.get 0
        local.get 3
        i32.store
        return
      end
      call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
      unreachable
    )
    (func $_RNvXs3_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support14stream_supportINtB5_14RawStreamWriteRINtB5_12StreamVtablehEENtNtNtCshQUFA83YM6w_4core6future6future6Future4pollCsgR5kJmH8IIE_5hello (;49;) (type 10) (param i32 i32 i32)
      (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
      global.get $__stack_pointer
      i32.const 48
      i32.sub
      local.tee 3
      global.set $__stack_pointer
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                local.get 1
                i32.load offset=16
                br_table 1 (;@4;) 2 (;@3;) 0 (;@5;) 1 (;@4;)
              end
              call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
              unreachable
            end
            local.get 3
            i32.const 12
            i32.add
            local.get 1
            i32.const 16
            i32.add
            local.tee 4
            i32.const 36
            memory.copy
            local.get 1
            i32.const 2
            i32.store offset=16
            local.get 3
            i32.load offset=12
            i32.eqz
            br_if 1 (;@2;)
            local.get 3
            i32.const 12
            i32.add
            call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitable22WaitableOperationStateINtNtBG_14stream_support13StreamWriteOpRINtB23_12StreamVtablehEEEECsgR5kJmH8IIE_5hello
            i32.const 40
            call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
            unreachable
          end
          local.get 1
          i32.load
          local.set 5
          local.get 1
          i32.const 0
          i32.store
          local.get 1
          i32.load offset=4
          local.set 6
          br 1 (;@1;)
        end
        local.get 3
        i32.load offset=44
        local.set 7
        local.get 3
        i32.load offset=40
        local.set 8
        local.get 3
        i32.load offset=36
        local.set 9
        local.get 3
        i32.load offset=32
        local.set 10
        local.get 3
        i32.load offset=28
        local.set 11
        local.get 3
        i32.load offset=24
        local.set 12
        local.get 3
        i32.load offset=20
        local.set 13
        local.get 3
        i32.load offset=16
        local.set 14
        i32.const 1
        local.set 5
        i32.const 1
        local.set 6
        block ;; label = @2
          local.get 1
          i32.load offset=68
          local.tee 15
          i32.load8_u offset=8
          br_if 0 (;@2;)
          block ;; label = @3
            block ;; label = @4
              local.get 8
              i32.load offset=44
              i32.eqz
              br_if 0 (;@4;)
              local.get 9
              i32.const 0
              local.get 11
              select
              local.get 8
              i32.load offset=4
              local.get 7
              i32.mul
              i32.add
              local.set 6
              br 1 (;@3;)
            end
            local.get 13
            local.get 7
            i32.add
            local.set 6
          end
          local.get 15
          i32.load offset=4
          local.get 6
          local.get 12
          local.get 7
          i32.sub
          local.tee 16
          i32.const 268435455
          local.get 16
          i32.const 268435455
          i32.lt_u
          select
          local.get 15
          i32.load
          i32.load offset=8
          call_indirect (type 5)
          local.set 6
          local.get 4
          i32.load
          i32.const 1
          i32.gt_u
          br_if 0 (;@2;)
          local.get 1
          i32.const 20
          i32.add
          call $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support10abi_buffer9AbiBufferRINtNtBG_14stream_support12StreamVtablehEEECsgR5kJmH8IIE_5hello
        end
        local.get 1
        local.get 7
        i32.store offset=48
        local.get 1
        local.get 8
        i32.store offset=44
        local.get 1
        local.get 9
        i32.store offset=40
        local.get 1
        local.get 10
        i32.store offset=36
        local.get 1
        local.get 11
        i32.store offset=32
        local.get 1
        local.get 12
        i32.store offset=28
        local.get 1
        local.get 13
        i32.store offset=24
        local.get 1
        local.get 14
        i32.store offset=20
        local.get 1
        i32.const 1
        i32.store offset=16
      end
      local.get 0
      local.get 1
      local.get 2
      local.get 5
      local.get 6
      call $_RNvMs2_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitableINtB5_17WaitableOperationINtNtB7_14stream_support13StreamWriteOpRINtB1v_12StreamVtablehEEE23poll_complete_with_codeCsgR5kJmH8IIE_5hello
      local.get 3
      i32.const 48
      i32.add
      global.set $__stack_pointer
    )
    (func $_RNvNtCsiqQVI2xHy0t_5alloc7raw_vec12handle_error (;50;) (type 3) (param i32 i32)
      block ;; label = @1
        local.get 0
        i32.eqz
        br_if 0 (;@1;)
        call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
        unreachable
      end
      call $_RNvNtCshQUFA83YM6w_4core6result13unwrap_failed
      unreachable
    )
    (func $_RNvNtCshQUFA83YM6w_4core6result13unwrap_failed (;51;) (type 7)
      call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
      unreachable
    )
    (func $_RNvNtNtCshQUFA83YM6w_4core5slice5index16slice_index_fail (;52;) (type 10) (param i32 i32 i32)
      call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
      unreachable
    )
    (func $_RNvMs4_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB5_10ReturnCode6decode (;53;) (type 3) (param i32 i32)
      (local i32 i32)
      block ;; label = @1
        block ;; label = @2
          local.get 1
          i32.const -1
          i32.ne
          br_if 0 (;@2;)
          i32.const 0
          local.set 2
          br 1 (;@1;)
        end
        local.get 1
        i32.const 4
        i32.shr_u
        local.set 3
        i32.const 1
        local.set 2
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              local.get 1
              i32.const 15
              i32.and
              br_table 3 (;@1;) 1 (;@3;) 0 (;@4;) 2 (;@2;)
            end
            i32.const 3
            local.set 2
            br 2 (;@1;)
          end
          i32.const 2
          local.set 2
          br 1 (;@1;)
        end
        call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
        unreachable
      end
      local.get 0
      local.get 3
      i32.store offset=4
      local.get 0
      local.get 2
      i32.store
    )
    (func $_RNvNvMs2_NtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support8waitableINtB7_17WaitableOperationpE14register_waker9cabi_wake (;54;) (type 3) (param i32 i32)
      local.get 0
      local.get 1
      i32.store offset=4
      local.get 0
      i32.const 1
      i32.store
      local.get 0
      i32.load offset=8
      local.set 1
      local.get 0
      i32.const 0
      i32.store offset=8
      block ;; label = @1
        local.get 1
        br_if 0 (;@1;)
        call $_RNvNtCshQUFA83YM6w_4core6option13unwrap_failed
        unreachable
      end
      local.get 0
      i32.load offset=12
      local.get 1
      i32.load offset=4
      call_indirect (type 1)
    )
    (func $_RNvNtCshQUFA83YM6w_4core9panicking19assert_failed_inner (;55;) (type 7)
      call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
      unreachable
    )
    (func $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE8memalignCskAuRjb5C0Ki_4p3rt (;56;) (type 0) (param i32 i32) (result i32)
      (local i32 i32 i32 i32 i32)
      i32.const 0
      local.set 2
      block ;; label = @1
        local.get 1
        i32.const -48
        global.get $__memory_base
        i32.const 1048612
        i32.add
        i32.load offset=452
        i32.sub
        i32.const -9
        i32.and
        i32.const -3
        i32.add
        local.tee 3
        i32.const -64
        local.get 3
        i32.const -64
        i32.lt_u
        select
        local.get 0
        i32.const 16
        local.get 0
        i32.const 16
        i32.gt_u
        select
        local.tee 0
        i32.sub
        i32.ge_u
        br_if 0 (;@1;)
        local.get 0
        i32.const 16
        local.get 1
        i32.const 11
        i32.add
        i32.const -8
        i32.and
        local.get 1
        i32.const 11
        i32.lt_u
        select
        local.tee 3
        i32.add
        i32.const 12
        i32.add
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCskAuRjb5C0Ki_4p3rt
        local.tee 1
        i32.eqz
        br_if 0 (;@1;)
        local.get 1
        i32.const -8
        i32.add
        local.set 2
        block ;; label = @2
          block ;; label = @3
            local.get 0
            i32.const -1
            i32.add
            local.tee 4
            local.get 1
            i32.and
            br_if 0 (;@3;)
            local.get 2
            local.set 0
            br 1 (;@2;)
          end
          local.get 1
          i32.const -4
          i32.add
          local.tee 5
          i32.load
          local.tee 6
          i32.const -8
          i32.and
          local.get 4
          local.get 1
          i32.add
          i32.const 0
          local.get 0
          i32.sub
          i32.and
          i32.const -8
          i32.add
          local.tee 1
          i32.const 0
          local.get 0
          local.get 1
          local.get 2
          i32.sub
          i32.const 16
          i32.gt_u
          select
          i32.add
          local.tee 0
          local.get 2
          i32.sub
          local.tee 1
          i32.sub
          local.set 4
          block ;; label = @3
            local.get 6
            i32.const 3
            i32.and
            i32.eqz
            br_if 0 (;@3;)
            local.get 0
            local.get 4
            local.get 0
            i32.load offset=4
            i32.const 1
            i32.and
            i32.or
            i32.const 2
            i32.or
            i32.store offset=4
            local.get 0
            local.get 4
            i32.add
            local.tee 4
            local.get 4
            i32.load offset=4
            i32.const 1
            i32.or
            i32.store offset=4
            local.get 5
            local.get 1
            local.get 5
            i32.load
            i32.const 1
            i32.and
            i32.or
            i32.const 2
            i32.or
            i32.store
            local.get 2
            local.get 1
            i32.add
            local.tee 4
            local.get 4
            i32.load offset=4
            i32.const 1
            i32.or
            i32.store offset=4
            local.get 2
            local.get 1
            call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13dispose_chunkCskAuRjb5C0Ki_4p3rt
            br 1 (;@2;)
          end
          local.get 2
          i32.load
          local.set 2
          local.get 0
          local.get 4
          i32.store offset=4
          local.get 0
          local.get 2
          local.get 1
          i32.add
          i32.store
        end
        block ;; label = @2
          local.get 0
          i32.load offset=4
          local.tee 1
          i32.const 3
          i32.and
          i32.eqz
          br_if 0 (;@2;)
          local.get 1
          i32.const -8
          i32.and
          local.tee 2
          local.get 3
          i32.const 16
          i32.add
          i32.le_u
          br_if 0 (;@2;)
          local.get 0
          local.get 3
          local.get 1
          i32.const 1
          i32.and
          i32.or
          i32.const 2
          i32.or
          i32.store offset=4
          local.get 0
          local.get 3
          i32.add
          local.tee 1
          local.get 2
          local.get 3
          i32.sub
          local.tee 3
          i32.const 3
          i32.or
          i32.store offset=4
          local.get 0
          local.get 2
          i32.add
          local.tee 2
          local.get 2
          i32.load offset=4
          i32.const 1
          i32.or
          i32.store offset=4
          local.get 1
          local.get 3
          call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13dispose_chunkCskAuRjb5C0Ki_4p3rt
        end
        local.get 0
        i32.const 8
        i32.add
        local.set 2
      end
      local.get 2
    )
    (func $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13dispose_chunkCskAuRjb5C0Ki_4p3rt (;57;) (type 3) (param i32 i32)
      (local i32 i32)
      local.get 0
      local.get 1
      i32.add
      local.set 2
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            local.get 0
            i32.load offset=4
            local.tee 3
            i32.const 1
            i32.and
            br_if 0 (;@3;)
            local.get 3
            i32.const 2
            i32.and
            i32.eqz
            br_if 1 (;@2;)
            local.get 0
            i32.load
            local.tee 3
            local.get 1
            i32.add
            local.set 1
            block ;; label = @4
              local.get 0
              local.get 3
              i32.sub
              local.tee 0
              global.get $__memory_base
              i32.const 1048612
              i32.add
              i32.load offset=424
              i32.ne
              br_if 0 (;@4;)
              local.get 2
              i32.load offset=4
              i32.const 3
              i32.and
              i32.const 3
              i32.ne
              br_if 1 (;@3;)
              global.get $__memory_base
              i32.const 1048612
              i32.add
              local.get 1
              i32.store offset=416
              local.get 2
              local.get 2
              i32.load offset=4
              i32.const -2
              i32.and
              i32.store offset=4
              local.get 0
              local.get 1
              i32.const 1
              i32.or
              i32.store offset=4
              local.get 2
              local.get 1
              i32.store
              return
            end
            local.get 0
            local.get 3
            call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCskAuRjb5C0Ki_4p3rt
          end
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                local.get 2
                i32.load offset=4
                local.tee 3
                i32.const 2
                i32.and
                br_if 0 (;@5;)
                local.get 2
                global.get $__memory_base
                i32.const 1048612
                i32.add
                i32.load offset=428
                i32.eq
                br_if 2 (;@3;)
                local.get 2
                global.get $__memory_base
                i32.const 1048612
                i32.add
                i32.load offset=424
                i32.eq
                br_if 4 (;@1;)
                local.get 2
                local.get 3
                i32.const -8
                i32.and
                local.tee 3
                call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCskAuRjb5C0Ki_4p3rt
                local.get 0
                local.get 3
                local.get 1
                i32.add
                local.tee 1
                i32.const 1
                i32.or
                i32.store offset=4
                local.get 0
                local.get 1
                i32.add
                local.get 1
                i32.store
                local.get 0
                global.get $__memory_base
                i32.const 1048612
                i32.add
                i32.load offset=424
                i32.ne
                br_if 1 (;@4;)
                global.get $__memory_base
                i32.const 1048612
                i32.add
                local.get 1
                i32.store offset=416
                return
              end
              local.get 2
              local.get 3
              i32.const -2
              i32.and
              i32.store offset=4
              local.get 0
              local.get 1
              i32.const 1
              i32.or
              i32.store offset=4
              local.get 0
              local.get 1
              i32.add
              local.get 1
              i32.store
            end
            local.get 0
            local.get 1
            call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12insert_chunkCskAuRjb5C0Ki_4p3rt
            return
          end
          global.get $__memory_base
          i32.const 1048612
          i32.add
          local.tee 2
          local.get 0
          i32.store offset=428
          local.get 2
          local.get 2
          i32.load offset=420
          local.get 1
          i32.add
          local.tee 1
          i32.store offset=420
          local.get 0
          local.get 1
          i32.const 1
          i32.or
          i32.store offset=4
          local.get 0
          local.get 2
          i32.load offset=424
          i32.ne
          br_if 0 (;@2;)
          global.get $__memory_base
          i32.const 1048612
          i32.add
          local.tee 0
          i32.const 0
          i32.store offset=416
          local.get 0
          i32.const 0
          i32.store offset=424
        end
        return
      end
      global.get $__memory_base
      i32.const 1048612
      i32.add
      local.tee 2
      local.get 0
      i32.store offset=424
      local.get 2
      local.get 2
      i32.load offset=416
      local.get 1
      i32.add
      local.tee 1
      i32.store offset=416
      local.get 0
      local.get 1
      i32.const 1
      i32.or
      i32.store offset=4
      local.get 0
      local.get 1
      i32.add
      local.get 1
      i32.store
    )
    (func $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE10replace_dvCskAuRjb5C0Ki_4p3rt (;58;) (type 3) (param i32 i32)
      (local i32 i32 i32 i32 i32)
      block ;; label = @1
        global.get $__memory_base
        i32.const 1048612
        i32.add
        i32.load offset=416
        local.tee 2
        i32.eqz
        br_if 0 (;@1;)
        global.get $__memory_base
        i32.const 1048612
        i32.add
        local.tee 3
        i32.load offset=424
        local.set 4
        block ;; label = @2
          block ;; label = @3
            local.get 3
            i32.load offset=408
            local.tee 3
            i32.const 1
            local.get 2
            i32.const 3
            i32.shr_u
            i32.shl
            local.tee 5
            i32.and
            br_if 0 (;@3;)
            global.get $__memory_base
            i32.const 1048612
            i32.add
            local.tee 6
            local.get 3
            local.get 5
            i32.or
            i32.store offset=408
            local.get 6
            local.get 2
            i32.const -8
            i32.and
            i32.add
            i32.const 144
            i32.add
            local.tee 2
            local.set 3
            br 1 (;@2;)
          end
          global.get $__memory_base
          i32.const 1048612
          i32.add
          local.get 2
          i32.const -8
          i32.and
          i32.add
          local.tee 2
          i32.const 144
          i32.add
          local.set 3
          local.get 2
          i32.const 152
          i32.add
          i32.load
          local.set 2
        end
        local.get 3
        local.get 4
        i32.store offset=8
        local.get 2
        local.get 4
        i32.store offset=12
        local.get 4
        local.get 3
        i32.store offset=12
        local.get 4
        local.get 2
        i32.store offset=8
      end
      global.get $__memory_base
      i32.const 1048612
      i32.add
      local.tee 4
      local.get 0
      i32.store offset=424
      local.get 4
      local.get 1
      i32.store offset=416
    )
    (func $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE18unlink_large_chunkCskAuRjb5C0Ki_4p3rt (;59;) (type 1) (param i32)
      (local i32 i32 i32 i32 i32)
      local.get 0
      i32.load offset=24
      local.set 1
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            local.get 0
            i32.const 12
            i32.add
            i32.load
            local.tee 2
            local.get 0
            i32.ne
            br_if 0 (;@3;)
            local.get 0
            i32.const 20
            i32.const 16
            local.get 0
            i32.load offset=20
            local.tee 2
            select
            i32.add
            i32.load
            local.tee 3
            br_if 1 (;@2;)
            i32.const 0
            local.set 2
            br 2 (;@1;)
          end
          local.get 0
          i32.const 8
          i32.add
          i32.load
          local.tee 3
          local.get 2
          i32.store offset=12
          local.get 2
          local.get 3
          i32.store offset=8
          br 1 (;@1;)
        end
        local.get 0
        i32.const 20
        i32.add
        local.get 0
        i32.const 16
        i32.add
        local.get 2
        select
        local.set 4
        loop ;; label = @2
          local.get 4
          local.set 5
          local.get 3
          local.tee 2
          i32.const 20
          i32.add
          local.set 4
          local.get 2
          i32.load offset=20
          local.tee 3
          br_if 0 (;@2;)
          local.get 2
          i32.const 16
          i32.add
          local.set 4
          local.get 2
          i32.load offset=16
          local.tee 3
          br_if 0 (;@2;)
        end
        local.get 5
        i32.const 0
        i32.store
      end
      block ;; label = @1
        block ;; label = @2
          local.get 1
          i32.eqz
          br_if 0 (;@2;)
          block ;; label = @3
            block ;; label = @4
              local.get 0
              global.get $__memory_base
              i32.const 1048612
              i32.add
              local.get 0
              i32.load offset=28
              local.tee 4
              i32.const 2
              i32.shl
              i32.add
              local.tee 3
              i32.load
              i32.eq
              br_if 0 (;@4;)
              block ;; label = @5
                block ;; label = @6
                  local.get 1
                  i32.load offset=16
                  local.get 0
                  i32.eq
                  br_if 0 (;@6;)
                  local.get 1
                  local.get 2
                  i32.store offset=20
                  br 1 (;@5;)
                end
                local.get 1
                local.get 2
                i32.store offset=16
              end
              local.get 2
              br_if 1 (;@3;)
              br 2 (;@2;)
            end
            local.get 3
            local.get 2
            i32.store
            local.get 2
            i32.eqz
            br_if 2 (;@1;)
          end
          local.get 2
          local.get 1
          i32.store offset=24
          block ;; label = @3
            local.get 0
            i32.load offset=16
            local.tee 3
            i32.eqz
            br_if 0 (;@3;)
            local.get 2
            local.get 3
            i32.store offset=16
            local.get 3
            local.get 2
            i32.store offset=24
          end
          local.get 0
          i32.load offset=20
          local.tee 3
          i32.eqz
          br_if 0 (;@2;)
          local.get 2
          local.get 3
          i32.store offset=20
          local.get 3
          local.get 2
          i32.store offset=24
        end
        return
      end
      global.get $__memory_base
      i32.const 1048612
      i32.add
      local.tee 2
      local.get 2
      i32.load offset=412
      i32.const -2
      local.get 4
      i32.rotl
      i32.and
      i32.store offset=412
    )
    (func $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12insert_chunkCskAuRjb5C0Ki_4p3rt (;60;) (type 3) (param i32 i32)
      (local i32 i32 i32)
      block ;; label = @1
        local.get 1
        i32.const 256
        i32.lt_u
        br_if 0 (;@1;)
        local.get 0
        local.get 1
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE18insert_large_chunkCskAuRjb5C0Ki_4p3rt
        return
      end
      block ;; label = @1
        block ;; label = @2
          global.get $__memory_base
          i32.const 1048612
          i32.add
          i32.load offset=408
          local.tee 2
          i32.const 1
          local.get 1
          i32.const 3
          i32.shr_u
          i32.shl
          local.tee 3
          i32.and
          br_if 0 (;@2;)
          global.get $__memory_base
          i32.const 1048612
          i32.add
          local.tee 4
          local.get 2
          local.get 3
          i32.or
          i32.store offset=408
          local.get 4
          local.get 1
          i32.const 248
          i32.and
          i32.add
          i32.const 144
          i32.add
          local.tee 1
          local.set 2
          br 1 (;@1;)
        end
        global.get $__memory_base
        i32.const 1048612
        i32.add
        local.get 1
        i32.const 248
        i32.and
        i32.add
        local.tee 1
        i32.const 144
        i32.add
        local.set 2
        local.get 1
        i32.const 152
        i32.add
        i32.load
        local.set 1
      end
      local.get 2
      local.get 0
      i32.store offset=8
      local.get 1
      local.get 0
      i32.store offset=12
      local.get 0
      local.get 2
      i32.store offset=12
      local.get 0
      local.get 1
      i32.store offset=8
    )
    (func $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCskAuRjb5C0Ki_4p3rt (;61;) (type 3) (param i32 i32)
      (local i32)
      block ;; label = @1
        local.get 1
        i32.const 256
        i32.lt_u
        br_if 0 (;@1;)
        local.get 0
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE18unlink_large_chunkCskAuRjb5C0Ki_4p3rt
        return
      end
      block ;; label = @1
        local.get 0
        i32.load offset=12
        local.tee 2
        local.get 0
        i32.load offset=8
        local.tee 0
        i32.eq
        br_if 0 (;@1;)
        local.get 0
        local.get 2
        i32.store offset=12
        local.get 2
        local.get 0
        i32.store offset=8
        return
      end
      global.get $__memory_base
      i32.const 1048612
      i32.add
      local.tee 0
      local.get 0
      i32.load offset=408
      i32.const -2
      local.get 1
      i32.const 3
      i32.shr_u
      i32.rotl
      i32.and
      i32.store offset=408
    )
    (func $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE18insert_large_chunkCskAuRjb5C0Ki_4p3rt (;62;) (type 3) (param i32 i32)
      (local i32 i32 i32 i32)
      i32.const 31
      local.set 2
      block ;; label = @1
        local.get 1
        i32.const 16777215
        i32.gt_u
        br_if 0 (;@1;)
        local.get 1
        i32.const 38
        local.get 1
        i32.const 8
        i32.shr_u
        i32.clz
        local.tee 2
        i32.sub
        i32.shr_u
        i32.const 1
        i32.and
        local.get 2
        i32.const 1
        i32.shl
        i32.or
        i32.const 62
        i32.xor
        local.set 2
      end
      local.get 0
      i64.const 0
      i64.store offset=16 align=4
      local.get 0
      local.get 2
      i32.store offset=28
      global.get $__memory_base
      i32.const 1048612
      i32.add
      local.tee 3
      local.get 2
      i32.const 2
      i32.shl
      i32.add
      local.set 4
      block ;; label = @1
        local.get 3
        i32.load offset=412
        i32.const 1
        local.get 2
        i32.shl
        local.tee 3
        i32.and
        br_if 0 (;@1;)
        local.get 4
        local.get 0
        i32.store
        local.get 0
        local.get 4
        i32.store offset=24
        local.get 0
        local.get 0
        i32.store offset=12
        local.get 0
        local.get 0
        i32.store offset=8
        global.get $__memory_base
        i32.const 1048612
        i32.add
        local.tee 2
        local.get 2
        i32.load offset=412
        local.get 3
        i32.or
        i32.store offset=412
        return
      end
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            local.get 4
            i32.load
            local.tee 3
            i32.load offset=4
            i32.const -8
            i32.and
            local.get 1
            i32.ne
            br_if 0 (;@3;)
            local.get 3
            local.set 2
            br 1 (;@2;)
          end
          local.get 1
          i32.const 0
          i32.const 25
          local.get 2
          i32.const 1
          i32.shr_u
          i32.sub
          local.get 2
          i32.const 31
          i32.eq
          select
          i32.shl
          local.set 4
          loop ;; label = @3
            local.get 3
            local.get 4
            i32.const 29
            i32.shr_u
            i32.const 4
            i32.and
            i32.add
            local.tee 5
            i32.load offset=16
            local.tee 2
            i32.eqz
            br_if 2 (;@1;)
            local.get 4
            i32.const 1
            i32.shl
            local.set 4
            local.get 2
            local.set 3
            local.get 2
            i32.load offset=4
            i32.const -8
            i32.and
            local.get 1
            i32.ne
            br_if 0 (;@3;)
          end
        end
        local.get 2
        i32.load offset=8
        local.tee 4
        local.get 0
        i32.store offset=12
        local.get 2
        local.get 0
        i32.store offset=8
        local.get 0
        i32.const 0
        i32.store offset=24
        local.get 0
        local.get 2
        i32.store offset=12
        local.get 0
        local.get 4
        i32.store offset=8
        return
      end
      local.get 5
      i32.const 16
      i32.add
      local.get 0
      i32.store
      local.get 0
      local.get 3
      i32.store offset=24
      local.get 0
      local.get 0
      i32.store offset=12
      local.get 0
      local.get 0
      i32.store offset=8
    )
    (func $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt (;63;) (type 3) (param i32 i32)
      (local i32)
      block ;; label = @1
        block ;; label = @2
          local.get 0
          i32.const -8
          i32.and
          local.tee 2
          i32.const 4
          i32.const 8
          local.get 0
          i32.const 3
          i32.and
          local.tee 0
          select
          local.get 1
          i32.add
          i32.lt_u
          br_if 0 (;@2;)
          local.get 0
          i32.eqz
          br_if 1 (;@1;)
          local.get 2
          local.get 1
          i32.const 39
          i32.add
          i32.le_u
          br_if 1 (;@1;)
          i32.const 46
          call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
          unreachable
        end
        i32.const 46
        call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
        unreachable
      end
    )
    (func $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt (;64;) (type 1) (param i32)
      (local i32 i32 i32 i32)
      local.get 0
      i32.const -8
      i32.add
      local.tee 1
      local.get 0
      i32.const -4
      i32.add
      i32.load
      local.tee 2
      i32.const -8
      i32.and
      local.tee 0
      i32.add
      local.set 3
      block ;; label = @1
        block ;; label = @2
          local.get 2
          i32.const 1
          i32.and
          br_if 0 (;@2;)
          local.get 2
          i32.const 2
          i32.and
          i32.eqz
          br_if 1 (;@1;)
          local.get 1
          i32.load
          local.tee 2
          local.get 0
          i32.add
          local.set 0
          block ;; label = @3
            local.get 1
            local.get 2
            i32.sub
            local.tee 1
            global.get $__memory_base
            i32.const 1048612
            i32.add
            i32.load offset=424
            i32.ne
            br_if 0 (;@3;)
            local.get 3
            i32.load offset=4
            i32.const 3
            i32.and
            i32.const 3
            i32.ne
            br_if 1 (;@2;)
            global.get $__memory_base
            i32.const 1048612
            i32.add
            local.get 0
            i32.store offset=416
            local.get 3
            local.get 3
            i32.load offset=4
            i32.const -2
            i32.and
            i32.store offset=4
            local.get 1
            local.get 0
            i32.const 1
            i32.or
            i32.store offset=4
            local.get 3
            local.get 0
            i32.store
            br 2 (;@1;)
          end
          local.get 1
          local.get 2
          call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCskAuRjb5C0Ki_4p3rt
        end
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  block ;; label = @7
                    block ;; label = @8
                      block ;; label = @9
                        local.get 3
                        i32.load offset=4
                        local.tee 2
                        i32.const 2
                        i32.and
                        br_if 0 (;@9;)
                        local.get 3
                        global.get $__memory_base
                        i32.const 1048612
                        i32.add
                        i32.load offset=428
                        i32.eq
                        br_if 2 (;@7;)
                        local.get 3
                        global.get $__memory_base
                        i32.const 1048612
                        i32.add
                        i32.load offset=424
                        i32.eq
                        br_if 6 (;@3;)
                        local.get 3
                        local.get 2
                        i32.const -8
                        i32.and
                        local.tee 2
                        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCskAuRjb5C0Ki_4p3rt
                        local.get 1
                        local.get 2
                        local.get 0
                        i32.add
                        local.tee 0
                        i32.const 1
                        i32.or
                        i32.store offset=4
                        local.get 1
                        local.get 0
                        i32.add
                        local.get 0
                        i32.store
                        local.get 1
                        global.get $__memory_base
                        i32.const 1048612
                        i32.add
                        i32.load offset=424
                        i32.ne
                        br_if 1 (;@8;)
                        global.get $__memory_base
                        i32.const 1048612
                        i32.add
                        local.get 0
                        i32.store offset=416
                        return
                      end
                      local.get 3
                      local.get 2
                      i32.const -2
                      i32.and
                      i32.store offset=4
                      local.get 1
                      local.get 0
                      i32.const 1
                      i32.or
                      i32.store offset=4
                      local.get 1
                      local.get 0
                      i32.add
                      local.get 0
                      i32.store
                    end
                    local.get 0
                    i32.const 256
                    i32.lt_u
                    br_if 1 (;@6;)
                    local.get 1
                    local.get 0
                    call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE18insert_large_chunkCskAuRjb5C0Ki_4p3rt
                    global.get $__memory_base
                    i32.const 1048612
                    i32.add
                    local.tee 1
                    local.get 1
                    i32.load offset=448
                    i32.const -1
                    i32.add
                    local.tee 1
                    i32.store offset=448
                    local.get 1
                    br_if 6 (;@1;)
                    global.get $__memory_base
                    i32.const 1048612
                    i32.add
                    i32.load offset=136
                    local.tee 0
                    br_if 2 (;@5;)
                    i32.const 0
                    local.set 1
                    br 3 (;@4;)
                  end
                  global.get $__memory_base
                  i32.const 1048612
                  i32.add
                  local.tee 3
                  local.get 1
                  i32.store offset=428
                  local.get 3
                  local.get 3
                  i32.load offset=420
                  local.get 0
                  i32.add
                  local.tee 0
                  i32.store offset=420
                  local.get 1
                  local.get 0
                  i32.const 1
                  i32.or
                  i32.store offset=4
                  block ;; label = @7
                    local.get 1
                    local.get 3
                    i32.load offset=424
                    i32.ne
                    br_if 0 (;@7;)
                    global.get $__memory_base
                    i32.const 1048612
                    i32.add
                    local.tee 1
                    i32.const 0
                    i32.store offset=416
                    local.get 1
                    i32.const 0
                    i32.store offset=424
                  end
                  local.get 0
                  global.get $__memory_base
                  i32.const 1048612
                  i32.add
                  i32.load offset=440
                  local.tee 2
                  i32.le_u
                  br_if 5 (;@1;)
                  i32.const -48
                  global.get $__memory_base
                  i32.const 1048612
                  i32.add
                  i32.load offset=452
                  local.tee 1
                  i32.sub
                  i32.const -9
                  i32.and
                  i32.const 3
                  i32.eq
                  br_if 5 (;@1;)
                  global.get $__memory_base
                  i32.const 1048612
                  i32.add
                  i32.load offset=428
                  local.tee 0
                  i32.eqz
                  br_if 5 (;@1;)
                  global.get $__memory_base
                  i32.const 1048612
                  i32.add
                  i32.load offset=420
                  local.tee 4
                  i32.const 41
                  i32.lt_u
                  br_if 4 (;@2;)
                  block ;; label = @7
                    local.get 1
                    i32.eqz
                    br_if 0 (;@7;)
                    global.get $__memory_base
                    i32.const 1048612
                    i32.add
                    i32.const 128
                    i32.add
                    local.set 1
                    loop ;; label = @8
                      block ;; label = @9
                        local.get 1
                        i32.load
                        local.tee 3
                        local.get 0
                        i32.gt_u
                        br_if 0 (;@9;)
                        local.get 0
                        local.get 3
                        local.get 1
                        i32.const 4
                        i32.add
                        i32.load
                        i32.add
                        i32.lt_u
                        br_if 7 (;@2;)
                      end
                      local.get 1
                      i32.load offset=8
                      local.tee 1
                      br_if 0 (;@8;)
                      br 6 (;@2;)
                    end
                  end
                  call $_RNvNtCshQUFA83YM6w_4core6result13unwrap_failed
                  unreachable
                end
                block ;; label = @6
                  block ;; label = @7
                    global.get $__memory_base
                    i32.const 1048612
                    i32.add
                    i32.load offset=408
                    local.tee 3
                    i32.const 1
                    local.get 0
                    i32.const 3
                    i32.shr_u
                    i32.shl
                    local.tee 2
                    i32.and
                    br_if 0 (;@7;)
                    global.get $__memory_base
                    i32.const 1048612
                    i32.add
                    local.tee 4
                    local.get 3
                    local.get 2
                    i32.or
                    i32.store offset=408
                    local.get 4
                    local.get 0
                    i32.const 248
                    i32.and
                    i32.add
                    i32.const 144
                    i32.add
                    local.tee 0
                    local.set 3
                    br 1 (;@6;)
                  end
                  global.get $__memory_base
                  i32.const 1048612
                  i32.add
                  local.get 0
                  i32.const 248
                  i32.and
                  i32.add
                  local.tee 0
                  i32.const 144
                  i32.add
                  local.set 3
                  local.get 0
                  i32.const 152
                  i32.add
                  i32.load
                  local.set 0
                end
                local.get 3
                local.get 1
                i32.store offset=8
                local.get 0
                local.get 1
                i32.store offset=12
                local.get 1
                local.get 3
                i32.store offset=12
                local.get 1
                local.get 0
                i32.store offset=8
                return
              end
              i32.const 0
              local.set 1
              loop ;; label = @5
                local.get 1
                i32.const 1
                i32.add
                local.set 1
                local.get 0
                i32.load offset=8
                local.tee 0
                br_if 0 (;@5;)
              end
            end
            global.get $__memory_base
            i32.const 1048612
            i32.add
            local.tee 0
            local.get 0
            i32.load offset=456
            local.tee 0
            local.get 1
            local.get 0
            local.get 1
            i32.gt_u
            select
            i32.const -1
            local.get 0
            select
            i32.store offset=448
            return
          end
          global.get $__memory_base
          i32.const 1048612
          i32.add
          local.tee 3
          local.get 1
          i32.store offset=424
          local.get 3
          local.get 3
          i32.load offset=416
          local.get 0
          i32.add
          local.tee 0
          i32.store offset=416
          local.get 1
          local.get 0
          i32.const 1
          i32.or
          i32.store offset=4
          local.get 1
          local.get 0
          i32.add
          local.get 0
          i32.store
          return
        end
        block ;; label = @2
          block ;; label = @3
            global.get $__memory_base
            i32.const 1048612
            i32.add
            i32.load offset=136
            local.tee 0
            br_if 0 (;@3;)
            i32.const 0
            local.set 1
            br 1 (;@2;)
          end
          i32.const 0
          local.set 1
          loop ;; label = @3
            local.get 1
            i32.const 1
            i32.add
            local.set 1
            local.get 0
            i32.load offset=8
            local.tee 0
            br_if 0 (;@3;)
          end
        end
        global.get $__memory_base
        i32.const 1048612
        i32.add
        local.tee 0
        local.get 0
        i32.load offset=456
        local.tee 0
        local.get 1
        local.get 0
        local.get 1
        i32.gt_u
        select
        i32.const -1
        local.get 0
        select
        i32.store offset=448
        local.get 4
        local.get 2
        i32.le_u
        br_if 0 (;@1;)
        global.get $__memory_base
        i32.const 1048612
        i32.add
        i32.const -1
        i32.store offset=440
        return
      end
    )
    (func $cabi_realloc (;65;) (type 4) (param i32 i32 i32 i32) (result i32)
      (local i32 i32 i32 i32)
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  block ;; label = @7
                    block ;; label = @8
                      block ;; label = @9
                        local.get 1
                        br_if 0 (;@9;)
                        local.get 3
                        i32.eqz
                        br_if 7 (;@2;)
                        local.get 2
                        i32.const 9
                        i32.lt_u
                        br_if 1 (;@8;)
                        local.get 2
                        local.get 3
                        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE8memalignCskAuRjb5C0Ki_4p3rt
                        local.set 2
                        br 2 (;@7;)
                      end
                      local.get 0
                      i32.const -4
                      i32.add
                      local.tee 4
                      i32.load
                      local.tee 5
                      local.get 1
                      call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
                      block ;; label = @9
                        local.get 2
                        i32.const 9
                        i32.lt_u
                        br_if 0 (;@9;)
                        local.get 2
                        local.get 3
                        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE8memalignCskAuRjb5C0Ki_4p3rt
                        local.tee 2
                        i32.eqz
                        br_if 8 (;@1;)
                        block ;; label = @10
                          local.get 3
                          local.get 1
                          local.get 3
                          local.get 1
                          i32.lt_u
                          select
                          local.tee 3
                          i32.eqz
                          br_if 0 (;@10;)
                          local.get 2
                          local.get 0
                          local.get 3
                          memory.copy
                        end
                        local.get 4
                        i32.load
                        local.get 1
                        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
                        br 6 (;@3;)
                      end
                      local.get 3
                      i32.const -48
                      global.get $__memory_base
                      i32.const 1048612
                      i32.add
                      i32.load offset=452
                      local.tee 6
                      i32.sub
                      i32.const -9
                      i32.and
                      i32.const -3
                      i32.add
                      local.tee 2
                      i32.const -64
                      local.get 2
                      i32.const -64
                      i32.lt_u
                      select
                      i32.ge_u
                      br_if 7 (;@1;)
                      i32.const 16
                      local.get 3
                      i32.const 11
                      i32.add
                      i32.const -8
                      i32.and
                      local.get 3
                      i32.const 11
                      i32.lt_u
                      select
                      local.set 2
                      local.get 5
                      i32.const -8
                      i32.and
                      local.set 1
                      local.get 0
                      i32.const -8
                      i32.add
                      local.set 7
                      block ;; label = @9
                        block ;; label = @10
                          block ;; label = @11
                            block ;; label = @12
                              block ;; label = @13
                                local.get 5
                                i32.const 3
                                i32.and
                                i32.eqz
                                br_if 0 (;@13;)
                                local.get 7
                                local.get 1
                                i32.add
                                local.set 6
                                local.get 1
                                local.get 2
                                i32.ge_u
                                br_if 3 (;@10;)
                                local.get 6
                                global.get $__memory_base
                                i32.const 1048612
                                i32.add
                                i32.load offset=428
                                i32.eq
                                br_if 4 (;@9;)
                                local.get 6
                                global.get $__memory_base
                                i32.const 1048612
                                i32.add
                                i32.load offset=424
                                i32.eq
                                br_if 2 (;@11;)
                                local.get 6
                                i32.load offset=4
                                local.tee 5
                                i32.const 2
                                i32.and
                                br_if 9 (;@4;)
                                local.get 5
                                i32.const -8
                                i32.and
                                local.tee 5
                                local.get 1
                                i32.add
                                local.tee 1
                                local.get 2
                                i32.lt_u
                                br_if 9 (;@4;)
                                local.get 6
                                local.get 5
                                call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCskAuRjb5C0Ki_4p3rt
                                local.get 1
                                local.get 2
                                i32.sub
                                local.tee 5
                                i32.const 16
                                i32.lt_u
                                br_if 1 (;@12;)
                                local.get 4
                                local.get 2
                                local.get 4
                                i32.load
                                i32.const 1
                                i32.and
                                i32.or
                                i32.const 2
                                i32.or
                                i32.store
                                local.get 7
                                local.get 2
                                i32.add
                                local.tee 2
                                local.get 5
                                i32.const 3
                                i32.or
                                i32.store offset=4
                                local.get 7
                                local.get 1
                                i32.add
                                local.tee 1
                                local.get 1
                                i32.load offset=4
                                i32.const 1
                                i32.or
                                i32.store offset=4
                                local.get 2
                                local.get 5
                                call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13dispose_chunkCskAuRjb5C0Ki_4p3rt
                                br 8 (;@5;)
                              end
                              local.get 2
                              i32.const 256
                              i32.lt_u
                              br_if 8 (;@4;)
                              local.get 1
                              local.get 2
                              i32.le_u
                              br_if 8 (;@4;)
                              local.get 1
                              local.get 2
                              i32.sub
                              local.get 6
                              i32.const 1
                              i32.shl
                              i32.gt_u
                              br_if 8 (;@4;)
                              br 7 (;@5;)
                            end
                            local.get 4
                            local.get 1
                            local.get 4
                            i32.load
                            i32.const 1
                            i32.and
                            i32.or
                            i32.const 2
                            i32.or
                            i32.store
                            local.get 7
                            local.get 1
                            i32.add
                            local.tee 2
                            local.get 2
                            i32.load offset=4
                            i32.const 1
                            i32.or
                            i32.store offset=4
                            br 6 (;@5;)
                          end
                          global.get $__memory_base
                          i32.const 1048612
                          i32.add
                          i32.load offset=416
                          local.get 1
                          i32.add
                          local.tee 1
                          local.get 2
                          i32.lt_u
                          br_if 6 (;@4;)
                          block ;; label = @11
                            block ;; label = @12
                              local.get 1
                              local.get 2
                              i32.sub
                              local.tee 6
                              i32.const 15
                              i32.gt_u
                              br_if 0 (;@12;)
                              local.get 4
                              local.get 1
                              local.get 5
                              i32.const 1
                              i32.and
                              i32.or
                              i32.const 2
                              i32.or
                              i32.store
                              local.get 7
                              local.get 1
                              i32.add
                              local.tee 2
                              local.get 2
                              i32.load offset=4
                              i32.const 1
                              i32.or
                              i32.store offset=4
                              i32.const 0
                              local.set 6
                              i32.const 0
                              local.set 2
                              br 1 (;@11;)
                            end
                            local.get 4
                            local.get 2
                            local.get 5
                            i32.const 1
                            i32.and
                            i32.or
                            i32.const 2
                            i32.or
                            i32.store
                            local.get 7
                            local.get 2
                            i32.add
                            local.tee 2
                            local.get 6
                            i32.const 1
                            i32.or
                            i32.store offset=4
                            local.get 7
                            local.get 1
                            i32.add
                            local.tee 1
                            local.get 6
                            i32.store
                            local.get 1
                            local.get 1
                            i32.load offset=4
                            i32.const -2
                            i32.and
                            i32.store offset=4
                          end
                          global.get $__memory_base
                          i32.const 1048612
                          i32.add
                          local.tee 1
                          local.get 2
                          i32.store offset=424
                          local.get 1
                          local.get 6
                          i32.store offset=416
                          br 5 (;@5;)
                        end
                        local.get 1
                        local.get 2
                        i32.sub
                        local.tee 1
                        i32.const 16
                        i32.lt_u
                        br_if 4 (;@5;)
                        local.get 4
                        local.get 2
                        local.get 5
                        i32.const 1
                        i32.and
                        i32.or
                        i32.const 2
                        i32.or
                        i32.store
                        local.get 7
                        local.get 2
                        i32.add
                        local.tee 2
                        local.get 1
                        i32.const 3
                        i32.or
                        i32.store offset=4
                        local.get 6
                        local.get 6
                        i32.load offset=4
                        i32.const 1
                        i32.or
                        i32.store offset=4
                        local.get 2
                        local.get 1
                        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13dispose_chunkCskAuRjb5C0Ki_4p3rt
                        br 4 (;@5;)
                      end
                      global.get $__memory_base
                      i32.const 1048612
                      i32.add
                      i32.load offset=420
                      local.get 1
                      i32.add
                      local.tee 1
                      local.get 2
                      i32.gt_u
                      br_if 2 (;@6;)
                      br 4 (;@4;)
                    end
                    local.get 3
                    call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCskAuRjb5C0Ki_4p3rt
                    local.set 2
                  end
                  local.get 2
                  br_if 4 (;@2;)
                  br 5 (;@1;)
                end
                local.get 4
                local.get 2
                local.get 5
                i32.const 1
                i32.and
                i32.or
                i32.const 2
                i32.or
                i32.store
                local.get 7
                local.get 2
                i32.add
                local.tee 5
                local.get 1
                local.get 2
                i32.sub
                local.tee 2
                i32.const 1
                i32.or
                i32.store offset=4
                global.get $__memory_base
                i32.const 1048612
                i32.add
                local.tee 1
                local.get 2
                i32.store offset=420
                local.get 1
                local.get 5
                i32.store offset=428
              end
              local.get 7
              i32.eqz
              br_if 0 (;@4;)
              local.get 0
              return
            end
            local.get 3
            call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCskAuRjb5C0Ki_4p3rt
            local.tee 2
            i32.eqz
            br_if 2 (;@1;)
            local.get 3
            i32.const -4
            i32.const -8
            local.get 4
            i32.load
            local.tee 1
            i32.const 3
            i32.and
            select
            local.get 1
            i32.const -8
            i32.and
            i32.add
            local.tee 1
            local.get 3
            local.get 1
            i32.lt_u
            select
            local.tee 3
            i32.eqz
            br_if 0 (;@3;)
            local.get 2
            local.get 0
            local.get 3
            memory.copy
          end
          local.get 0
          call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt
        end
        local.get 2
        return
      end
      unreachable
    )
    (func $_RNvNtCs8o6ThntBNTu_6wasip37command40___link_custom_section_describing_imports (;66;) (type 7))
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable05lower (;67;) (type 3) (param i32 i32)
      block ;; label = @1
        block ;; label = @2
          local.get 0
          i32.const 255
          i32.and
          i32.const 255
          i32.ne
          br_if 0 (;@2;)
          i32.const 0
          local.set 0
          br 1 (;@1;)
        end
        local.get 1
        local.get 0
        i32.store8 offset=1
        i32.const 1
        local.set 0
      end
      local.get 1
      local.get 0
      i32.store8
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable013dealloc_lists (;68;) (type 1) (param i32))
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable04lift (;69;) (type 2) (param i32) (result i32)
      block ;; label = @1
        local.get 0
        i32.load8_u
        br_if 0 (;@1;)
        i32.const 255
        return
      end
      local.get 0
      i32.load8_u offset=1
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable011start_write (;70;) (type 0) (param i32 i32) (result i32)
      local.get 0
      local.get 1
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports11start_write
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable010start_read (;71;) (type 0) (param i32 i32) (result i32)
      local.get 0
      local.get 1
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports10start_read
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable012cancel_write (;72;) (type 2) (param i32) (result i32)
      local.get 0
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports12cancel_write
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable011cancel_read (;73;) (type 2) (param i32) (result i32)
      local.get 0
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports11cancel_read
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable013drop_writable (;74;) (type 1) (param i32)
      local.get 0
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports13drop_writable
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable013drop_readable (;75;) (type 1) (param i32)
      local.get 0
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports13drop_readable
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable03new (;76;) (type 8) (result i64)
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_future7vtable07imports3new
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable011start_write (;77;) (type 5) (param i32 i32 i32) (result i32)
      local.get 0
      local.get 1
      local.get 2
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports11start_write
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable010start_read (;78;) (type 5) (param i32 i32 i32) (result i32)
      local.get 0
      local.get 1
      local.get 2
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports10start_read
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable012cancel_write (;79;) (type 2) (param i32) (result i32)
      local.get 0
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports12cancel_write
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable011cancel_read (;80;) (type 2) (param i32) (result i32)
      local.get 0
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports11cancel_read
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable013drop_writable (;81;) (type 1) (param i32)
      local.get 0
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports13drop_writable
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable013drop_readable (;82;) (type 1) (param i32)
      local.get 0
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports13drop_readable
    )
    (func $_RNvNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable03new (;83;) (type 8) (result i64)
      call $_RNvNtNtNtNtCs8o6ThntBNTu_6wasip37imports10wit_stream7vtable07imports3new
    )
    (func $_RNvMsY_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB5_7NodeRefNtNtB5_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB19_14LeafOrInternalE16choose_parent_kvB1w_ (;84;) (type 10) (param i32 i32 i32)
      (local i32 i32 i32)
      block ;; label = @1
        local.get 1
        i32.load offset=88
        local.tee 3
        br_if 0 (;@1;)
        local.get 0
        local.get 2
        i32.store offset=8
        local.get 0
        local.get 1
        i32.store offset=4
        local.get 0
        i32.const 2
        i32.store
        return
      end
      local.get 2
      i32.const 1
      i32.add
      local.set 4
      block ;; label = @1
        block ;; label = @2
          local.get 1
          i32.load16_u offset=136
          local.tee 5
          br_if 0 (;@2;)
          local.get 3
          i32.load16_u offset=138
          i32.eqz
          br_if 1 (;@1;)
          local.get 0
          local.get 2
          i32.store offset=28
          local.get 0
          local.get 2
          i32.store offset=20
          local.get 0
          local.get 1
          i32.store offset=16
          local.get 0
          i32.const 0
          i32.store offset=12
          local.get 0
          local.get 4
          i32.store offset=8
          local.get 0
          local.get 3
          i32.store offset=4
          local.get 0
          i32.const 1
          i32.store
          local.get 0
          local.get 3
          i32.load offset=144
          i32.store offset=24
          return
        end
        local.get 0
        local.get 2
        i32.store offset=28
        local.get 0
        local.get 1
        i32.store offset=24
        local.get 0
        local.get 2
        i32.store offset=20
        local.get 0
        local.get 4
        i32.store offset=8
        local.get 0
        local.get 3
        i32.store offset=4
        local.get 0
        i32.const 0
        i32.store
        local.get 0
        local.get 5
        i32.const -1
        i32.add
        local.tee 1
        i32.store offset=12
        local.get 0
        local.get 3
        local.get 1
        i32.const 2
        i32.shl
        i32.add
        i32.load offset=140
        i32.store offset=16
        return
      end
      call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
      unreachable
    )
    (func $_RNvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB6_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE15bulk_steal_leftB1p_ (;85;) (type 3) (param i32 i32)
      (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i64)
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                local.get 1
                i32.eqz
                br_if 0 (;@5;)
                local.get 1
                local.get 0
                i32.load offset=20
                local.tee 2
                i32.load16_u offset=138
                local.tee 3
                i32.add
                local.tee 4
                i32.const 12
                i32.ge_u
                br_if 1 (;@4;)
                local.get 0
                i32.load offset=12
                local.tee 5
                i32.load16_u offset=138
                local.tee 6
                local.get 1
                i32.lt_u
                br_if 2 (;@3;)
                local.get 5
                local.get 6
                local.get 1
                i32.sub
                local.tee 7
                i32.store16 offset=138
                local.get 2
                local.get 4
                i32.store16 offset=138
                local.get 2
                i32.const 92
                i32.add
                local.set 8
                block ;; label = @6
                  local.get 3
                  i32.const 2
                  i32.shl
                  local.tee 9
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 8
                  local.get 1
                  i32.const 2
                  i32.shl
                  i32.add
                  local.get 8
                  local.get 9
                  memory.copy
                end
                block ;; label = @6
                  local.get 3
                  i32.const 3
                  i32.shl
                  local.tee 3
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 2
                  local.get 1
                  i32.const 3
                  i32.shl
                  i32.add
                  local.get 2
                  local.get 3
                  memory.copy
                end
                local.get 5
                i32.const 92
                i32.add
                local.set 3
                block ;; label = @6
                  local.get 6
                  local.get 7
                  i32.const 1
                  i32.add
                  local.tee 10
                  i32.sub
                  local.tee 6
                  i32.const 2
                  i32.shl
                  local.tee 11
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 8
                  local.get 3
                  local.get 10
                  i32.const 2
                  i32.shl
                  i32.add
                  local.get 11
                  memory.copy
                end
                block ;; label = @6
                  local.get 6
                  i32.const 3
                  i32.shl
                  local.tee 6
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 2
                  local.get 5
                  local.get 10
                  i32.const 3
                  i32.shl
                  i32.add
                  local.get 6
                  memory.copy
                end
                local.get 0
                i32.load
                local.tee 6
                local.get 0
                i32.load offset=8
                local.tee 11
                i32.const 2
                i32.shl
                i32.add
                local.tee 12
                i32.load offset=92
                local.set 13
                local.get 5
                local.get 7
                i32.const 3
                i32.shl
                i32.add
                i64.load align=4
                local.set 14
                local.get 12
                local.get 3
                local.get 7
                i32.const 2
                i32.shl
                i32.add
                i32.load
                i32.store offset=92
                local.get 6
                local.get 11
                i32.const 3
                i32.shl
                i32.add
                local.tee 7
                i64.load align=4
                local.set 15
                local.get 7
                local.get 14
                i64.store align=4
                local.get 2
                local.get 1
                i32.const -1
                i32.add
                local.tee 7
                i32.const 3
                i32.shl
                i32.add
                local.get 15
                i64.store align=4
                local.get 8
                local.get 7
                i32.const 2
                i32.shl
                i32.add
                local.get 13
                i32.store
                local.get 0
                i32.load offset=24
                local.set 7
                block ;; label = @6
                  local.get 0
                  i32.load offset=16
                  br_if 0 (;@6;)
                  local.get 7
                  br_if 4 (;@2;)
                  br 5 (;@1;)
                end
                local.get 7
                i32.eqz
                br_if 3 (;@2;)
                local.get 1
                i32.const 2
                i32.shl
                local.set 0
                local.get 2
                i32.const 140
                i32.add
                local.set 1
                block ;; label = @6
                  local.get 9
                  i32.const 4
                  i32.add
                  local.tee 7
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 1
                  local.get 0
                  i32.add
                  local.get 1
                  local.get 7
                  memory.copy
                end
                block ;; label = @6
                  local.get 0
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 1
                  local.get 5
                  local.get 10
                  i32.const 2
                  i32.shl
                  i32.add
                  i32.const 140
                  i32.add
                  local.get 0
                  memory.copy
                end
                local.get 4
                i32.const 1
                i32.add
                local.set 7
                i32.const 0
                local.set 0
                loop ;; label = @6
                  local.get 1
                  i32.load
                  local.tee 5
                  local.get 0
                  i32.store16 offset=136
                  local.get 5
                  local.get 2
                  i32.store offset=88
                  local.get 1
                  i32.const 4
                  i32.add
                  local.set 1
                  local.get 7
                  local.get 0
                  i32.const 1
                  i32.add
                  local.tee 0
                  i32.ne
                  br_if 0 (;@6;)
                  br 5 (;@1;)
                end
              end
              i32.const 27
              call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
              unreachable
            end
            i32.const 51
            call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
            unreachable
          end
          i32.const 39
          call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
          unreachable
        end
        i32.const 40
        call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
        unreachable
      end
    )
    (func $_RINvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB7_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE8do_mergeNCINvB2_21merge_tracking_parentNtNtBd_5alloc6GlobalE0INtB7_7NodeRefNtNtB7_6marker3MutmB1k_NtB3E_8InternalEB32_EB1q_ (;86;) (type 3) (param i32 i32)
      (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64)
      block ;; label = @1
        local.get 1
        i32.load offset=12
        local.tee 2
        i32.load16_u offset=138
        local.tee 3
        i32.const 1
        i32.add
        local.tee 4
        local.get 1
        i32.load offset=20
        local.tee 5
        i32.load16_u offset=138
        local.tee 6
        i32.add
        local.tee 7
        i32.const 12
        i32.ge_u
        br_if 0 (;@1;)
        local.get 1
        i32.load offset=4
        local.set 8
        local.get 1
        i32.load
        local.tee 9
        i32.load16_u offset=138
        local.set 10
        local.get 2
        local.get 7
        i32.store16 offset=138
        local.get 9
        local.get 1
        i32.load offset=8
        local.tee 7
        i32.const 2
        i32.shl
        i32.add
        local.tee 1
        i32.load offset=92
        local.set 11
        block ;; label = @2
          local.get 10
          local.get 7
          i32.const -1
          i32.xor
          i32.add
          local.tee 12
          i32.const 2
          i32.shl
          local.tee 13
          i32.eqz
          local.tee 14
          br_if 0 (;@2;)
          local.get 1
          i32.const 92
          i32.add
          local.get 1
          i32.const 96
          i32.add
          local.get 13
          memory.copy
        end
        local.get 2
        i32.const 92
        i32.add
        local.tee 1
        local.get 3
        i32.const 2
        i32.shl
        i32.add
        local.get 11
        i32.store
        block ;; label = @2
          local.get 6
          i32.const 2
          i32.shl
          local.tee 15
          i32.eqz
          br_if 0 (;@2;)
          local.get 1
          local.get 4
          i32.const 2
          i32.shl
          i32.add
          local.get 5
          i32.const 92
          i32.add
          local.get 15
          memory.copy
        end
        local.get 9
        local.get 7
        i32.const 3
        i32.shl
        i32.add
        local.tee 1
        i64.load align=4
        local.set 16
        block ;; label = @2
          local.get 12
          i32.const 3
          i32.shl
          local.tee 11
          i32.eqz
          br_if 0 (;@2;)
          local.get 1
          local.get 1
          i32.const 8
          i32.add
          local.get 11
          memory.copy
        end
        local.get 2
        local.get 3
        i32.const 3
        i32.shl
        i32.add
        local.get 16
        i64.store align=4
        block ;; label = @2
          local.get 6
          i32.const 3
          i32.shl
          local.tee 1
          i32.eqz
          br_if 0 (;@2;)
          local.get 2
          local.get 4
          i32.const 3
          i32.shl
          i32.add
          local.get 5
          local.get 1
          memory.copy
        end
        local.get 7
        i32.const 1
        i32.add
        local.set 1
        block ;; label = @2
          local.get 14
          br_if 0 (;@2;)
          local.get 9
          local.get 1
          i32.const 2
          i32.shl
          i32.add
          local.tee 11
          i32.const 140
          i32.add
          local.get 11
          i32.const 144
          i32.add
          local.get 13
          memory.copy
        end
        block ;; label = @2
          local.get 1
          local.get 10
          i32.ge_u
          br_if 0 (;@2;)
          local.get 7
          i32.const 2
          i32.shl
          local.get 9
          i32.add
          i32.const 144
          i32.add
          local.set 7
          loop ;; label = @3
            local.get 7
            i32.load
            local.tee 11
            local.get 1
            i32.store16 offset=136
            local.get 11
            local.get 9
            i32.store offset=88
            local.get 7
            i32.const 4
            i32.add
            local.set 7
            local.get 10
            local.get 1
            i32.const 1
            i32.add
            local.tee 1
            i32.ne
            br_if 0 (;@3;)
          end
        end
        local.get 9
        local.get 9
        i32.load16_u offset=138
        i32.const -1
        i32.add
        i32.store16 offset=138
        block ;; label = @2
          block ;; label = @3
            local.get 8
            i32.const 2
            i32.ge_u
            br_if 0 (;@3;)
            i32.const 140
            local.set 1
            br 1 (;@2;)
          end
          block ;; label = @3
            local.get 15
            i32.const 4
            i32.add
            local.tee 1
            i32.eqz
            br_if 0 (;@3;)
            local.get 2
            local.get 4
            i32.const 2
            i32.shl
            i32.add
            i32.const 140
            i32.add
            local.get 5
            i32.const 140
            i32.add
            local.get 1
            memory.copy
          end
          local.get 6
          i32.const 1
          i32.add
          local.set 7
          local.get 3
          i32.const 2
          i32.shl
          local.get 2
          i32.add
          i32.const 144
          i32.add
          local.set 1
          loop ;; label = @3
            local.get 1
            i32.load
            local.tee 11
            local.get 4
            i32.store16 offset=136
            local.get 11
            local.get 2
            i32.store offset=88
            local.get 1
            i32.const 4
            i32.add
            local.set 1
            local.get 4
            i32.const 1
            i32.add
            local.set 4
            local.get 7
            i32.const -1
            i32.add
            local.tee 7
            br_if 0 (;@3;)
          end
          i32.const 188
          local.set 1
        end
        local.get 5
        i32.const -4
        i32.add
        i32.load
        local.get 1
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
        local.get 5
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt
        local.get 0
        local.get 8
        i32.store offset=4
        local.get 0
        local.get 9
        i32.store
        return
      end
      i32.const 42
      call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
      unreachable
    )
    (func $_RNvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB6_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE16bulk_steal_rightB1p_ (;87;) (type 3) (param i32 i32)
      (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i64)
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                local.get 1
                i32.eqz
                br_if 0 (;@5;)
                local.get 1
                local.get 0
                i32.load offset=12
                local.tee 2
                i32.load16_u offset=138
                local.tee 3
                i32.add
                local.tee 4
                i32.const 12
                i32.ge_u
                br_if 1 (;@4;)
                local.get 0
                i32.load offset=20
                local.tee 5
                i32.load16_u offset=138
                local.tee 6
                local.get 1
                i32.lt_u
                br_if 2 (;@3;)
                local.get 2
                local.get 4
                i32.store16 offset=138
                local.get 5
                local.get 6
                local.get 1
                i32.sub
                local.tee 7
                i32.store16 offset=138
                local.get 0
                i32.load
                local.tee 4
                local.get 0
                i32.load offset=8
                local.tee 8
                i32.const 2
                i32.shl
                i32.add
                local.tee 9
                i32.load offset=92
                local.set 10
                local.get 5
                local.get 1
                i32.const -1
                i32.add
                local.tee 11
                i32.const 3
                i32.shl
                local.tee 6
                i32.add
                i64.load align=4
                local.set 12
                local.get 9
                local.get 5
                i32.const 92
                i32.add
                local.tee 13
                local.get 11
                i32.const 2
                i32.shl
                local.tee 11
                i32.add
                i32.load
                i32.store offset=92
                local.get 4
                local.get 8
                i32.const 3
                i32.shl
                i32.add
                local.tee 4
                i64.load align=4
                local.set 14
                local.get 4
                local.get 12
                i64.store align=4
                local.get 2
                i32.const 92
                i32.add
                local.tee 8
                local.get 3
                i32.const 2
                i32.shl
                i32.add
                local.get 10
                i32.store
                local.get 2
                local.get 3
                i32.const 3
                i32.shl
                i32.add
                local.get 14
                i64.store align=4
                local.get 3
                i32.const 1
                i32.add
                local.set 4
                block ;; label = @6
                  local.get 11
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 8
                  local.get 4
                  i32.const 2
                  i32.shl
                  i32.add
                  local.get 13
                  local.get 11
                  memory.copy
                end
                block ;; label = @6
                  local.get 6
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 2
                  local.get 4
                  i32.const 3
                  i32.shl
                  i32.add
                  local.get 5
                  local.get 6
                  memory.copy
                end
                block ;; label = @6
                  local.get 7
                  i32.const 2
                  i32.shl
                  local.tee 6
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 13
                  local.get 13
                  local.get 1
                  i32.const 2
                  i32.shl
                  i32.add
                  local.get 6
                  memory.copy
                end
                block ;; label = @6
                  local.get 7
                  i32.const 3
                  i32.shl
                  local.tee 13
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 5
                  local.get 5
                  local.get 1
                  i32.const 3
                  i32.shl
                  i32.add
                  local.get 13
                  memory.copy
                end
                local.get 0
                i32.load offset=24
                local.set 13
                block ;; label = @6
                  local.get 0
                  i32.load offset=16
                  br_if 0 (;@6;)
                  local.get 13
                  br_if 4 (;@2;)
                  br 5 (;@1;)
                end
                local.get 13
                i32.eqz
                br_if 3 (;@2;)
                local.get 5
                i32.const 140
                i32.add
                local.set 0
                block ;; label = @6
                  local.get 1
                  i32.const 2
                  i32.shl
                  local.tee 13
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 2
                  local.get 4
                  i32.const 2
                  i32.shl
                  i32.add
                  i32.const 140
                  i32.add
                  local.get 0
                  local.get 13
                  memory.copy
                end
                block ;; label = @6
                  local.get 6
                  i32.const 4
                  i32.add
                  local.tee 6
                  i32.eqz
                  br_if 0 (;@6;)
                  local.get 0
                  local.get 0
                  local.get 13
                  i32.add
                  local.get 6
                  memory.copy
                end
                local.get 3
                i32.const 2
                i32.shl
                local.get 2
                i32.add
                i32.const 144
                i32.add
                local.set 3
                loop ;; label = @6
                  local.get 3
                  i32.load
                  local.tee 6
                  local.get 4
                  i32.store16 offset=136
                  local.get 6
                  local.get 2
                  i32.store offset=88
                  local.get 3
                  i32.const 4
                  i32.add
                  local.set 3
                  local.get 4
                  i32.const 1
                  i32.add
                  local.set 4
                  local.get 1
                  i32.const -1
                  i32.add
                  local.tee 1
                  br_if 0 (;@6;)
                end
                local.get 7
                i32.const 1
                i32.add
                local.set 1
                i32.const 0
                local.set 4
                loop ;; label = @6
                  local.get 0
                  i32.load
                  local.tee 3
                  local.get 4
                  i32.store16 offset=136
                  local.get 3
                  local.get 5
                  i32.store offset=88
                  local.get 0
                  i32.const 4
                  i32.add
                  local.set 0
                  local.get 1
                  local.get 4
                  i32.const 1
                  i32.add
                  local.tee 4
                  i32.ne
                  br_if 0 (;@6;)
                  br 5 (;@1;)
                end
              end
              i32.const 27
              call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
              unreachable
            end
            i32.const 50
            call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
            unreachable
          end
          i32.const 40
          call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
          unreachable
        end
        i32.const 40
        call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
        unreachable
      end
    )
    (func $_RINvMs_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree6removeINtNtB7_4node6HandleINtBY_7NodeRefNtNtBY_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB1v_4LeafENtB1v_2KVE14remove_leaf_kvNCNvMs5_NtNtB7_3map5entryINtB3z_13OccupiedEntrymB1M_E9remove_kv0NtNtBb_5alloc6GlobalEB1S_ (;88;) (type 10) (param i32 i32 i32)
      (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
      global.get $__stack_pointer
      i32.const 80
      i32.sub
      local.tee 3
      global.set $__stack_pointer
      local.get 1
      i32.load
      local.tee 4
      local.get 1
      i32.load offset=8
      local.tee 5
      i32.const 2
      i32.shl
      i32.add
      local.tee 6
      i32.load offset=92
      local.set 7
      block ;; label = @1
        local.get 4
        i32.load16_u offset=138
        local.tee 8
        local.get 5
        i32.const -1
        i32.xor
        i32.add
        local.tee 9
        i32.const 2
        i32.shl
        local.tee 10
        i32.eqz
        br_if 0 (;@1;)
        local.get 6
        i32.const 92
        i32.add
        local.get 6
        i32.const 96
        i32.add
        local.get 10
        memory.copy
      end
      local.get 4
      local.get 5
      i32.const 3
      i32.shl
      i32.add
      local.tee 6
      i32.load offset=4
      local.set 11
      local.get 6
      i32.load
      local.set 12
      block ;; label = @1
        local.get 9
        i32.const 3
        i32.shl
        local.tee 9
        i32.eqz
        br_if 0 (;@1;)
        local.get 6
        local.get 6
        i32.const 8
        i32.add
        local.get 9
        memory.copy
      end
      local.get 4
      local.get 8
      i32.const -1
      i32.add
      local.tee 6
      i32.store16 offset=138
      local.get 1
      i32.load offset=4
      local.set 8
      block ;; label = @1
        local.get 6
        i32.const 65535
        i32.and
        i32.const 4
        i32.gt_u
        br_if 0 (;@1;)
        local.get 3
        i32.const 48
        i32.add
        local.get 4
        local.get 8
        call $_RNvMsY_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB5_7NodeRefNtNtB5_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB19_14LeafOrInternalE16choose_parent_kvB1w_
        local.get 3
        i32.const 48
        i32.add
        i32.const 4
        i32.add
        local.set 1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  block ;; label = @7
                    local.get 3
                    i32.load offset=48
                    br_table 1 (;@6;) 2 (;@5;) 0 (;@7;) 2 (;@5;)
                  end
                  local.get 3
                  local.get 5
                  i32.store offset=44
                  local.get 3
                  local.get 3
                  i32.load offset=56
                  local.tee 8
                  i32.store offset=40
                  local.get 3
                  local.get 3
                  i32.load offset=52
                  local.tee 4
                  i32.store offset=36
                  br 4 (;@2;)
                end
                block ;; label = @6
                  local.get 3
                  i32.load offset=64
                  i32.load16_u offset=138
                  local.get 3
                  i32.load offset=72
                  local.tee 4
                  i32.load16_u offset=138
                  i32.add
                  i32.const 1
                  i32.add
                  i32.const 12
                  i32.lt_u
                  br_if 0 (;@6;)
                  local.get 3
                  i32.load offset=76
                  local.set 8
                  local.get 1
                  i32.const 1
                  call $_RNvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB6_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE15bulk_steal_leftB1p_
                  local.get 5
                  i32.const 1
                  i32.add
                  local.set 5
                  br 2 (;@4;)
                end
                local.get 3
                i32.const 36
                i32.add
                local.get 1
                i32.const 1
                local.get 5
                call $_RINvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB7_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE25merge_tracking_child_edgeNtNtBd_5alloc6GlobalEB1q_
                local.get 3
                i32.load offset=44
                local.set 5
                local.get 3
                i32.load offset=36
                local.set 4
                local.get 3
                i32.load offset=40
                local.set 8
                br 3 (;@2;)
              end
              local.get 3
              i32.load offset=64
              local.tee 4
              i32.load16_u offset=138
              local.tee 6
              local.get 3
              i32.load offset=72
              i32.load16_u offset=138
              i32.add
              i32.const 1
              i32.add
              i32.const 12
              i32.lt_u
              br_if 1 (;@3;)
              local.get 3
              i32.load offset=68
              local.set 8
              local.get 1
              i32.const 1
              call $_RNvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB6_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE16bulk_steal_rightB1p_
            end
            local.get 3
            local.get 5
            i32.store offset=44
            local.get 3
            local.get 8
            i32.store offset=40
            local.get 3
            local.get 4
            i32.store offset=36
            br 1 (;@2;)
          end
          block ;; label = @3
            local.get 5
            local.get 6
            i32.gt_u
            br_if 0 (;@3;)
            local.get 3
            i32.const 24
            i32.add
            local.get 1
            call $_RINvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB7_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE8do_mergeNCINvB2_20merge_tracking_childNtNtBd_5alloc6GlobalE0INtB7_7NodeRefNtNtB7_6marker3MutmB1k_NtB3D_14LeafOrInternalEB31_EB1q_
            local.get 3
            local.get 5
            i32.store offset=44
            local.get 3
            local.get 3
            i32.load offset=28
            local.tee 8
            i32.store offset=40
            local.get 3
            local.get 3
            i32.load offset=24
            local.tee 4
            i32.store offset=36
            br 1 (;@2;)
          end
          i32.const 142
          call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
          unreachable
        end
        local.get 4
        i32.load offset=88
        local.tee 1
        i32.eqz
        br_if 0 (;@1;)
        local.get 8
        i32.const 1
        i32.add
        local.set 6
        local.get 3
        i32.const 48
        i32.add
        i32.const 4
        i32.add
        local.set 9
        loop ;; label = @2
          local.get 1
          i32.load16_u offset=138
          local.tee 10
          i32.const 4
          i32.gt_u
          br_if 1 (;@1;)
          local.get 3
          i32.const 48
          i32.add
          local.get 1
          local.get 6
          call $_RNvMsY_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB5_7NodeRefNtNtB5_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB19_14LeafOrInternalE16choose_parent_kvB1w_
          block ;; label = @3
            block ;; label = @4
              block ;; label = @5
                block ;; label = @6
                  block ;; label = @7
                    local.get 3
                    i32.load offset=48
                    br_table 0 (;@7;) 1 (;@6;) 2 (;@5;) 1 (;@6;)
                  end
                  local.get 3
                  i32.load offset=64
                  i32.load16_u offset=138
                  local.get 3
                  i32.load offset=72
                  i32.load16_u offset=138
                  i32.add
                  i32.const 1
                  i32.add
                  i32.const 12
                  i32.lt_u
                  br_if 2 (;@4;)
                  local.get 9
                  i32.const 5
                  local.get 10
                  i32.sub
                  call $_RNvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB6_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE15bulk_steal_leftB1p_
                  br 5 (;@1;)
                end
                block ;; label = @6
                  local.get 3
                  i32.load offset=64
                  i32.load16_u offset=138
                  local.get 3
                  i32.load offset=72
                  i32.load16_u offset=138
                  i32.add
                  i32.const 1
                  i32.add
                  i32.const 12
                  i32.lt_u
                  br_if 0 (;@6;)
                  local.get 9
                  i32.const 5
                  local.get 10
                  i32.sub
                  call $_RNvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB6_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE16bulk_steal_rightB1p_
                  br 5 (;@1;)
                end
                local.get 3
                i32.const 8
                i32.add
                local.get 9
                call $_RINvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB7_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE8do_mergeNCINvB2_21merge_tracking_parentNtNtBd_5alloc6GlobalE0INtB7_7NodeRefNtNtB7_6marker3MutmB1k_NtB3E_8InternalEB32_EB1q_
                local.get 3
                i32.load offset=12
                local.set 6
                local.get 3
                i32.load offset=8
                local.set 1
                br 2 (;@3;)
              end
              local.get 10
              br_if 3 (;@1;)
              local.get 2
              i32.const 1
              i32.store8
              br 3 (;@1;)
            end
            local.get 3
            i32.const 16
            i32.add
            local.get 9
            call $_RINvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB7_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE8do_mergeNCINvB2_21merge_tracking_parentNtNtBd_5alloc6GlobalE0INtB7_7NodeRefNtNtB7_6marker3MutmB1k_NtB3E_8InternalEB32_EB1q_
            local.get 3
            i32.load offset=20
            local.set 6
            local.get 3
            i32.load offset=16
            local.set 1
          end
          local.get 1
          br_if 0 (;@2;)
        end
      end
      local.get 0
      local.get 5
      i32.store offset=20
      local.get 0
      local.get 8
      i32.store offset=16
      local.get 0
      local.get 4
      i32.store offset=12
      local.get 0
      local.get 11
      i32.store offset=8
      local.get 0
      local.get 12
      i32.store offset=4
      local.get 0
      local.get 7
      i32.store
      local.get 3
      i32.const 80
      i32.add
      global.set $__stack_pointer
    )
    (func $_RINvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB7_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE25merge_tracking_child_edgeNtNtBd_5alloc6GlobalEB1q_ (;89;) (type 11) (param i32 i32 i32 i32)
      (local i32 i32)
      global.get $__stack_pointer
      i32.const 16
      i32.sub
      local.tee 4
      global.set $__stack_pointer
      local.get 1
      i32.load offset=12
      i32.load16_u offset=138
      local.set 5
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            local.get 2
            i32.const 1
            i32.ne
            br_if 0 (;@3;)
            local.get 3
            local.get 1
            i32.load offset=20
            i32.load16_u offset=138
            i32.gt_u
            br_if 2 (;@1;)
            local.get 4
            local.get 1
            call $_RINvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB7_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE8do_mergeNCINvB2_20merge_tracking_childNtNtBd_5alloc6GlobalE0INtB7_7NodeRefNtNtB7_6marker3MutmB1k_NtB3D_14LeafOrInternalEB31_EB1q_
            local.get 3
            local.get 5
            i32.add
            i32.const 1
            i32.add
            local.set 3
            local.get 4
            i32.load offset=4
            local.set 1
            local.get 4
            i32.load
            local.set 2
            br 1 (;@2;)
          end
          local.get 3
          local.get 5
          i32.gt_u
          br_if 1 (;@1;)
          local.get 4
          i32.const 8
          i32.add
          local.get 1
          call $_RINvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB7_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE8do_mergeNCINvB2_20merge_tracking_childNtNtBd_5alloc6GlobalE0INtB7_7NodeRefNtNtB7_6marker3MutmB1k_NtB3D_14LeafOrInternalEB31_EB1q_
          local.get 4
          i32.load offset=12
          local.set 1
          local.get 4
          i32.load offset=8
          local.set 2
        end
        local.get 0
        local.get 3
        i32.store offset=8
        local.get 0
        local.get 2
        i32.store
        local.get 0
        local.get 1
        i32.store offset=4
        local.get 4
        i32.const 16
        i32.add
        global.set $__stack_pointer
        return
      end
      i32.const 142
      call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
      unreachable
    )
    (func $_RINvMs10_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB7_16BalancingContextmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE8do_mergeNCINvB2_20merge_tracking_childNtNtBd_5alloc6GlobalE0INtB7_7NodeRefNtNtB7_6marker3MutmB1k_NtB3D_14LeafOrInternalEB31_EB1q_ (;90;) (type 3) (param i32 i32)
      (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64)
      block ;; label = @1
        local.get 1
        i32.load offset=12
        local.tee 2
        i32.load16_u offset=138
        local.tee 3
        i32.const 1
        i32.add
        local.tee 4
        local.get 1
        i32.load offset=20
        local.tee 5
        i32.load16_u offset=138
        local.tee 6
        i32.add
        local.tee 7
        i32.const 12
        i32.ge_u
        br_if 0 (;@1;)
        local.get 1
        i32.load offset=16
        local.set 8
        local.get 1
        i32.load offset=4
        local.set 9
        local.get 1
        i32.load
        local.tee 10
        i32.load16_u offset=138
        local.set 11
        local.get 2
        local.get 7
        i32.store16 offset=138
        local.get 10
        local.get 1
        i32.load offset=8
        local.tee 7
        i32.const 2
        i32.shl
        i32.add
        local.tee 1
        i32.load offset=92
        local.set 12
        block ;; label = @2
          local.get 11
          local.get 7
          i32.const -1
          i32.xor
          i32.add
          local.tee 13
          i32.const 2
          i32.shl
          local.tee 14
          i32.eqz
          local.tee 15
          br_if 0 (;@2;)
          local.get 1
          i32.const 92
          i32.add
          local.get 1
          i32.const 96
          i32.add
          local.get 14
          memory.copy
        end
        local.get 2
        i32.const 92
        i32.add
        local.tee 1
        local.get 3
        i32.const 2
        i32.shl
        i32.add
        local.get 12
        i32.store
        block ;; label = @2
          local.get 6
          i32.const 2
          i32.shl
          local.tee 16
          i32.eqz
          br_if 0 (;@2;)
          local.get 1
          local.get 4
          i32.const 2
          i32.shl
          i32.add
          local.get 5
          i32.const 92
          i32.add
          local.get 16
          memory.copy
        end
        local.get 10
        local.get 7
        i32.const 3
        i32.shl
        i32.add
        local.tee 1
        i64.load align=4
        local.set 17
        block ;; label = @2
          local.get 13
          i32.const 3
          i32.shl
          local.tee 12
          i32.eqz
          br_if 0 (;@2;)
          local.get 1
          local.get 1
          i32.const 8
          i32.add
          local.get 12
          memory.copy
        end
        local.get 2
        local.get 3
        i32.const 3
        i32.shl
        i32.add
        local.get 17
        i64.store align=4
        block ;; label = @2
          local.get 6
          i32.const 3
          i32.shl
          local.tee 1
          i32.eqz
          br_if 0 (;@2;)
          local.get 2
          local.get 4
          i32.const 3
          i32.shl
          i32.add
          local.get 5
          local.get 1
          memory.copy
        end
        local.get 7
        i32.const 1
        i32.add
        local.set 1
        block ;; label = @2
          local.get 15
          br_if 0 (;@2;)
          local.get 10
          local.get 1
          i32.const 2
          i32.shl
          i32.add
          local.tee 12
          i32.const 140
          i32.add
          local.get 12
          i32.const 144
          i32.add
          local.get 14
          memory.copy
        end
        block ;; label = @2
          local.get 1
          local.get 11
          i32.ge_u
          br_if 0 (;@2;)
          local.get 7
          i32.const 2
          i32.shl
          local.get 10
          i32.add
          i32.const 144
          i32.add
          local.set 7
          loop ;; label = @3
            local.get 7
            i32.load
            local.tee 12
            local.get 1
            i32.store16 offset=136
            local.get 12
            local.get 10
            i32.store offset=88
            local.get 7
            i32.const 4
            i32.add
            local.set 7
            local.get 11
            local.get 1
            i32.const 1
            i32.add
            local.tee 1
            i32.ne
            br_if 0 (;@3;)
          end
        end
        local.get 10
        local.get 10
        i32.load16_u offset=138
        i32.const -1
        i32.add
        i32.store16 offset=138
        block ;; label = @2
          block ;; label = @3
            local.get 9
            i32.const 2
            i32.ge_u
            br_if 0 (;@3;)
            i32.const 140
            local.set 1
            br 1 (;@2;)
          end
          block ;; label = @3
            local.get 16
            i32.const 4
            i32.add
            local.tee 1
            i32.eqz
            br_if 0 (;@3;)
            local.get 2
            local.get 4
            i32.const 2
            i32.shl
            i32.add
            i32.const 140
            i32.add
            local.get 5
            i32.const 140
            i32.add
            local.get 1
            memory.copy
          end
          local.get 6
          i32.const 1
          i32.add
          local.set 7
          local.get 3
          i32.const 2
          i32.shl
          local.get 2
          i32.add
          i32.const 144
          i32.add
          local.set 1
          loop ;; label = @3
            local.get 1
            i32.load
            local.tee 12
            local.get 4
            i32.store16 offset=136
            local.get 12
            local.get 2
            i32.store offset=88
            local.get 1
            i32.const 4
            i32.add
            local.set 1
            local.get 4
            i32.const 1
            i32.add
            local.set 4
            local.get 7
            i32.const -1
            i32.add
            local.tee 7
            br_if 0 (;@3;)
          end
          i32.const 188
          local.set 1
        end
        local.get 5
        i32.const -4
        i32.add
        i32.load
        local.get 1
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
        local.get 5
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt
        local.get 0
        local.get 8
        i32.store offset=4
        local.get 0
        local.get 2
        i32.store
        return
      end
      i32.const 42
      call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
      unreachable
    )
    (func $_RINvMsV_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB6_6HandleINtB6_7NodeRefNtNtB6_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB1n_4LeafENtB1n_2KVE5splitNtNtBc_5alloc6GlobalEB1K_ (;91;) (type 3) (param i32 i32)
      (local i32 i32 i32 i32 i32 i32 i32 i64 i32)
      block ;; label = @1
        block ;; label = @2
          i32.const 140
          call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCskAuRjb5C0Ki_4p3rt
          local.tee 2
          i32.eqz
          br_if 0 (;@2;)
          local.get 2
          i32.const 0
          i32.store16 offset=138
          local.get 2
          i32.const 0
          i32.store offset=88
          local.get 2
          local.get 1
          i32.load offset=8
          local.tee 3
          i32.const -1
          i32.xor
          local.get 1
          i32.load
          local.tee 4
          i32.load16_u offset=138
          i32.add
          local.tee 5
          i32.store16 offset=138
          local.get 5
          i32.const 12
          i32.ge_u
          br_if 1 (;@1;)
          local.get 4
          i32.const 92
          i32.add
          local.tee 6
          local.get 3
          i32.const 2
          i32.shl
          i32.add
          i32.load
          local.set 7
          local.get 3
          i32.const 1
          i32.add
          local.set 8
          local.get 4
          local.get 3
          i32.const 3
          i32.shl
          i32.add
          i64.load align=4
          local.set 9
          block ;; label = @3
            local.get 5
            i32.const 2
            i32.shl
            local.tee 10
            i32.eqz
            br_if 0 (;@3;)
            local.get 2
            i32.const 92
            i32.add
            local.get 6
            local.get 8
            i32.const 2
            i32.shl
            i32.add
            local.get 10
            memory.copy
          end
          block ;; label = @3
            local.get 5
            i32.const 3
            i32.shl
            local.tee 5
            i32.eqz
            br_if 0 (;@3;)
            local.get 2
            local.get 4
            local.get 8
            i32.const 3
            i32.shl
            i32.add
            local.get 5
            memory.copy
          end
          local.get 0
          local.get 9
          i64.store offset=20 align=4
          local.get 0
          local.get 7
          i32.store offset=16
          local.get 4
          local.get 3
          i32.store16 offset=138
          local.get 0
          i32.const 0
          i32.store offset=12
          local.get 0
          local.get 2
          i32.store offset=8
          local.get 0
          local.get 4
          i32.store
          local.get 0
          local.get 1
          i32.load offset=4
          i32.store offset=4
          return
        end
        call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
        unreachable
      end
      i32.const 0
      local.get 5
      i32.const 11
      call $_RNvNtNtCshQUFA83YM6w_4core5slice5index16slice_index_fail
      unreachable
    )
    (func $_RNvMsM_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB5_6HandleINtB5_7NodeRefNtNtB5_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB1m_8InternalENtB1m_4EdgeE10insert_fitB1J_ (;92;) (type 12) (param i32 i32 i32 i32 i32 i32)
      (local i32 i32 i32 i32 i32 i32)
      local.get 0
      i32.const 92
      i32.add
      local.tee 6
      local.get 1
      i32.const 2
      i32.shl
      i32.add
      local.set 7
      block ;; label = @1
        block ;; label = @2
          local.get 1
          i32.const 1
          i32.add
          local.tee 8
          local.get 0
          i32.load16_u offset=138
          local.tee 9
          i32.le_u
          br_if 0 (;@2;)
          local.get 7
          local.get 2
          i32.store
          br 1 (;@1;)
        end
        block ;; label = @2
          local.get 9
          local.get 1
          i32.sub
          local.tee 10
          i32.const 2
          i32.shl
          local.tee 11
          i32.eqz
          br_if 0 (;@2;)
          local.get 6
          local.get 8
          i32.const 2
          i32.shl
          i32.add
          local.get 7
          local.get 11
          memory.copy
        end
        local.get 7
        local.get 2
        i32.store
        local.get 10
        i32.const 3
        i32.shl
        local.tee 7
        i32.eqz
        br_if 0 (;@1;)
        local.get 0
        local.get 8
        i32.const 3
        i32.shl
        i32.add
        local.get 0
        local.get 1
        i32.const 3
        i32.shl
        i32.add
        local.get 7
        memory.copy
      end
      local.get 9
      i32.const 1
      i32.add
      local.set 2
      local.get 0
      local.get 1
      i32.const 3
      i32.shl
      i32.add
      local.tee 7
      local.get 4
      i32.store offset=4
      local.get 7
      local.get 3
      i32.store
      local.get 0
      i32.const 140
      i32.add
      local.set 7
      block ;; label = @1
        local.get 9
        i32.const 2
        i32.add
        local.tee 4
        local.get 1
        i32.const 2
        i32.add
        local.tee 3
        i32.le_u
        br_if 0 (;@1;)
        local.get 9
        local.get 1
        i32.sub
        i32.const 2
        i32.shl
        local.tee 6
        i32.eqz
        br_if 0 (;@1;)
        local.get 7
        local.get 3
        i32.const 2
        i32.shl
        i32.add
        local.get 7
        local.get 8
        i32.const 2
        i32.shl
        i32.add
        local.get 6
        memory.copy
      end
      local.get 7
      local.get 8
      i32.const 2
      i32.shl
      i32.add
      local.get 5
      i32.store
      local.get 0
      local.get 2
      i32.store16 offset=138
      block ;; label = @1
        local.get 8
        local.get 4
        i32.ge_u
        br_if 0 (;@1;)
        local.get 9
        i32.const 1
        i32.add
        local.set 7
        local.get 1
        i32.const 2
        i32.shl
        local.get 0
        i32.add
        i32.const 144
        i32.add
        local.set 9
        loop ;; label = @2
          local.get 9
          i32.load
          local.tee 8
          local.get 1
          i32.const 1
          i32.add
          local.tee 1
          i32.store16 offset=136
          local.get 8
          local.get 0
          i32.store offset=88
          local.get 9
          i32.const 4
          i32.add
          local.set 9
          local.get 7
          local.get 1
          i32.ne
          br_if 0 (;@2;)
        end
      end
    )
    (func $_RINvMsW_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB6_6HandleINtB6_7NodeRefNtNtB6_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB1n_8InternalENtB1n_2KVE5splitNtNtBc_5alloc6GlobalEB1K_ (;93;) (type 3) (param i32 i32)
      (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
      local.get 1
      i32.load
      local.tee 2
      i32.load16_u offset=138
      local.set 3
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            i32.const 188
            call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCskAuRjb5C0Ki_4p3rt
            local.tee 4
            i32.eqz
            br_if 0 (;@3;)
            local.get 4
            i32.const 0
            i32.store16 offset=138
            local.get 4
            i32.const 0
            i32.store offset=88
            local.get 4
            local.get 1
            i32.load offset=8
            local.tee 5
            i32.const -1
            i32.xor
            local.get 2
            i32.load16_u offset=138
            i32.add
            local.tee 6
            i32.store16 offset=138
            local.get 6
            i32.const 12
            i32.ge_u
            br_if 1 (;@2;)
            local.get 2
            i32.const 92
            i32.add
            local.tee 7
            local.get 5
            i32.const 2
            i32.shl
            i32.add
            i32.load
            local.set 8
            local.get 5
            i32.const 1
            i32.add
            local.set 9
            local.get 2
            local.get 5
            i32.const 3
            i32.shl
            i32.add
            local.tee 10
            i32.load
            local.set 11
            local.get 10
            i32.load offset=4
            local.set 10
            block ;; label = @4
              local.get 6
              i32.const 2
              i32.shl
              local.tee 12
              i32.eqz
              br_if 0 (;@4;)
              local.get 4
              i32.const 92
              i32.add
              local.get 7
              local.get 9
              i32.const 2
              i32.shl
              i32.add
              local.get 12
              memory.copy
            end
            block ;; label = @4
              local.get 6
              i32.const 3
              i32.shl
              local.tee 6
              i32.eqz
              br_if 0 (;@4;)
              local.get 4
              local.get 2
              local.get 9
              i32.const 3
              i32.shl
              i32.add
              local.get 6
              memory.copy
            end
            local.get 2
            local.get 5
            i32.store16 offset=138
            local.get 4
            i32.load16_u offset=138
            local.tee 6
            i32.const 1
            i32.add
            local.set 9
            block ;; label = @4
              local.get 6
              i32.const 11
              i32.gt_u
              br_if 0 (;@4;)
              local.get 3
              local.get 5
              i32.sub
              local.get 9
              i32.ne
              br_if 3 (;@1;)
              local.get 4
              i32.const 140
              i32.add
              local.set 6
              block ;; label = @5
                local.get 9
                i32.const 2
                i32.shl
                local.tee 3
                i32.eqz
                br_if 0 (;@5;)
                local.get 6
                local.get 2
                local.get 5
                i32.const 2
                i32.shl
                i32.add
                i32.const 144
                i32.add
                local.get 3
                memory.copy
              end
              local.get 1
              i32.load offset=4
              local.set 3
              i32.const 0
              local.set 5
              loop ;; label = @5
                local.get 6
                i32.load
                local.tee 1
                local.get 5
                i32.store16 offset=136
                local.get 1
                local.get 4
                i32.store offset=88
                local.get 6
                i32.const 4
                i32.add
                local.set 6
                local.get 9
                local.get 5
                i32.const 1
                i32.add
                local.tee 5
                i32.ne
                br_if 0 (;@5;)
              end
              local.get 0
              local.get 10
              i32.store offset=24
              local.get 0
              local.get 11
              i32.store offset=20
              local.get 0
              local.get 8
              i32.store offset=16
              local.get 0
              local.get 3
              i32.store offset=4
              local.get 0
              local.get 2
              i32.store
              local.get 0
              local.get 3
              i32.store offset=12
              local.get 0
              local.get 4
              i32.store offset=8
              return
            end
            i32.const 0
            local.get 9
            i32.const 12
            call $_RNvNtNtCshQUFA83YM6w_4core5slice5index16slice_index_fail
            unreachable
          end
          call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
          unreachable
        end
        i32.const 0
        local.get 6
        i32.const 11
        call $_RNvNtNtCshQUFA83YM6w_4core5slice5index16slice_index_fail
        unreachable
      end
      i32.const 40
      call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
      unreachable
    )
    (func $_RINvMsi_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree3mapINtB6_8BTreeMapmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE12remove_entrymEB1f_ (;94;) (type 10) (param i32 i32 i32)
      (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64)
      global.get $__stack_pointer
      i32.const 48
      i32.sub
      local.tee 3
      global.set $__stack_pointer
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              local.get 1
              i32.load
              local.tee 4
              i32.eqz
              br_if 0 (;@4;)
              local.get 1
              i32.load offset=4
              local.tee 5
              local.set 6
              local.get 4
              local.set 7
              loop ;; label = @5
                local.get 7
                i32.const 92
                i32.add
                local.set 8
                local.get 7
                i32.load16_u offset=138
                local.tee 9
                i32.const 2
                i32.shl
                local.set 10
                i32.const -1
                local.set 11
                block ;; label = @6
                  loop ;; label = @7
                    block ;; label = @8
                      local.get 10
                      br_if 0 (;@8;)
                      local.get 9
                      local.set 11
                      br 2 (;@6;)
                    end
                    local.get 8
                    i32.load
                    local.set 12
                    local.get 10
                    i32.const -4
                    i32.add
                    local.set 10
                    local.get 11
                    i32.const 1
                    i32.add
                    local.set 11
                    local.get 8
                    i32.const 4
                    i32.add
                    local.set 8
                    local.get 2
                    local.get 12
                    i32.gt_u
                    local.get 2
                    local.get 12
                    i32.lt_u
                    i32.sub
                    i32.const 255
                    i32.and
                    local.tee 12
                    i32.const 1
                    i32.eq
                    br_if 0 (;@7;)
                  end
                  local.get 12
                  i32.eqz
                  br_if 4 (;@2;)
                end
                local.get 6
                i32.eqz
                br_if 2 (;@3;)
                local.get 6
                i32.const -1
                i32.add
                local.set 6
                local.get 7
                local.get 11
                i32.const 2
                i32.shl
                i32.add
                i32.load offset=140
                local.set 7
                br 0 (;@5;)
              end
            end
            local.get 0
            i32.const 0
            i32.store offset=4
            br 2 (;@1;)
          end
          local.get 0
          i32.const 0
          i32.store offset=4
          br 1 (;@1;)
        end
        local.get 3
        i32.const 0
        i32.store8 offset=11
        block ;; label = @2
          block ;; label = @3
            local.get 6
            br_if 0 (;@3;)
            local.get 3
            local.get 11
            i32.store offset=20
            local.get 3
            i32.const 0
            i32.store offset=16
            local.get 3
            local.get 7
            i32.store offset=12
            local.get 3
            i32.const 24
            i32.add
            local.get 3
            i32.const 12
            i32.add
            local.get 3
            i32.const 11
            i32.add
            call $_RINvMs_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree6removeINtNtB7_4node6HandleINtBY_7NodeRefNtNtBY_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB1v_4LeafENtB1v_2KVE14remove_leaf_kvNCNvMs5_NtNtB7_3map5entryINtB3z_13OccupiedEntrymB1M_E9remove_kv0NtNtBb_5alloc6GlobalEB1S_
            br 1 (;@2;)
          end
          local.get 7
          local.get 11
          i32.const 2
          i32.shl
          i32.add
          i32.load offset=140
          local.set 10
          block ;; label = @3
            local.get 6
            i32.const 1
            i32.eq
            br_if 0 (;@3;)
            i32.const 1
            local.set 8
            loop ;; label = @4
              local.get 10
              local.get 10
              i32.load16_u offset=138
              i32.const 2
              i32.shl
              i32.add
              i32.load offset=140
              local.set 10
              local.get 6
              local.get 8
              i32.const 1
              i32.add
              local.tee 8
              i32.ne
              br_if 0 (;@4;)
            end
          end
          local.get 3
          local.get 10
          i32.load16_u offset=138
          i32.const -1
          i32.add
          i32.store offset=20
          local.get 3
          i32.const 0
          i32.store offset=16
          local.get 3
          local.get 10
          i32.store offset=12
          local.get 3
          i32.const 24
          i32.add
          local.get 3
          i32.const 12
          i32.add
          local.get 3
          i32.const 11
          i32.add
          call $_RINvMs_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree6removeINtNtB7_4node6HandleINtBY_7NodeRefNtNtBY_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB1v_4LeafENtB1v_2KVE14remove_leaf_kvNCNvMs5_NtNtB7_3map5entryINtB3z_13OccupiedEntrymB1M_E9remove_kv0NtNtBb_5alloc6GlobalEB1S_
          local.get 3
          i32.load offset=32
          local.set 11
          local.get 3
          i32.load offset=28
          local.set 2
          local.get 3
          i32.load offset=24
          local.set 6
          block ;; label = @3
            local.get 3
            i32.load offset=44
            local.tee 12
            local.get 3
            i32.load offset=36
            local.tee 10
            i32.load16_u offset=138
            i32.lt_u
            br_if 0 (;@3;)
            local.get 3
            i32.load offset=40
            local.set 8
            loop ;; label = @4
              local.get 8
              i32.const 1
              i32.add
              local.set 8
              local.get 10
              i32.load16_u offset=136
              local.tee 12
              local.get 10
              i32.load offset=88
              local.tee 10
              i32.load16_u offset=138
              i32.ge_u
              br_if 0 (;@4;)
            end
          end
          local.get 10
          local.get 12
          i32.const 2
          i32.shl
          i32.add
          local.tee 8
          i32.load offset=92
          local.set 7
          local.get 8
          local.get 6
          i32.store offset=92
          local.get 10
          local.get 12
          i32.const 3
          i32.shl
          i32.add
          local.tee 10
          i64.load align=4
          local.set 13
          local.get 10
          local.get 11
          i32.store offset=4
          local.get 10
          local.get 2
          i32.store
          local.get 3
          local.get 7
          i32.store offset=24
          local.get 3
          local.get 13
          i64.store offset=28 align=4
        end
        local.get 0
        local.get 3
        i32.load offset=32
        i32.store offset=8
        local.get 0
        local.get 3
        i64.load offset=24 align=4
        i64.store align=4
        local.get 1
        local.get 1
        i32.load offset=8
        i32.const -1
        i32.add
        i32.store offset=8
        local.get 3
        i32.load8_u offset=11
        i32.const 1
        i32.ne
        br_if 0 (;@1;)
        block ;; label = @2
          local.get 5
          i32.eqz
          br_if 0 (;@2;)
          local.get 4
          i32.load offset=140
          local.tee 10
          i32.const 0
          i32.store offset=88
          local.get 1
          local.get 5
          i32.const -1
          i32.add
          i32.store offset=4
          local.get 1
          local.get 10
          i32.store
          local.get 4
          i32.const -4
          i32.add
          i32.load
          i32.const 188
          call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
          local.get 4
          call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt
          br 1 (;@1;)
        end
        i32.const 33
        call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
        unreachable
      end
      local.get 3
      i32.const 48
      i32.add
      global.set $__stack_pointer
    )
    (func $_RINvNtCshQUFA83YM6w_4core9panicking13assert_failedmmECscNOpLhlpk4u_11wit_bindgen (;95;) (type 1) (param i32)
      call $_RNvNtCshQUFA83YM6w_4core9panicking19assert_failed_inner
      unreachable
    )
    (func $_RINvNvNtCsiqQVI2xHy0t_5alloc4task9raw_waker10drop_wakerNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support15SharedTaskStateEBX_ (;96;) (type 1) (param i32)
      (local i32)
      local.get 0
      i32.const -8
      i32.add
      local.tee 0
      local.get 0
      i32.load
      local.tee 1
      i32.const -1
      i32.add
      i32.store
      block ;; label = @1
        local.get 1
        i32.const 1
        i32.ne
        br_if 0 (;@1;)
        local.get 0
        call $_RNvMsn_NtCsiqQVI2xHy0t_5alloc4syncINtB5_3ArcNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support15SharedTaskStateE9drop_slowBM_
      end
    )
    (func $_RNvMsn_NtCsiqQVI2xHy0t_5alloc4syncINtB5_3ArcNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support15SharedTaskStateE9drop_slowBM_ (;97;) (type 1) (param i32)
      (local i32 i32 i32 i32 i32 i32)
      i32.const 0
      local.set 1
      block ;; label = @1
        block ;; label = @2
          local.get 0
          i32.load offset=8
          local.tee 2
          br_if 0 (;@2;)
          i32.const 0
          local.set 3
          i32.const 0
          local.set 4
          br 1 (;@1;)
        end
        local.get 0
        i32.load offset=12
        local.set 5
        local.get 0
        i32.load offset=16
        local.set 3
        i32.const 1
        local.set 4
      end
      block ;; label = @1
        block ;; label = @2
          loop ;; label = @3
            block ;; label = @4
              local.get 3
              br_if 0 (;@4;)
              local.get 4
              i32.const 1
              i32.and
              i32.eqz
              br_if 3 (;@1;)
              block ;; label = @5
                local.get 1
                i32.eqz
                br_if 0 (;@5;)
                local.get 2
                local.set 6
                local.get 1
                local.set 2
                br 3 (;@2;)
              end
              i32.const 0
              local.set 6
              local.get 5
              i32.eqz
              br_if 2 (;@2;)
              loop ;; label = @5
                local.get 2
                i32.load offset=140
                local.set 2
                local.get 5
                i32.const -1
                i32.add
                local.tee 5
                br_if 0 (;@5;)
                br 3 (;@2;)
              end
            end
            block ;; label = @4
              block ;; label = @5
                local.get 4
                i32.const 1
                i32.and
                i32.eqz
                br_if 0 (;@5;)
                block ;; label = @6
                  block ;; label = @7
                    local.get 1
                    i32.eqz
                    br_if 0 (;@7;)
                    local.get 5
                    local.set 6
                    local.get 2
                    local.set 5
                    local.get 1
                    local.set 2
                    br 1 (;@6;)
                  end
                  i32.const 0
                  local.set 6
                  block ;; label = @7
                    local.get 5
                    i32.eqz
                    br_if 0 (;@7;)
                    loop ;; label = @8
                      local.get 2
                      i32.load offset=140
                      local.set 2
                      local.get 5
                      i32.const -1
                      i32.add
                      local.tee 5
                      br_if 0 (;@8;)
                    end
                  end
                  i32.const 0
                  local.set 5
                end
                block ;; label = @6
                  local.get 6
                  local.get 2
                  i32.load16_u offset=138
                  i32.ge_u
                  br_if 0 (;@6;)
                  local.get 2
                  local.set 1
                  br 2 (;@4;)
                end
                block ;; label = @6
                  loop ;; label = @7
                    local.get 2
                    i32.load offset=88
                    local.tee 1
                    i32.eqz
                    br_if 1 (;@6;)
                    local.get 2
                    i32.load16_u offset=136
                    local.set 6
                    local.get 2
                    i32.const -4
                    i32.add
                    i32.load
                    i32.const 188
                    i32.const 140
                    local.get 5
                    select
                    call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
                    local.get 2
                    call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt
                    local.get 5
                    i32.const 1
                    i32.add
                    local.set 5
                    local.get 1
                    local.set 2
                    local.get 6
                    local.get 1
                    i32.load16_u offset=138
                    i32.lt_u
                    br_if 3 (;@4;)
                    br 0 (;@7;)
                  end
                end
                local.get 2
                i32.const -4
                i32.add
                i32.load
                i32.const 188
                i32.const 140
                local.get 5
                select
                call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
                local.get 2
                call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt
              end
              call $_RNvNtCshQUFA83YM6w_4core6option13unwrap_failed
              unreachable
            end
            local.get 3
            i32.const -1
            i32.add
            local.set 3
            block ;; label = @4
              local.get 5
              br_if 0 (;@4;)
              i32.const 1
              local.set 4
              local.get 6
              i32.const 1
              i32.add
              local.set 5
              i32.const 0
              local.set 2
              br 1 (;@3;)
            end
            local.get 1
            local.get 6
            i32.const 2
            i32.shl
            i32.add
            i32.const 144
            i32.add
            local.set 2
            loop ;; label = @4
              local.get 2
              i32.load
              local.tee 1
              i32.const 140
              i32.add
              local.set 2
              local.get 5
              i32.const -1
              i32.add
              local.tee 5
              br_if 0 (;@4;)
            end
            i32.const 1
            local.set 4
            i32.const 0
            local.set 5
            i32.const 0
            local.set 2
            br 0 (;@3;)
          end
        end
        block ;; label = @2
          local.get 2
          i32.load offset=88
          local.tee 5
          i32.eqz
          br_if 0 (;@2;)
          loop ;; label = @3
            local.get 2
            local.tee 2
            i32.const -4
            i32.add
            i32.load
            i32.const 188
            i32.const 140
            local.get 6
            select
            call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
            local.get 2
            call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt
            local.get 6
            i32.const 1
            i32.add
            local.set 6
            local.get 5
            local.tee 2
            i32.load offset=88
            local.tee 5
            br_if 0 (;@3;)
          end
        end
        local.get 2
        i32.const -4
        i32.add
        i32.load
        i32.const 188
        i32.const 140
        local.get 6
        select
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
        local.get 2
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt
      end
      block ;; label = @1
        local.get 0
        i32.load offset=24
        local.tee 2
        i32.eqz
        br_if 0 (;@1;)
        local.get 2
        call $_RNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12waitable_set4drop
      end
      block ;; label = @1
        local.get 0
        i32.const -1
        i32.eq
        br_if 0 (;@1;)
        local.get 0
        local.get 0
        i32.load offset=4
        local.tee 2
        i32.const -1
        i32.add
        i32.store offset=4
        local.get 2
        i32.const 1
        i32.ne
        br_if 0 (;@1;)
        local.get 0
        i32.const -4
        i32.add
        i32.load
        i32.const 36
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
        local.get 0
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt
      end
    )
    (func $_RINvNvNtCsiqQVI2xHy0t_5alloc4task9raw_waker11wake_by_refNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support15SharedTaskStateEBY_ (;98;) (type 1) (param i32)
      local.get 0
      i32.const -8
      i32.add
      call $_RNvXs2_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB5_15SharedTaskStateNtNtCsiqQVI2xHy0t_5alloc4task4Wake11wake_by_ref
    )
    (func $_RNvXs2_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB5_15SharedTaskStateNtNtCsiqQVI2xHy0t_5alloc4task4Wake11wake_by_ref (;99;) (type 1) (param i32)
      (local i32 i32)
      global.get $__stack_pointer
      i32.const 16
      i32.sub
      local.tee 1
      global.set $__stack_pointer
      local.get 0
      i32.load offset=32
      local.set 2
      local.get 0
      i32.const 1
      i32.store offset=32
      block ;; label = @1
        block ;; label = @2
          local.get 2
          i32.const 2
          i32.lt_u
          br_if 0 (;@2;)
          local.get 2
          i32.const 2
          i32.eq
          br_if 1 (;@1;)
          local.get 1
          i32.const 12
          i32.add
          call $_RINvNtCshQUFA83YM6w_4core9panicking13assert_failedmmECscNOpLhlpk4u_11wit_bindgen
          unreachable
        end
        local.get 1
        i32.const 16
        i32.add
        global.set $__stack_pointer
        return
      end
      call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
      unreachable
    )
    (func $_RINvNvNtCsiqQVI2xHy0t_5alloc4task9raw_waker4wakeNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support15SharedTaskStateEBQ_ (;100;) (type 1) (param i32)
      (local i32)
      local.get 0
      i32.const -8
      i32.add
      local.tee 0
      call $_RNvXs2_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB5_15SharedTaskStateNtNtCsiqQVI2xHy0t_5alloc4task4Wake11wake_by_ref
      local.get 0
      local.get 0
      i32.load
      local.tee 1
      i32.const -1
      i32.add
      i32.store
      block ;; label = @1
        local.get 1
        i32.const 1
        i32.ne
        br_if 0 (;@1;)
        local.get 0
        call $_RNvMsn_NtCsiqQVI2xHy0t_5alloc4syncINtB5_3ArcNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support15SharedTaskStateE9drop_slowBM_
      end
    )
    (func $_RINvNvNtCsiqQVI2xHy0t_5alloc4task9raw_waker11clone_wakerNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support15SharedTaskStateEBY_ (;101;) (type 3) (param i32 i32)
      (local i32)
      local.get 1
      i32.const -8
      i32.add
      local.tee 2
      local.get 2
      i32.load
      local.tee 2
      i32.const 1
      i32.add
      i32.store
      block ;; label = @1
        local.get 2
        i32.const -1
        i32.gt_s
        br_if 0 (;@1;)
        unreachable
      end
      local.get 0
      local.get 1
      i32.store offset=4
      local.get 0
      global.get $__memory_base
      i32.const 1049284
      i32.add
      i32.store
    )
    (func $_RNvMs1_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB5_15SharedTaskState22cabi_waitable_register (;102;) (type 4) (param i32 i32 i32 i32) (result i32)
      (local i32 i32 i32 i32 i32 i32 i32 i32 i32)
      global.get $__stack_pointer
      i32.const 48
      i32.sub
      local.tee 4
      global.set $__stack_pointer
      local.get 0
      i32.load8_u offset=20
      local.set 5
      local.get 0
      i32.const 1
      i32.store8 offset=20
      block ;; label = @1
        block ;; label = @2
          block ;; label = @3
            block ;; label = @4
              local.get 5
              br_if 0 (;@4;)
              block ;; label = @5
                local.get 0
                i32.load offset=16
                local.tee 5
                br_if 0 (;@5;)
                call $_RNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12waitable_set3new
                local.tee 5
                i32.eqz
                br_if 1 (;@4;)
                local.get 0
                local.get 5
                i32.store offset=16
              end
              local.get 1
              local.get 5
              call $_RNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12waitable_set4join
              local.get 0
              i32.const 0
              i32.store8 offset=20
              local.get 0
              i32.load8_u offset=12
              local.set 5
              local.get 0
              i32.const 1
              i32.store8 offset=12
              local.get 5
              br_if 0 (;@4;)
              block ;; label = @5
                block ;; label = @6
                  block ;; label = @7
                    block ;; label = @8
                      block ;; label = @9
                        block ;; label = @10
                          block ;; label = @11
                            local.get 0
                            i32.load
                            local.tee 6
                            i32.eqz
                            br_if 0 (;@11;)
                            local.get 0
                            i32.load offset=4
                            local.set 7
                            block ;; label = @12
                              loop ;; label = @13
                                local.get 6
                                i32.const 92
                                i32.add
                                local.set 8
                                local.get 6
                                i32.load16_u offset=138
                                local.tee 9
                                i32.const 2
                                i32.shl
                                local.set 5
                                i32.const -1
                                local.set 10
                                block ;; label = @14
                                  block ;; label = @15
                                    loop ;; label = @16
                                      block ;; label = @17
                                        local.get 5
                                        br_if 0 (;@17;)
                                        local.get 9
                                        local.set 10
                                        br 2 (;@15;)
                                      end
                                      local.get 8
                                      i32.load
                                      local.set 11
                                      local.get 5
                                      i32.const -4
                                      i32.add
                                      local.set 5
                                      local.get 10
                                      i32.const 1
                                      i32.add
                                      local.set 10
                                      local.get 8
                                      i32.const 4
                                      i32.add
                                      local.set 8
                                      local.get 1
                                      local.get 11
                                      i32.gt_u
                                      local.get 1
                                      local.get 11
                                      i32.lt_u
                                      i32.sub
                                      i32.const 255
                                      i32.and
                                      local.tee 11
                                      i32.const 1
                                      i32.eq
                                      br_if 0 (;@16;)
                                    end
                                    local.get 11
                                    i32.eqz
                                    br_if 1 (;@14;)
                                  end
                                  local.get 7
                                  i32.eqz
                                  br_if 2 (;@12;)
                                  local.get 7
                                  i32.const -1
                                  i32.add
                                  local.set 7
                                  local.get 6
                                  local.get 10
                                  i32.const 2
                                  i32.shl
                                  i32.add
                                  i32.load offset=140
                                  local.set 6
                                  br 1 (;@13;)
                                end
                              end
                              local.get 6
                              local.get 10
                              i32.const 3
                              i32.shl
                              i32.add
                              local.tee 8
                              local.get 2
                              i32.store
                              local.get 8
                              i32.load offset=4
                              local.set 5
                              local.get 8
                              local.get 3
                              i32.store offset=4
                              br 7 (;@5;)
                            end
                            block ;; label = @12
                              block ;; label = @13
                                block ;; label = @14
                                  block ;; label = @15
                                    block ;; label = @16
                                      local.get 6
                                      i32.load16_u offset=138
                                      local.tee 5
                                      i32.const 11
                                      i32.lt_u
                                      br_if 0 (;@16;)
                                      i32.const 5
                                      local.set 8
                                      i32.const 4
                                      local.set 5
                                      local.get 10
                                      i32.const 5
                                      i32.lt_u
                                      br_if 1 (;@15;)
                                      local.get 10
                                      local.set 5
                                      i32.const 0
                                      local.set 11
                                      local.get 10
                                      i32.const -5
                                      i32.add
                                      br_table 1 (;@15;) 3 (;@13;) 2 (;@14;)
                                    end
                                    local.get 6
                                    i32.const 92
                                    i32.add
                                    local.tee 7
                                    local.get 10
                                    i32.const 2
                                    i32.shl
                                    i32.add
                                    local.set 8
                                    block ;; label = @16
                                      block ;; label = @17
                                        local.get 10
                                        i32.const 1
                                        i32.add
                                        local.tee 11
                                        local.get 5
                                        i32.le_u
                                        br_if 0 (;@17;)
                                        local.get 8
                                        local.get 1
                                        i32.store
                                        br 1 (;@16;)
                                      end
                                      block ;; label = @17
                                        local.get 5
                                        local.get 10
                                        i32.sub
                                        local.tee 9
                                        i32.const 2
                                        i32.shl
                                        local.tee 12
                                        i32.eqz
                                        br_if 0 (;@17;)
                                        local.get 7
                                        local.get 11
                                        i32.const 2
                                        i32.shl
                                        i32.add
                                        local.get 8
                                        local.get 12
                                        memory.copy
                                      end
                                      local.get 8
                                      local.get 1
                                      i32.store
                                      local.get 9
                                      i32.const 3
                                      i32.shl
                                      local.tee 8
                                      i32.eqz
                                      br_if 0 (;@16;)
                                      local.get 6
                                      local.get 11
                                      i32.const 3
                                      i32.shl
                                      i32.add
                                      local.get 6
                                      local.get 10
                                      i32.const 3
                                      i32.shl
                                      i32.add
                                      local.get 8
                                      memory.copy
                                    end
                                    local.get 6
                                    local.get 10
                                    i32.const 3
                                    i32.shl
                                    i32.add
                                    local.tee 8
                                    local.get 2
                                    i32.store
                                    local.get 8
                                    local.get 3
                                    i32.store offset=4
                                    local.get 6
                                    local.get 5
                                    i32.const 1
                                    i32.add
                                    i32.store16 offset=138
                                    br 9 (;@6;)
                                  end
                                  local.get 4
                                  local.get 5
                                  i32.store offset=16
                                  local.get 4
                                  i32.const 0
                                  i32.store offset=12
                                  local.get 4
                                  local.get 6
                                  i32.store offset=8
                                  local.get 4
                                  i32.const 20
                                  i32.add
                                  local.get 4
                                  i32.const 8
                                  i32.add
                                  call $_RINvMsV_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB6_6HandleINtB6_7NodeRefNtNtB6_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB1n_4LeafENtB1n_2KVE5splitNtNtBc_5alloc6GlobalEB1K_
                                  local.get 4
                                  i32.load offset=20
                                  local.set 5
                                  br 2 (;@12;)
                                end
                                local.get 10
                                i32.const -7
                                i32.add
                                local.set 11
                                i32.const 6
                                local.set 8
                              end
                              local.get 4
                              local.get 8
                              i32.store offset=16
                              local.get 4
                              i32.const 0
                              i32.store offset=12
                              local.get 4
                              local.get 6
                              i32.store offset=8
                              local.get 4
                              i32.const 20
                              i32.add
                              local.get 4
                              i32.const 8
                              i32.add
                              call $_RINvMsV_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB6_6HandleINtB6_7NodeRefNtNtB6_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB1n_4LeafENtB1n_2KVE5splitNtNtBc_5alloc6GlobalEB1K_
                              local.get 4
                              i32.load offset=28
                              local.set 5
                              local.get 11
                              local.set 10
                            end
                            local.get 5
                            i32.const 92
                            i32.add
                            local.tee 6
                            local.get 10
                            i32.const 2
                            i32.shl
                            i32.add
                            local.set 11
                            block ;; label = @12
                              block ;; label = @13
                                local.get 5
                                i32.load16_u offset=138
                                local.tee 8
                                local.get 10
                                i32.gt_u
                                br_if 0 (;@13;)
                                local.get 11
                                local.get 1
                                i32.store
                                br 1 (;@12;)
                              end
                              local.get 10
                              i32.const 1
                              i32.add
                              local.set 7
                              block ;; label = @13
                                local.get 8
                                local.get 10
                                i32.sub
                                local.tee 9
                                i32.const 2
                                i32.shl
                                local.tee 12
                                i32.eqz
                                br_if 0 (;@13;)
                                local.get 6
                                local.get 7
                                i32.const 2
                                i32.shl
                                i32.add
                                local.get 11
                                local.get 12
                                memory.copy
                              end
                              local.get 11
                              local.get 1
                              i32.store
                              local.get 9
                              i32.const 3
                              i32.shl
                              local.tee 11
                              i32.eqz
                              br_if 0 (;@12;)
                              local.get 5
                              local.get 7
                              i32.const 3
                              i32.shl
                              i32.add
                              local.get 5
                              local.get 10
                              i32.const 3
                              i32.shl
                              i32.add
                              local.get 11
                              memory.copy
                            end
                            local.get 5
                            local.get 10
                            i32.const 3
                            i32.shl
                            i32.add
                            local.tee 11
                            local.get 2
                            i32.store
                            local.get 11
                            local.get 3
                            i32.store offset=4
                            local.get 5
                            local.get 8
                            i32.const 1
                            i32.add
                            i32.store16 offset=138
                            local.get 4
                            i32.load offset=20
                            local.tee 8
                            i32.eqz
                            br_if 5 (;@6;)
                            local.get 4
                            i32.load offset=28
                            local.set 3
                            local.get 4
                            i32.load offset=32
                            local.set 5
                            local.get 4
                            i32.load offset=36
                            local.set 6
                            local.get 4
                            i32.load offset=40
                            local.set 7
                            local.get 4
                            i32.load offset=44
                            local.set 9
                            block ;; label = @12
                              local.get 8
                              i32.load offset=88
                              local.tee 11
                              br_if 0 (;@12;)
                              local.get 3
                              local.set 1
                              br 5 (;@7;)
                            end
                            local.get 4
                            i32.load offset=24
                            local.set 10
                            loop ;; label = @12
                              local.get 5
                              local.get 10
                              i32.ne
                              br_if 2 (;@10;)
                              local.get 8
                              i32.load16_u offset=136
                              local.set 5
                              local.get 11
                              i32.load16_u offset=138
                              i32.const 11
                              i32.lt_u
                              br_if 3 (;@9;)
                              local.get 10
                              i32.const 1
                              i32.add
                              local.set 10
                              i32.const 4
                              local.set 8
                              block ;; label = @13
                                block ;; label = @14
                                  block ;; label = @15
                                    block ;; label = @16
                                      local.get 5
                                      i32.const 5
                                      i32.lt_u
                                      br_if 0 (;@16;)
                                      i32.const 0
                                      local.set 2
                                      i32.const 5
                                      local.set 1
                                      local.get 5
                                      local.set 8
                                      local.get 5
                                      i32.const -5
                                      i32.add
                                      br_table 0 (;@16;) 2 (;@14;) 1 (;@15;)
                                    end
                                    local.get 4
                                    local.get 8
                                    i32.store offset=16
                                    local.get 4
                                    local.get 10
                                    i32.store offset=12
                                    local.get 4
                                    local.get 11
                                    i32.store offset=8
                                    local.get 4
                                    i32.const 20
                                    i32.add
                                    local.get 4
                                    i32.const 8
                                    i32.add
                                    call $_RINvMsW_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB6_6HandleINtB6_7NodeRefNtNtB6_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB1n_8InternalENtB1n_2KVE5splitNtNtBc_5alloc6GlobalEB1K_
                                    local.get 4
                                    i32.load offset=28
                                    local.set 1
                                    local.get 4
                                    i32.load offset=20
                                    local.tee 8
                                    local.set 11
                                    br 2 (;@13;)
                                  end
                                  local.get 5
                                  i32.const -7
                                  i32.add
                                  local.set 2
                                  i32.const 6
                                  local.set 1
                                end
                                local.get 4
                                local.get 1
                                i32.store offset=16
                                local.get 4
                                local.get 10
                                i32.store offset=12
                                local.get 4
                                local.get 11
                                i32.store offset=8
                                local.get 4
                                i32.const 20
                                i32.add
                                local.get 4
                                i32.const 8
                                i32.add
                                call $_RINvMsW_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB6_6HandleINtB6_7NodeRefNtNtB6_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB1n_8InternalENtB1n_2KVE5splitNtNtBc_5alloc6GlobalEB1K_
                                local.get 4
                                i32.load offset=20
                                local.set 8
                                local.get 4
                                i32.load offset=28
                                local.tee 1
                                local.set 11
                                local.get 2
                                local.set 5
                              end
                              local.get 11
                              local.get 5
                              local.get 6
                              local.get 7
                              local.get 9
                              local.get 3
                              call $_RNvMsM_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB5_6HandleINtB5_7NodeRefNtNtB5_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB1m_8InternalENtB1m_4EdgeE10insert_fitB1J_
                              local.get 8
                              i32.eqz
                              br_if 6 (;@6;)
                              local.get 4
                              i32.load offset=44
                              local.set 9
                              local.get 4
                              i32.load offset=40
                              local.set 7
                              local.get 4
                              i32.load offset=36
                              local.set 6
                              local.get 4
                              i32.load offset=32
                              local.set 5
                              local.get 4
                              i32.load offset=24
                              local.set 10
                              local.get 1
                              local.set 3
                              local.get 8
                              i32.load offset=88
                              local.tee 11
                              i32.eqz
                              br_if 5 (;@7;)
                              br 0 (;@12;)
                            end
                          end
                          i32.const 140
                          call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCskAuRjb5C0Ki_4p3rt
                          local.tee 5
                          i32.eqz
                          br_if 7 (;@3;)
                          local.get 5
                          i32.const 0
                          i32.store16 offset=138
                          local.get 5
                          i32.const 0
                          i32.store offset=88
                          local.get 0
                          i32.const 0
                          i32.store offset=4
                          local.get 0
                          local.get 5
                          i32.store
                          local.get 5
                          i32.load16_u offset=138
                          local.tee 8
                          i32.const 11
                          i32.ge_u
                          br_if 2 (;@8;)
                          local.get 5
                          local.get 8
                          i32.const 1
                          i32.add
                          i32.store16 offset=138
                          local.get 5
                          local.get 8
                          i32.const 2
                          i32.shl
                          i32.add
                          local.get 1
                          i32.store offset=92
                          local.get 5
                          local.get 8
                          i32.const 3
                          i32.shl
                          i32.add
                          local.tee 5
                          local.get 3
                          i32.store offset=4
                          local.get 5
                          local.get 2
                          i32.store
                          br 4 (;@6;)
                        end
                        i32.const 53
                        call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                        unreachable
                      end
                      local.get 11
                      local.get 5
                      local.get 6
                      local.get 7
                      local.get 9
                      local.get 3
                      call $_RNvMsM_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree4nodeINtB5_6HandleINtB5_7NodeRefNtNtB5_6marker3MutmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableNtB1m_8InternalENtB1m_4EdgeE10insert_fitB1J_
                      br 2 (;@6;)
                    end
                    i32.const 32
                    call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
                    unreachable
                  end
                  local.get 0
                  i32.load
                  local.tee 11
                  i32.eqz
                  br_if 2 (;@4;)
                  local.get 0
                  i32.load offset=4
                  local.set 10
                  i32.const 188
                  call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCskAuRjb5C0Ki_4p3rt
                  local.tee 8
                  i32.eqz
                  br_if 3 (;@3;)
                  local.get 8
                  local.get 11
                  i32.store offset=140
                  local.get 8
                  i32.const 0
                  i32.store16 offset=138
                  local.get 8
                  i32.const 0
                  i32.store offset=88
                  local.get 10
                  i32.const 1
                  i32.add
                  local.tee 3
                  i32.eqz
                  br_if 2 (;@4;)
                  local.get 11
                  i32.const 0
                  i32.store16 offset=136
                  local.get 11
                  local.get 8
                  i32.store offset=88
                  local.get 0
                  local.get 3
                  i32.store offset=4
                  local.get 0
                  local.get 8
                  i32.store
                  local.get 5
                  local.get 10
                  i32.ne
                  br_if 4 (;@2;)
                  local.get 8
                  i32.load16_u offset=138
                  local.tee 5
                  i32.const 11
                  i32.ge_u
                  br_if 5 (;@1;)
                  local.get 8
                  local.get 5
                  i32.const 1
                  i32.add
                  local.tee 11
                  i32.store16 offset=138
                  local.get 8
                  local.get 5
                  i32.const 2
                  i32.shl
                  i32.add
                  local.get 6
                  i32.store offset=92
                  local.get 8
                  local.get 5
                  i32.const 3
                  i32.shl
                  i32.add
                  local.tee 5
                  local.get 9
                  i32.store offset=4
                  local.get 5
                  local.get 7
                  i32.store
                  local.get 8
                  i32.const 140
                  i32.add
                  local.get 11
                  i32.const 2
                  i32.shl
                  i32.add
                  local.get 1
                  i32.store
                  local.get 1
                  local.get 11
                  i32.store16 offset=136
                  local.get 1
                  local.get 8
                  i32.store offset=88
                end
                local.get 0
                local.get 0
                i32.load offset=8
                i32.const 1
                i32.add
                i32.store offset=8
                i32.const 0
                local.set 5
              end
              local.get 0
              i32.const 0
              i32.store8 offset=12
              local.get 4
              i32.const 48
              i32.add
              global.set $__stack_pointer
              local.get 5
              return
            end
            call $_RNvNtCshQUFA83YM6w_4core6option13unwrap_failed
            unreachable
          end
          call $_RNvNtCshQUFA83YM6w_4core9panicking18panic_nounwind_fmt
          unreachable
        end
        i32.const 48
        call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
        unreachable
      end
      i32.const 32
      call $_RNvNtCshQUFA83YM6w_4core9panicking5panic
      unreachable
    )
    (func $_RNvMs1_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB5_15SharedTaskState24cabi_waitable_unregister (;103;) (type 0) (param i32 i32) (result i32)
      (local i32 i32)
      global.get $__stack_pointer
      i32.const 16
      i32.sub
      local.tee 2
      global.set $__stack_pointer
      local.get 1
      i32.const 0
      call $_RNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12waitable_set4join
      local.get 0
      i32.load8_u offset=12
      local.set 3
      local.get 0
      i32.const 1
      i32.store8 offset=12
      block ;; label = @1
        local.get 3
        i32.eqz
        br_if 0 (;@1;)
        call $_RNvNtCshQUFA83YM6w_4core6option13unwrap_failed
        unreachable
      end
      local.get 2
      i32.const 4
      i32.add
      local.get 0
      local.get 1
      call $_RINvMsi_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree3mapINtB6_8BTreeMapmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE12remove_entrymEB1f_
      local.get 2
      i32.load offset=12
      local.set 1
      local.get 2
      i32.load offset=8
      local.set 3
      local.get 0
      i32.const 0
      i32.store8 offset=12
      local.get 2
      i32.const 16
      i32.add
      global.set $__stack_pointer
      local.get 1
      i32.const 0
      local.get 3
      select
    )
    (func $_RNvMs_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB4_9TaskState22deliver_waitable_event (;104;) (type 10) (param i32 i32 i32)
      (local i32 i32)
      global.get $__stack_pointer
      i32.const 16
      i32.sub
      local.tee 3
      global.set $__stack_pointer
      local.get 1
      i32.const 0
      call $_RNvNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12waitable_set4join
      local.get 0
      i32.load8_u offset=20
      local.set 4
      local.get 0
      i32.const 1
      i32.store8 offset=20
      block ;; label = @1
        local.get 4
        br_if 0 (;@1;)
        local.get 3
        i32.const 4
        i32.add
        local.get 0
        i32.const 8
        i32.add
        local.get 1
        call $_RINvMsi_NtNtNtCsiqQVI2xHy0t_5alloc11collections5btree3mapINtB6_8BTreeMapmNtNtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_support12CabiWaitableE12remove_entrymEB1f_
        local.get 3
        i32.load offset=8
        local.tee 1
        i32.eqz
        br_if 0 (;@1;)
        local.get 3
        i32.load offset=12
        local.set 4
        local.get 0
        i32.const 0
        i32.store8 offset=20
        local.get 4
        local.get 2
        local.get 1
        call_indirect (type 3)
        local.get 3
        i32.const 16
        i32.add
        global.set $__stack_pointer
        return
      end
      call $_RNvNtCshQUFA83YM6w_4core6option13unwrap_failed
      unreachable
    )
    (func $_RINvNtCshQUFA83YM6w_4core3ptr9drop_glueINtNtB4_6option6OptionINtNtB4_3pin3PinINtNtCsiqQVI2xHy0t_5alloc5boxed3BoxDNtNtNtB4_6future6future6Futurep6OutputuEL_EEEECscNOpLhlpk4u_11wit_bindgen (;105;) (type 3) (param i32 i32)
      (local i32)
      block ;; label = @1
        local.get 0
        i32.eqz
        br_if 0 (;@1;)
        block ;; label = @2
          local.get 1
          i32.load
          local.tee 2
          i32.eqz
          br_if 0 (;@2;)
          local.get 0
          local.get 2
          call_indirect (type 1)
        end
        local.get 1
        i32.load offset=4
        local.tee 1
        i32.eqz
        br_if 0 (;@1;)
        local.get 0
        i32.const -4
        i32.add
        i32.load
        local.get 1
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13validate_sizeCskAuRjb5C0Ki_4p3rt
        local.get 0
        call $_RNvMs0_NtCs79fo1HNZIej_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCskAuRjb5C0Ki_4p3rt
      end
    )
    (func $_RNvMs1_NtNtCscNOpLhlpk4u_11wit_bindgen2rt13async_supportNtB5_15SharedTaskState10cabi_clone (;106;) (type 2) (param i32) (result i32)
      (local i32)
      local.get 0
      i32.const -8
      i32.add
      local.tee 1
      local.get 1
      i32.load
      local.tee 1
      i32.const 1
      i32.add
      i32.store
      block ;; label = @1
        local.get 1
        i32.const -1
        i32.gt_s
        br_if 0 (;@1;)
        unreachable
      end
      local.get 0
    )
    (func $wasip3_task_set (;107;) (type 2) (param i32) (result i32)
      (local i32 i32)
      global.get $__memory_base
      i32.const 1049304
      i32.add
      local.tee 1
      i32.load
      local.set 2
      local.get 1
      local.get 0
      i32.store
      local.get 2
    )
    (data $.rodata (;0;) (i32.const 1048576) "Hello, WASI 0.3!\0a")
    (data $.data (;1;) (i32.const 1048596) "\04\00\00\00\f4\00\00\00\04\00\00\00\05\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\ff\0f\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\01\00\00\00\02\00\00\00\07\00\00\00\08\00\00\00\09\00\00\00\0a\00\00\00\0b\00\00\00\0c\00\00\00\0d\00\00\00\0e\00\00\00\0f\00\00\00\10\00\00\00\01\00\00\00\01\00\00\00\11\00\00\00\12\00\00\00\13\00\00\00\14\00\00\00\15\00\00\00\16\00\00\00\17\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\01\00\00\00\18\00\00\00\19\00\00\00\1a\00\00\00\1b\00\00\00\1c\00\00\00\19\00\00\00")
    (@producers
      (language "Rust" "")
      (processed-by "rustc" "1.99.1 (58cf8f9c3 2026-10-13)")
      (processed-by "wit-component" "0.259.0")
      (processed-by "wit-bindgen-rust" "0.62.0")
    )
    (@custom "target_features" (after data) "\08+\0bbulk-memory+\0fbulk-memory-opt+\16call-indirect-overlong+\0amultivalue+\0fmutable-globals+\13nontrapping-fptoint+\0freference-types+\08sign-ext")
  )
  (core module $wit-component-shim-module (;1;)
    (type (;0;) (func (param i32 i32) (result i32)))
    (type (;1;) (func (param i32 i32 i32) (result i32)))
    (table (;0;) 5 5 funcref)
    (export "0" (func 0))
    (export "1" (func 1))
    (export "2" (func 2))
    (export "3" (func 3))
    (export "4" (func 4))
    (export "$imports" (table 0))
    (func (;0;) (type 0) (param i32 i32) (result i32)
      local.get 0
      local.get 1
      i32.const 0
      call_indirect (type 0)
    )
    (func (;1;) (type 0) (param i32 i32) (result i32)
      local.get 0
      local.get 1
      i32.const 1
      call_indirect (type 0)
    )
    (func (;2;) (type 0) (param i32 i32) (result i32)
      local.get 0
      local.get 1
      i32.const 2
      call_indirect (type 0)
    )
    (func (;3;) (type 1) (param i32 i32 i32) (result i32)
      local.get 0
      local.get 1
      local.get 2
      i32.const 3
      call_indirect (type 1)
    )
    (func (;4;) (type 1) (param i32 i32 i32) (result i32)
      local.get 0
      local.get 1
      local.get 2
      i32.const 4
      call_indirect (type 1)
    )
    (@producers
      (processed-by "wit-component" "0.254.0")
    )
  )
  (core module $wit-component-fixup (;2;)
    (type (;0;) (func (param i32 i32) (result i32)))
    (type (;1;) (func (param i32 i32 i32) (result i32)))
    (import "" "0" (func (;0;) (type 0) (param i32 i32) (result i32)))
    (import "" "1" (func (;1;) (type 0) (param i32 i32) (result i32)))
    (import "" "2" (func (;2;) (type 0) (param i32 i32) (result i32)))
    (import "" "3" (func (;3;) (type 1) (param i32 i32 i32) (result i32)))
    (import "" "4" (func (;4;) (type 1) (param i32 i32 i32) (result i32)))
    (import "" "$imports" (table (;0;) 5 5 funcref))
    (elem (;0;) (i32.const 0) func 0 1 2 3 4)
    (@producers
      (processed-by "wit-component" "0.254.0")
    )
  )
  (core instance $wit-component-shim-instance (;0;) (instantiate $wit-component-shim-module))
  (core func $"context.get 0" (;0;) (canon context.get i32 0))
  (core func $"context.set 0" (;1;) (canon context.set i32 0))
  (core func $waitable-set.drop (;2;) (canon waitable-set.drop))
  (core func $waitable-set.new (;3;) (canon waitable-set.new))
  (core func $waitable.join (;4;) (canon waitable.join))
  (alias core export $wit-component-shim-instance "0" (core func $waitable-set.poll (;5;)))
  (core instance $$root (;1;)
    (export "[context-get-0]" (func $"context.get 0"))
    (export "[context-set-0]" (func $"context.set 0"))
    (export "[waitable-set-drop]" (func $waitable-set.drop))
    (export "[waitable-set-new]" (func $waitable-set.new))
    (export "[waitable-join]" (func $waitable.join))
    (export "[waitable-set-poll]" (func $waitable-set.poll))
  )
  (core func $task.cancel (;6;) (canon task.cancel))
  (core instance $"[export]$root" (;2;)
    (export "[task-cancel]" (func $task.cancel))
  )
  (type (;5;) (stream u8))
  (core func $stream.new (;7;) (canon stream.new 5))
  (alias core export $wit-component-shim-instance "1" (core func $"wasi:cli/stdin@0.3.0-[future-write-1]read-via-stream" (;8;)))
  (alias core export $wit-component-shim-instance "2" (core func $"wasi:cli/stdin@0.3.0-[future-read-1]read-via-stream" (;9;)))
  (alias export $wasi:cli/stdin@0.3.0 "error-code" (type $"#type6 error-code" (@name "error-code") (;6;)))
  (type (;7;) (result (error $"#type6 error-code")))
  (type (;8;) (future 7))
  (core func $future.cancel-write (;10;) (canon future.cancel-write 8))
  (core func $future.cancel-read (;11;) (canon future.cancel-read 8))
  (core func $future.drop-writable (;12;) (canon future.drop-writable 8))
  (core func $future.drop-readable (;13;) (canon future.drop-readable 8))
  (core func $future.new (;14;) (canon future.new 8))
  (alias core export $wit-component-shim-instance "3" (core func $"wasi:cli/stdin@0.3.0-[stream-write-0]read-via-stream" (;15;)))
  (alias core export $wit-component-shim-instance "4" (core func $"wasi:cli/stdin@0.3.0-[stream-read-0]read-via-stream" (;16;)))
  (core func $stream.cancel-write (;17;) (canon stream.cancel-write 5))
  (core func $stream.cancel-read (;18;) (canon stream.cancel-read 5))
  (core func $stream.drop-writable (;19;) (canon stream.drop-writable 5))
  (core func $stream.drop-readable (;20;) (canon stream.drop-readable 5))
  (core instance $wasi:cli/stdin@0.3.0 (;3;)
    (export "[stream-new-0]read-via-stream" (func $stream.new))
    (export "[async-lower][future-write-1]read-via-stream" (func $"wasi:cli/stdin@0.3.0-[future-write-1]read-via-stream"))
    (export "[async-lower][future-read-1]read-via-stream" (func $"wasi:cli/stdin@0.3.0-[future-read-1]read-via-stream"))
    (export "[future-cancel-write-1]read-via-stream" (func $future.cancel-write))
    (export "[future-cancel-read-1]read-via-stream" (func $future.cancel-read))
    (export "[future-drop-writable-1]read-via-stream" (func $future.drop-writable))
    (export "[future-drop-readable-1]read-via-stream" (func $future.drop-readable))
    (export "[future-new-1]read-via-stream" (func $future.new))
    (export "[async-lower][stream-write-0]read-via-stream" (func $"wasi:cli/stdin@0.3.0-[stream-write-0]read-via-stream"))
    (export "[async-lower][stream-read-0]read-via-stream" (func $"wasi:cli/stdin@0.3.0-[stream-read-0]read-via-stream"))
    (export "[stream-cancel-write-0]read-via-stream" (func $stream.cancel-write))
    (export "[stream-cancel-read-0]read-via-stream" (func $stream.cancel-read))
    (export "[stream-drop-writable-0]read-via-stream" (func $stream.drop-writable))
    (export "[stream-drop-readable-0]read-via-stream" (func $stream.drop-readable))
  )
  (alias export $wasi:cli/stdout@0.3.0 "write-via-stream" (func $write-via-stream (;0;)))
  (core func $write-via-stream (;21;) (canon lower (func $write-via-stream)))
  (core instance $wasi:cli/stdout@0.3.0 (;4;)
    (export "write-via-stream" (func $write-via-stream))
  )
  (type (;9;) (result))
  (core func $task.return (;22;) (canon task.return (result 9)))
  (core instance $"[export]wasi:cli/run@0.3.0" (;5;)
    (export "[task-return]run" (func $task.return))
  )
  (core instance $main (;6;) (instantiate $main
      (with "$root" (instance $$root))
      (with "[export]$root" (instance $"[export]$root"))
      (with "wasi:cli/stdin@0.3.0" (instance $wasi:cli/stdin@0.3.0))
      (with "wasi:cli/stdout@0.3.0" (instance $wasi:cli/stdout@0.3.0))
      (with "[export]wasi:cli/run@0.3.0" (instance $"[export]wasi:cli/run@0.3.0"))
    )
  )
  (alias core export $main "memory" (core memory $memory (;0;)))
  (alias core export $wit-component-shim-instance "$imports" (core table $"shim table" (;0;)))
  (core func $"#core-func23 waitable-set.poll" (@name "waitable-set.poll") (;23;) (canon waitable-set.poll (memory $memory)))
  (alias core export $main "cabi_realloc" (core func $realloc (;24;)))
  (core func $future.write (;25;) (canon future.write 8 (memory $memory) async))
  (core func $future.read (;26;) (canon future.read 8 (memory $memory) async))
  (core func $stream.write (;27;) (canon stream.write 5 (memory $memory) async))
  (core func $stream.read (;28;) (canon stream.read 5 (memory $memory) async))
  (core instance $fixup-args (;7;)
    (export "$imports" (table $"shim table"))
    (export "0" (func $"#core-func23 waitable-set.poll"))
    (export "1" (func $future.write))
    (export "2" (func $future.read))
    (export "3" (func $stream.write))
    (export "4" (func $stream.read))
  )
  (core instance $fixup (;8;) (instantiate $wit-component-fixup
      (with "" (instance $fixup-args))
    )
  )
  (type (;10;) (func async (result 9)))
  (alias core export $main "[async-lift]wasi:cli/run@0.3.0#run" (core func $"[async-lift]wasi:cli/run@0.3.0#run" (;29;)))
  (alias core export $main "[callback][async-lift]wasi:cli/run@0.3.0#run" (core func $"[callback][async-lift]wasi:cli/run@0.3.0#run" (;30;)))
  (func $run (;1;) (type 10) (canon lift (core func $"[async-lift]wasi:cli/run@0.3.0#run") async (callback $"[callback][async-lift]wasi:cli/run@0.3.0#run")))
  (component $wasi:cli/run@0.3.0-shim-component (;0;)
    (type (;0;) (result))
    (type (;1;) (func async (result 0)))
    (import "import-func-run" (func (;0;) (type 1)))
    (type (;2;) (result))
    (type (;3;) (func async (result 2)))
    (export (;1;) "run" (func 0) (func (type 3)))
  )
  (instance $wasi:cli/run@0.3.0-shim-instance (;3;) (instantiate $wasi:cli/run@0.3.0-shim-component
      (with "import-func-run" (func $run))
    )
  )
  (export $wasi:cli/run@0.3.0 (;4;) "wasi:cli/run@0.3.0" (instance $wasi:cli/run@0.3.0-shim-instance))
  (@producers
    (processed-by "wit-component" "0.254.0")
  )
)
