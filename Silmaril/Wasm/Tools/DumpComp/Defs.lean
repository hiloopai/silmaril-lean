module

public import Silmaril.Wasm.Tools.DumpFlat.Defs

/-!
# `wasm-tools dump`: wasmparser's component readers, transcribed

The items of the component sections, read as wasmparser 0.262 reads them
(`wasmparser/src/readers/component/*.rs`, all features enabled) and printed in their derived
`Debug` forms, which `dump` prints: core instances (`Instance`), core types (`CoreType`, with
`RecGroup`'s `Debug` and its offsets), component instances, aliases, types (defined, function,
component, instance and resource types), canonical functions with their options, the start
function, imports and exports with `ComponentExternName`.

Each reader returns the `Debug` text and, where `dump` numbers the item, its index-space name.
Not verified (a transcription, tested against the pinned upstream binary).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.DumpComp

open Silmaril.Wasm.Tools.DumpFlat

/-- The `Debug` of `Option<&str>`. -/
def optStr : Option String → String
  | none => "None"
  | some s => s!"Some({RustDebug.debugStr s})"

/-- `ComponentExternName`, read. -/
def externNameR : R String := do
  let o ← get
  let opts ← match ← u8 with
    | 0 | 1 => pure false
    | 2 => pure true
    | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for component name" o
  let name ← str
  let mut impl : Option String := none
  let mut ver : Option String := none
  let mut ext : Option String := none
  if opts then
    let n ← varU32
    for _ in [0:n] do
      let p ← get
      match ← u8 with
      | 0 => do
        let s ← str
        if impl.isSome then bailAt "duplicate 'implements' option in name" p
        impl := some s
      | 1 => do
        let s ← str
        if ver.isSome then bailAt "duplicate 'version-suffix' option in name" p
        ver := some s
      | 2 => do
        let s ← str
        if ext.isSome then bailAt "duplicate 'external-id' option in name" p
        ext := some s
      | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for name option" p
  pure s!"ComponentExternName \{ name: {RustDebug.debugStr name}, implements: {optStr impl}, version_suffix: {optStr ver}, external_id: {optStr ext} }"

/-- `ComponentExternalKind`, read (`from_bytes`). -/
def externalKindR : R String := do
  let o ← get
  let b1 ← u8
  match b1 with
  | 0 => do
    match ← u8 with
    | 0x11 => pure "Module"
    | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for component external kind" (o + 1)
  | 1 => pure "Func" | 2 => pure "Value" | 3 => pure "Type" | 4 => pure "Component"
  | 5 => pure "Instance"
  | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for component external kind" o

def primName : Nat → Option String
  | 0x7f => some "Bool" | 0x7e => some "S8" | 0x7d => some "U8" | 0x7c => some "S16"
  | 0x7b => some "U16" | 0x7a => some "S32" | 0x79 => some "U32" | 0x78 => some "S64"
  | 0x77 => some "U64" | 0x76 => some "F32" | 0x75 => some "F64" | 0x74 => some "Char"
  | 0x73 => some "String" | 0x64 => some "ErrorContext"
  | _ => none

/-- `ComponentValType`, read. -/
def valTypeR : R String := do
  let o ← get
  let b ← peek
  match primName b with
  | some n => do let _ ← u8; pure s!"Primitive({n})"
  | none =>
    let x ← varS33
    if 0 ≤ x ∧ x < 2 ^ 32 then pure s!"Type({x.toNat})"
    else bailAt s!"invalid leading byte (0x{RustDebug.hexDigits b}) for component value type" o

/-- `Option<ComponentValType>`, read. -/
def optValTypeR : R String := do
  let o ← get
  match ← u8 with
  | 0 => pure "None"
  | 1 => do pure s!"Some({← valTypeR})"
  | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for optional component value type" o

/-- `ComponentTypeRef`, read. -/
def typeRefR : R String := do
  let k ← externalKindR
  match k with
  | "Module" => do pure s!"Module({← varU32})"
  | "Func" => do pure s!"Func({← varU32})"
  | "Value" => do pure s!"Value({← valTypeR})"
  | "Type" => do
    let o ← get
    match ← u8 with
    | 0 => do pure s!"Type(Eq({← varU32}))"
    | 1 => pure "Type(SubResource)"
    | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for type bound" o
  | "Instance" => do pure s!"Instance({← varU32})"
  | _ => do pure s!"Component({← varU32})"

/-- `ComponentImport`, read: its `Debug` and the index-space name `dump` gives it. -/
def importR : R (String × String) := do
  let n ← externNameR
  let p ← get
  let ty ← typeRefR
  -- the space comes from the kind byte(s)
  let e ← read
  let desc := match e.b[p]!.toNat with
    | 0 => "module" | 1 => "func" | 2 => "value" | 3 => "type" | 4 => "component"
    | _ => "instance"
  pure (s!"ComponentImport \{ name: {n}, ty: {ty} }", desc)

/-- `ComponentAlias`, read: its `Debug` and the index-space name `dump` gives it. -/
def aliasR : R (String × String) := do
  let o ← get
  let b1 ← u8
  let b2 ← if b1 == 0 then do pure (some (← u8)) else pure none
  match ← u8 with
  | 0 => do
    set o
    let k ← externalKindR
    let _ ← u8
    let i ← varU32
    let n ← str
    let space := match k with
      | "Module" => "module" | "Func" => "func" | "Value" => "value" | "Type" => "type"
      | "Instance" => "instance" | _ => "component"
    pure (s!"InstanceExport \{ kind: {k}, instance_index: {i}, name: {RustDebug.debugStr n} }", space)
  | 1 => do
    let kb ← match b2 with
      | some k => pure k
      | none => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits b1}) for core instance export kind" o
    let (k, space) ← match kb with
      | 0 => pure ("Func", "core func") | 1 => pure ("Table", "core table")
      | 2 => pure ("Memory", "core memory") | 3 => pure ("Global", "core global")
      | 4 => pure ("Tag", "core tag")
      | 0x20 => bailAt "exact type is not allowed in core export aliases" o
      | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for external kind" o
    let i ← varU32
    let n ← str
    pure (s!"CoreInstanceExport \{ kind: {k}, instance_index: {i}, name: {RustDebug.debugStr n} }", space)
  | 2 => do
    let (k, space) ← match b1, b2 with
      | 0, some 0x10 => pure ("CoreType", "core type")
      | 0, some 0x11 => pure ("CoreModule", "module")
      | 0, some x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for component outer alias kind" (o + 1)
      | 3, _ => pure ("Type", "type")
      | 4, _ => pure ("Component", "component")
      | x, _ => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for component outer alias kind" o
    let c ← varU32
    let i ← varU32
    pure (s!"Outer \{ kind: {k}, count: {c}, index: {i} }", space)
  | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for alias" ((← get) - 1)

/-- `RecGroup`'s `Debug`, read (with the offsets of its sub types). -/
def recGroupR : R String := do
  let p ← get
  if (← peek) == 0x4E then
    let _ ← u8
    let n ← size 1000000 "rec group types"
    let mut acc : Array String := #[]
    for _ in [0:n] do
      let o ← get
      acc := acc.push s!"({o}, {(← subTypeR2).2})"
    pure ("RecGroup { inner: Explicit([" ++ ", ".intercalate acc.toList ++ "]) }")
  else
    pure s!"RecGroup \{ inner: Implicit(({p}, {(← subTypeR2).2})) }"

/-- `TypeRef`'s `Debug` (of a core module type's imports and exports), read. -/
def coreTypeRefR : R String := do pure (← DumpFlat.typeRefR).2

/-- `CoreType`, read. -/
def coreTypeR : R String := do
  match ← peek with
  | 0x00 => do
    let _ ← u8
    let x ← peek
    unless x == 0x50 do
      bail s!"invalid leading byte (0x{RustDebug.hexDigits x}) for non-final sub type"
    pure s!"Rec({← recGroupR})"
  | 0x50 => do
    let _ ← u8
    let n ← size 1000000 "module type declaration"
    let mut acc : Array String := #[]
    for _ in [0:n] do
      let o ← get
      let d ← match ← u8 with
        | 0 => do
          let m ← str; let nm ← str; let ty ← coreTypeRefR
          pure s!"Import(Import \{ module: {RustDebug.debugStr m}, name: {RustDebug.debugStr nm}, ty: {ty} })"
        | 1 => do pure s!"Type({← recGroupR})"
        | 2 => do
          let q ← get
          unless (← u8) == 0x10 do bailAt "invalid leading byte for outer alias kind" q
          let q ← get
          unless (← u8) == 0x01 do bailAt "invalid leading byte for outer alias target" q
          let c ← varU32; let i ← varU32
          pure s!"OuterAlias \{ kind: Type, count: {c}, index: {i} }"
        | 3 => do
          let nm ← str; let ty ← coreTypeRefR
          pure s!"Export \{ name: {RustDebug.debugStr nm}, ty: {ty} }"
        | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for type definition" o
      acc := acc.push d
    pure ("Module([" ++ ", ".intercalate acc.toList ++ "])")
  | _ => do pure s!"Rec({← recGroupR})"

/-- A list of `f`, its count read first. -/
def listR (desc : String) (f : R String) : R String := do
  let n ← size 1000000 desc
  let mut acc : Array String := #[]
  for _ in [0:n] do acc := acc.push (← f)
  pure ("[" ++ ", ".intercalate acc.toList ++ "]")

/-- The result list of a function type (`read_resultlist`). -/
def resultListR : R String := do
  let o ← get
  match ← u8 with
  | 0 => do pure s!"Some({← valTypeR})"
  | 1 => do
    let q ← get
    match ← u8 with
    | 0 => pure "None"
    | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for number of results" q
  | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for component function results" o

/-- `ComponentDefinedType`, read after its first byte `b`. -/
def definedR (b : Nat) : R String := do
  match b with
  | 0x72 => do
    pure ("Record(" ++ (← listR "record field" (do
      let n ← str; pure s!"({RustDebug.debugStr n}, {← valTypeR})")) ++ ")")
  | 0x71 => do
    pure ("Variant(" ++ (← listR "variant cases" (do
      let n ← str; let t ← optValTypeR
      let q ← get
      unless (← u8) == 0 do bailAt "invalid leading byte for zero byte required" q
      pure s!"VariantCase \{ name: {RustDebug.debugStr n}, ty: {t} }")) ++ ")")
  | 0x70 => do pure s!"List({← valTypeR})"
  | 0x63 => do let a ← valTypeR; let c ← valTypeR; pure s!"Map({a}, {c})"
  | 0x6f => do pure ("Tuple(" ++ (← listR "tuple types" valTypeR) ++ ")")
  | 0x6e => do
    pure ("Flags(" ++ (← listR "flag names" (do pure (RustDebug.debugStr (← str)))) ++ ")")
  | 0x6d => do
    pure ("Enum(" ++ (← listR "enum cases" (do pure (RustDebug.debugStr (← str)))) ++ ")")
  | 0x6b => do pure s!"Option({← valTypeR})"
  | 0x6a => do let ok ← optValTypeR; let err ← optValTypeR; pure s!"Result \{ ok: {ok}, err: {err} }"
  | 0x69 => do pure s!"Own({← varU32})"
  | 0x68 => do pure s!"Borrow({← varU32})"
  | 0x67 => do let t ← valTypeR; let n ← varU32; pure s!"FixedLengthList({t}, {n})"
  | 0x66 => do pure s!"Stream({← optValTypeR})"
  | 0x65 => do pure s!"Future({← optValTypeR})"
  | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for component defined type" ((← get) - 1)

mutual
/-- `ComponentType`, read (nesting `depth`, at most 100 as wasmparser). -/
def compTypeR (fuel : Nat) : R String := do
  match fuel with
  | 0 => bail "component type nesting is too deep"
  | fuel + 1 =>
    let o ← get
    match ← u8 with
    | 0x3f => do
      let rep ← valR
      let q ← get
      let dtor ← match ← u8 with
        | 0 => pure "None"
        | 1 => do pure s!"Some({← varU32})"
        | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for resource destructor" q
      pure s!"Resource \{ rep: {rep.dbg}, dtor: {dtor} }"
    | 0x40 | 0x43 => do
      let async_ := (← read).b[o]!.toNat == 0x43
      let ps ← listR "component function parameters" (do
        let n ← str; pure s!"({RustDebug.debugStr n}, {← valTypeR})")
      let r ← resultListR
      pure s!"Func(ComponentFuncType \{ async_: {async_}, params: {ps}, result: {r} })"
    | 0x41 => do
      let n ← size 1000000 "component type declaration"
      let mut acc : Array String := #[]
      for _ in [0:n] do
        if (← peek) == 0x03 then
          let _ ← u8
          let (i, _) ← importR
          acc := acc.push s!"Import({i})"
        else acc := acc.push (← instDeclR fuel)
      pure ("Component([" ++ ", ".intercalate acc.toList ++ "])")
    | 0x42 => do
      let n ← size 1000000 "instance type declaration"
      let mut acc : Array String := #[]
      for _ in [0:n] do acc := acc.push (← instDeclR fuel)
      pure ("Instance([" ++ ", ".intercalate acc.toList ++ "])")
    | x =>
      match primName x with
      | some n => pure s!"Defined(Primitive({n}))"
      | none => do pure s!"Defined({← definedR x})"
/-- `InstanceTypeDeclaration`, read. -/
def instDeclR (fuel : Nat) : R String := do
  match fuel with
  | 0 => bail "component type nesting is too deep"
  | fuel + 1 =>
    let o ← get
    match ← u8 with
    | 0 => do pure s!"CoreType({← coreTypeR})"
    | 1 => do pure s!"Type({← compTypeR fuel})"
    | 2 => do pure s!"Alias({(← aliasR).1})"
    | 4 => do
      let n ← externNameR; let ty ← typeRefR
      pure s!"Export \{ name: {n}, ty: {ty} }"
    | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for component or instance type declaration" o
end

/-- `ComponentType` from the top of a type section. -/
def componentTypeR : R String := compTypeR 202

/-- `Instance` (a core instance), read. -/
def coreInstanceR : R String := do
  let o ← get
  match ← u8 with
  | 0 => do
    let m ← varU32
    let args ← listR "core instantiation arguments" (do
      let n ← str
      let q ← get
      unless (← u8) == 0x12 do bailAt "invalid leading byte for instantiation arg kind" q
      let i ← varU32
      pure s!"InstantiationArg \{ name: {RustDebug.debugStr n}, kind: Instance, index: {i} }")
    pure s!"Instantiate \{ module_index: {m}, args: {args} }"
  | 1 => do
    let es ← listR "core instantiation arguments" (do
      let n ← str; let k ← exportKindR; let i ← varU32
      pure s!"Export \{ name: {RustDebug.debugStr n}, kind: {k}, index: {i} }")
    pure s!"FromExports({es})"
  | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for core instance" o

/-- `ComponentInstance`, read. -/
def instanceR : R String := do
  let o ← get
  match ← u8 with
  | 0 => do
    let c ← varU32
    let args ← listR "instantiation arguments" (do
      let n ← str; let k ← externalKindR; let i ← varU32
      pure s!"ComponentInstantiationArg \{ name: {RustDebug.debugStr n}, kind: {k}, index: {i} }")
    pure s!"Instantiate \{ component_index: {c}, args: {args} }"
  | 1 => do
    let es ← listR "instantiation exports" (do
      let n ← externNameR; let k ← externalKindR; let i ← varU32
      pure s!"ComponentExport \{ name: {n}, kind: {k}, index: {i}, ty: None }")
    pure s!"FromExports({es})"
  | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for instance" o

/-- `ComponentExport`, read. -/
def exportR : R String := do
  let n ← externNameR
  let k ← externalKindR
  let i ← varU32
  let q ← get
  let ty ← match ← u8 with
    | 0 => pure "None"
    | 1 => do pure s!"Some({← typeRefR})"
    | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for optional component export type" q
  pure s!"ComponentExport \{ name: {n}, kind: {k}, index: {i}, ty: {ty} }"

/-- `CanonicalOption`, read. -/
def canonOptR : R String := do
  let o ← get
  match ← u8 with
  | 0 => pure "UTF8" | 1 => pure "UTF16" | 2 => pure "CompactUTF16"
  | 3 => do pure s!"Memory({← varU32})"
  | 4 => do pure s!"Realloc({← varU32})"
  | 5 => do pure s!"PostReturn({← varU32})"
  | 6 => pure "Async"
  | 7 => do pure s!"Callback({← varU32})"
  | 8 => do pure s!"CoreType({← varU32})"
  | 9 => pure "Gc"
  | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for canonical option" o

def optsR : R String := listR "canonical options" canonOptR

def boolR : R Bool := do
  let o ← get
  match ← u8 with
  | 0 => pure false
  | 1 => pure true
  | _ => bailAt "invalid boolean value" o

/-- `read_legacy_cancellation_byte`. -/
def zeroByteR : R Unit := do
  let o ← get
  match ← u8 with
  | 0 => pure ()
  | 1 => bailAt "invalid leading byte (0x1) for zero byte; this was historically accepted as `cancellable` until WebAssembly/component-model#716" o
  | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for zero byte" o

/-- `CanonicalFunction`, read: its `Debug`, and whether `dump` counts it as a component
function (`Lift`) rather than a core function. -/
def canonR : R (String × Bool) := do
  let o ← get
  let ty (nm : String) : R String := do pure s!"{nm} \{ ty: {← varU32} }"
  let tyOpts (nm : String) : R String := do
    let t ← varU32; let os ← optsR; pure s!"{nm} \{ ty: {t}, options: {os} }"
  let tyAsync (nm : String) : R String := do
    let t ← varU32; let a ← boolR; pure s!"{nm} \{ ty: {t}, async_: {a} }"
  match ← u8 with
  | 0x00 => do
    let q ← get
    unless (← u8) == 0 do bailAt "invalid leading byte for canonical function lift" q
    let f ← varU32; let os ← optsR; let t ← varU32
    pure (s!"Lift \{ core_func_index: {f}, type_index: {t}, options: {os} }", true)
  | 0x01 => do
    let q ← get
    unless (← u8) == 0 do bailAt "invalid leading byte for canonical function lower" q
    let f ← varU32; let os ← optsR
    pure (s!"Lower \{ func_index: {f}, options: {os} }", false)
  | 0x02 => do pure (s!"ResourceNew \{ resource: {← varU32} }", false)
  | 0x03 => do pure (s!"ResourceDrop \{ resource: {← varU32} }", false)
  | 0x04 => do pure (s!"ResourceRep \{ resource: {← varU32} }", false)
  | 0x24 => pure ("BackpressureInc", false)
  | 0x25 => pure ("BackpressureDec", false)
  | 0x09 => do
    let r ← resultListR; let os ← optsR
    pure (s!"TaskReturn \{ result: {r}, options: {os} }", false)
  | 0x05 => pure ("TaskCancel", false)
  | 0x0a => do let t ← valR; let s ← varU32; pure (s!"ContextGet \{ ty: {t.dbg}, slot: {s} }", false)
  | 0x0b => do let t ← valR; let s ← varU32; pure (s!"ContextSet \{ ty: {t.dbg}, slot: {s} }", false)
  | 0x06 => do pure (s!"SubtaskCancel \{ async_: {← boolR} }", false)
  | 0x0d => pure ("SubtaskDrop", false)
  | 0x0e => do pure (← ty "StreamNew", false)
  | 0x0f => do pure (← tyOpts "StreamRead", false)
  | 0x10 => do pure (← tyOpts "StreamWrite", false)
  | 0x2e => do pure (← ty "StreamForward", false)
  | 0x11 => do pure (← tyAsync "StreamCancelRead", false)
  | 0x12 => do pure (← tyAsync "StreamCancelWrite", false)
  | 0x13 => do pure (← ty "StreamDropReadable", false)
  | 0x14 => do pure (← ty "StreamDropWritable", false)
  | 0x15 => do pure (← ty "FutureNew", false)
  | 0x16 => do pure (← tyOpts "FutureRead", false)
  | 0x17 => do pure (← tyOpts "FutureWrite", false)
  | 0x2f => do pure (← ty "FutureForward", false)
  | 0x18 => do pure (← tyAsync "FutureCancelRead", false)
  | 0x19 => do pure (← tyAsync "FutureCancelWrite", false)
  | 0x1a => do pure (← ty "FutureDropReadable", false)
  | 0x1b => do pure (← ty "FutureDropWritable", false)
  | 0x1c => do pure (s!"ErrorContextNew \{ options: {← optsR} }", false)
  | 0x1d => do pure (s!"ErrorContextDebugMessage \{ options: {← optsR} }", false)
  | 0x1e => pure ("ErrorContextDrop", false)
  | 0x1f => pure ("WaitableSetNew", false)
  | 0x20 => do zeroByteR; pure (s!"WaitableSetWait \{ memory: {← varU32} }", false)
  | 0x21 => do zeroByteR; pure (s!"WaitableSetPoll \{ memory: {← varU32} }", false)
  | 0x22 => pure ("WaitableSetDrop", false)
  | 0x23 => pure ("WaitableJoin", false)
  | 0x26 => pure ("ThreadIndex", false)
  | 0x27 => do
    let f ← varU32; let t ← varU32
    pure (s!"ThreadNewIndirect \{ func_ty_index: {f}, table_index: {t} }", false)
  | 0x28 => pure ("ThreadResumeLater", false)
  | 0x29 => do zeroByteR; pure ("ThreadSuspend", false)
  | 0x0c => do zeroByteR; pure ("ThreadYield", false)
  | 0x2a => do zeroByteR; pure ("ThreadSuspendThenResume", false)
  | 0x2b => do zeroByteR; pure ("ThreadYieldThenResume", false)
  | 0x2c => do zeroByteR; pure ("ThreadSuspendThenPromote", false)
  | 0x2d => do zeroByteR; pure ("ThreadYieldThenPromote", false)
  | 0x40 => do pure (s!"ThreadSpawnRef \{ func_ty_index: {← varU32} }", false)
  | 0x41 => do
    let f ← varU32; let t ← varU32
    pure (s!"ThreadSpawnIndirect \{ func_ty_index: {f}, table_index: {t} }", false)
  | 0x42 => pure ("ThreadAvailableParallelism", false)
  | x => bailAt s!"invalid leading byte (0x{RustDebug.hexDigits x}) for canonical function" o

/-- `ComponentStartFunction`, read. -/
def startR : R String := do
  let f ← varU32
  let args ← listR "start function arguments" (do pure (toString (← varU32)))
  let r ← size 1000 "start function results"
  pure s!"ComponentStartFunction \{ func_index: {f}, arguments: {args}, results: {r} }"

/-- The index space `dump` counts a component type in. -/
def typeKindDesc : String := "type"

end Silmaril.Wasm.Tools.DumpComp
