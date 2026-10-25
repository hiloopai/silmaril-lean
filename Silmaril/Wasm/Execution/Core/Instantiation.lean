module

public import Silmaril.Wasm.Execution.Core.Step

@[expose] public section

/-! # Allocation, instantiation and invocation (§4.4)

Allocation functions (`$alloctypes`, `$alloctag(s)`, `$allocglobal(s)`,
`$allocmem(s)`, `$alloctable(s)`, `$allocfunc(s)`, `$allocdata(s)`,
`$allocelem(s)`, `$allocexport(s)`, `$allocmodule`) and the segment programs
(`$rundata_`, `$runelem_`) are real definitions. Initializer evaluation
(`$evalglobals`, `$evalexprs`, `$evalexprss`) runs the machine, so it is a
relation over `Steps`; `Instantiate` collects the premises of `$instantiate`.
`invoke` is `$invoke`.

As in the spec, `$rundata_`/`$runelem_` use `I32` offsets for the
`memory.init`/`table.init` they emit, even for 64-bit memories and tables.

Deviation (documented in Silmaril.Wasm.Execution.Core.Instantiation): `$instantiate` passes the raw module
global types to `$evalglobals`, which stores them in the temporary global instances it
allocates. `Instantiate.run` passes them closed
(`$subst_all_globaltype(gt, $alloctypes(type*))`, the types `$allocmodule` uses), so the
store stays closed as `StoreOk` requires. Only the TYPE field of those unreachable
temporary instances differs; execution is unchanged.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- `$alloctypes(type*)`: roll each group at its index and close it. -/
def allocTypes (rts : List RecType) : List DefType :=
  rts.foldl (fun acc rt => acc ++ (rolldt acc.length (liftRec rt)).map (·.substAll (acc.map .dt))) []

/-- The fold of `$alloctypes` from an arbitrary prefix of closed types. -/
theorem allocTypes_foldl_eq {C : Context} {rts : List RecType} {dts : List DefType}
    (h : TypesOk C rts dts) :
    rts.foldl (fun acc rt => acc ++ (rolldt acc.length (liftRec rt)).map (·.substAll (acc.map .dt)))
      C.types = C.types ++ dts := by
  induction h with
  | nil => simp
  | @cons C rt rts dts _ _ ih =>
    simp only [List.foldl_cons]
    rw [show C.types ++ (rolldt C.types.length (liftRec rt)).map (·.substAll (C.types.map .dt))
      = C.types ++ C.rollGroup rt from rfl]
    rw [ih]; simp

/-- `$alloctypes` agrees with module validation's closed types. -/
theorem allocTypes_eq {rts : List RecType} {dts : List DefType} (h : TypesOk {} rts dts) :
    allocTypes rts = dts := by
  simpa [allocTypes] using allocTypes_foldl_eq h

def allocTag (s : Store H) (d : DefType) : Store H × Nat :=
  ({ s with tags := s.tags ++ [⟨d⟩] }, s.tags.length)

def allocGlobal (s : Store H) (g : CGlobalType) (v : Val) : Store H × Nat :=
  ({ s with globals := s.globals ++ [⟨g, v⟩] }, s.globals.length)

def allocMem (s : Store H) (m : MemoryType) : Store H × Nat :=
  ({ s with mems := s.mems ++ [⟨m, ByteArray.mk (Array.replicate (m.limits.min.val * Memory.pageSize) 0)⟩] },
    s.mems.length)

def allocTable (s : Store H) (t : CTableType) (r : Ref) : Store H × Nat :=
  ({ s with tables := s.tables ++ [⟨t, List.replicate t.limits.min.val r⟩] }, s.tables.length)

def allocFunc (s : Store H) (d : DefType) (code : FuncCode H) (m : ModuleInst) : Store H × Nat :=
  ({ s with funcs := s.funcs ++ [⟨d, m, code⟩] }, s.funcs.length)

def allocData (s : Store H) (bytes : ByteArray) : Store H × Nat :=
  ({ s with datas := s.datas ++ [⟨bytes⟩] }, s.datas.length)

def allocElem (s : Store H) (rt : CRefType) (refs : List Ref) : Store H × Nat :=
  ({ s with elems := s.elems ++ [⟨rt, refs⟩] }, s.elems.length)

/-- Allocate a list, threading the store (`$alloc*s`). -/
def allocMany {α : Type} (alloc : Store H → α → Store H × Nat) : Store H → List α → Store H × List Nat
  | s, [] => (s, [])
  | s, x :: xs =>
    let (s₁, a) := alloc s x
    let (s₂, as) := allocMany alloc s₁ xs
    (s₂, a :: as)

/-- `$tagsxa` & co. -/
def ExternAddr.tags : List ExternAddr → List Nat
  | [] => [] | .tag a :: xs => a :: tags xs | _ :: xs => tags xs
def ExternAddr.globals : List ExternAddr → List Nat
  | [] => [] | .global a :: xs => a :: globals xs | _ :: xs => globals xs
def ExternAddr.mems : List ExternAddr → List Nat
  | [] => [] | .mem a :: xs => a :: mems xs | _ :: xs => mems xs
def ExternAddr.tables : List ExternAddr → List Nat
  | [] => [] | .table a :: xs => a :: tables xs | _ :: xs => tables xs
def ExternAddr.funcs : List ExternAddr → List Nat
  | [] => [] | .func a :: xs => a :: funcs xs | _ :: xs => funcs xs

/-- `$allocexport(moduleinst, export)`; `none` for an out-of-range index. -/
def allocExport? (mi : ModuleInst) (e : Export) : Option ExportInst :=
  (match e.index with
    | .tag x => mi.tags[x.toNat]?.map ExternAddr.tag
    | .global x => mi.globals[x.toNat]?.map ExternAddr.global
    | .memory x => mi.mems[x.toNat]?.map ExternAddr.mem
    | .table x => mi.tables[x.toNat]?.map ExternAddr.table
    | .func x => mi.funcs[x.toNat]?.map ExternAddr.func).map (⟨e.name, ·⟩)

/-- `$allocmodule(s, module, externaddr*, val_G*, ref_T*, (ref_E*)*)`. Out-of-range
type or export indices (impossible for valid modules) make it `none`. -/
def allocModule? (s : Store H) (m : Module) (xas : List ExternAddr) (valsG : List Val)
    (refsT : List Ref) (refsE : List (List Ref)) : Option (Store H × ModuleInst) := do
  let dts := allocTypes m.types
  let close {k : TKind} (t : Ty k) : Ty k := t.substAll (dts.map .dt)
  let tagTypes ← m.tags.mapM fun x => dts[x.toNat]?
  let funcTypes ← m.funcs.mapM fun fn => dts[fn.type.toNat]?
  let fa := (List.range m.funcs.length).map (s.funcs.length + ·)
  let (s₁, aa) := allocMany allocTag s tagTypes
  let (s₂, ga) := allocMany (fun s (p : CGlobalType × Val) => allocGlobal s p.1 p.2) s₁
    ((m.globals.map fun g => (⟨g.type.mutability, close (liftVal g.type.value)⟩ : CGlobalType)).zip valsG)
  let (s₃, ma) := allocMany allocMem s₂ m.memories
  let (s₄, ta) := allocMany (fun s (p : CTableType × Ref) => allocTable s p.1 p.2) s₃
    ((m.tables.map fun t => (⟨t.type.address, t.type.limits, close (liftRef t.type.element)⟩ : CTableType)).zip refsT)
  let (s₅, da) := allocMany allocData s₄ (m.data.map Data.bytes)
  let (s₆, ea) := allocMany (fun s (p : CRefType × List Ref) => allocElem s p.1 p.2) s₅
    ((m.elems.map fun e => close (liftRef e.type)).zip refsE)
  let exportsInst : ModuleInst :=
    { tags := ExternAddr.tags xas ++ aa, globals := ExternAddr.globals xas ++ ga,
      mems := ExternAddr.mems xas ++ ma, tables := ExternAddr.tables xas ++ ta,
      funcs := ExternAddr.funcs xas ++ fa }
  let xi ← m.exports.mapM (allocExport? exportsInst)
  let mi : ModuleInst := { exportsInst with types := dts, datas := da, elems := ea, exports := xi }
  let (s₇, _) := allocMany (fun s (p : DefType × Func) => allocFunc s p.1 (.wasm p.2) mi) s₆
    (funcTypes.zip m.funcs)
  return (s₇, mi)

/-- `$rundata_(x, data)`. -/
def runData (x : Nat) (d : Data) : List Instr :=
  match d.mode with
  | .passive => []
  | .active y off =>
    let xd : DataIdx := ⟨Fin.ofNat _ x⟩
    off ++ [.intConst .i32 0, .intConst .i32 (BitVec.ofNat 32 d.bytes.size), .memoryInit y xd,
      .dataDrop xd]

/-- `$runelem_(x, elem)`. -/
def runElem (x : Nat) (e : Elem) : List Instr :=
  let xe : ElemIdx := ⟨Fin.ofNat _ x⟩
  match e.mode with
  | .passive => []
  | .declarative => [.elemDrop xe]
  | .active y off =>
    off ++ [.intConst .i32 0, .intConst .i32 (BitVec.ofNat 32 e.init.length), .tableInit y xe,
      .elemDrop xe]

/-- `$evalglobals`: each initializer runs with the globals allocated so far. -/
inductive EvalGlobals (P : Profile) (host : HostSemantics H) :
    Store H → Frame → List CGlobalType → List Expr → Store H → Frame → List Val → Prop where
  | nil {s : Store H} {f : Frame} : EvalGlobals P host s f [] [] s f []
  | cons {s s' s'' : Store H} {f f' f'' : Frame} {g : CGlobalType} {gs : List CGlobalType}
      {e : Expr} {es : List Expr} {v : Val} {vs : List Val}
      (he : EvalExpr P host s f e s' f' [v])
      (hs : EvalGlobals P host (allocGlobal s' g v).1
        { f' with module := { f'.module with globals := f'.module.globals ++ [(allocGlobal s' g v).2] } }
        gs es s'' f'' vs) :
      EvalGlobals P host s f (g :: gs) (e :: es) s'' f'' (v :: vs)

/-- `$evalexprs` (reference-valued initializers). -/
inductive EvalExprs (P : Profile) (host : HostSemantics H) :
    Store H → Frame → List Expr → Store H → Frame → List Ref → Prop where
  | nil {s : Store H} {f : Frame} : EvalExprs P host s f [] s f []
  | cons {s s' s'' : Store H} {f f' f'' : Frame} {e : Expr} {es : List Expr} {r : Ref}
      {rs : List Ref} (he : EvalExpr P host s f e s' f' [.ref r])
      (hs : EvalExprs P host s' f' es s'' f'' rs) :
      EvalExprs P host s f (e :: es) s'' f'' (r :: rs)

/-- `$evalexprss`. -/
inductive EvalExprss (P : Profile) (host : HostSemantics H) :
    Store H → Frame → List (List Expr) → Store H → Frame → List (List Ref) → Prop where
  | nil {s : Store H} {f : Frame} : EvalExprss P host s f [] s f []
  | cons {s s' s'' : Store H} {f f' f'' : Frame} {es : List Expr} {ess : List (List Expr)}
      {rs : List Ref} {rss : List (List Ref)} (he : EvalExprs P host s f es s' f' rs)
      (hs : EvalExprss P host s' f' ess s'' f'' rss) :
      EvalExprss P host s f (es :: ess) s'' f'' (rs :: rss)

/-- The provisional module instance `moduleinst_0` used to evaluate initializers. -/
def ModuleInst.initial (s : Store H) (m : Module) (xas : List ExternAddr) : ModuleInst :=
  { types := allocTypes m.types, globals := ExternAddr.globals xas,
    funcs := ExternAddr.funcs xas ++ (List.range m.funcs.length).map (s.funcs.length + ·) }

/-- `$instantiate(s, module, externaddr*) = c`: the configuration that runs the
element and data segments and then the start function. The global types given to
`EvalGlobals` are closed over the allocated types (a documented deviation: the spec
passes the raw `globaltype*`; see the module docstring). -/
structure Instantiate (P : Profile) (host : HostSemantics H) (s : Store H) (m : Module)
    (xas : List ExternAddr) (c : Config H) : Prop where
  valid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI
  /-- The segment indices `i_E`, `i_D` passed to `$runelem_`/`$rundata_` are `u32`
  indices (`elemidx`, `dataidx`), so there are at most `2^32` segments of each kind; and
  the lengths `n` of `DATA b^n` / `ELEM rt e^n` are emitted as `CONST I32 n`, which is only
  well formed for `n < 2^32`, so `$rundata_`/`$runelem_` (hence `$instantiate`) are
  undefined for longer segments. -/
  bounded : m.elems.length ≤ 2 ^ 32 ∧ m.data.length ≤ 2 ^ 32 ∧
    (∀ d ∈ m.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ m.elems, e.init.length < 2 ^ 32)
  run : ∃ (s₁ s₂ s₃ s₄ : Store H) (f₁ f₂ f₃ : Frame) (valsG : List Val) (refsT : List Ref)
      (refsE : List (List Ref)) (mi : ModuleInst),
    EvalGlobals P host s ⟨[], ModuleInst.initial s m xas⟩
      (m.globals.map fun g => ⟨g.type.mutability,
        (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩)
      (m.globals.map Global.init) s₁ f₁ valsG ∧
    EvalExprs P host s₁ f₁ (m.tables.map Table.init) s₂ f₂ refsT ∧
    EvalExprss P host s₂ f₂ (m.elems.map Elem.init) s₃ f₃ refsE ∧
    allocModule? s₃ m xas valsG refsT refsE = some (s₄, mi) ∧
    c = ⟨s₄, { module := mi },
      expression ((List.range m.elems.length).zip m.elems |>.flatMap fun (i, e) => runElem i e) ++
      expression ((List.range m.data.length).zip m.data |>.flatMap fun (i, d) => runData i d) ++
      (match m.start with | some x => [.plain (.call x)] | none => [])⟩

/-- `$invoke(s, funcaddr, val*)`. -/
def invoke (s : Store H) (a : Nat) (vs : List Val) : Config H :=
  ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType ((s.funcs[a]?.map FuncInst.type).getD default)]⟩

/-- The premises of `$invoke`: the function exists and the arguments are typed. -/
def InvokeOk (s : Store H) (a : Nat) (vs : List Val) : Prop :=
  ∃ fi ps rs, s.funcs[a]? = some fi ∧ Expand fi.type (.func ps rs) ∧
    List.Forall₂ (ValOk s) vs ps.toList

end Silmaril.Wasm.Execution.Core
