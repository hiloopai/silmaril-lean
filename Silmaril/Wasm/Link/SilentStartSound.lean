module

public import Silmaril.Wasm.Link.SilentStart
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.Link.Preparation
public import Silmaril.Wasm.Binaryen.InlineTyping
public import Silmaril.Wasm.SingleThreaded.Determinism.Stuck

@[expose] public section

namespace Silmaril.Wasm.Link.SilentStart

open Execution.Core Validation Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Every local accepted by the checker has an actual default value after
closing its type over any module instance. -/
theorem localDefault?_sound {type : ValType} (accepted : localDefault? type = true)
    (types : List DefType) :
    ∃ value, defaultVal? ((liftVal type).substAll (types.map .dt)) = some value := by
  cases type with
  | num type => cases type with
    | int type => cases type <;> exact ⟨_, rfl⟩
    | float type => cases type <;> exact ⟨_, rfl⟩
  | vec type => cases type; exact ⟨_, rfl⟩
  | ref type =>
    cases type with
    | mk nullable heap =>
      cases nullable
      · cases accepted
      · exact ⟨_, rfl⟩

theorem defaultLocal_lookup {locals : List ValType} {x : LocalIdx} {type : ValType}
    (lookup : locals[x.toNat]? = some type) (accepted : localDefault? type = true)
    (module : ModuleInst) :
    ∃ value, (Frame.forCall module [] locals).local? x = some (some value) := by
  obtain ⟨value, default⟩ := localDefault?_sound accepted module.types
  refine ⟨value, ?_⟩
  simp [Frame.forCall, Frame.local?, List.getElem?_map, lookup, default]

theorem bodyResult?_steps {locals : List ValType} {instructions : List Instr} {returned : Bool}
    (accepted : bodyResult? locals instructions = some returned) (s : Store H) (module : ModuleInst) :
    Steps P host ⟨s, Frame.forCall module [] locals, expression instructions⟩
      ⟨s, Frame.forCall module [] locals, if returned then [.plain .return_] else []⟩ := by
  fun_induction bodyResult? locals instructions generalizing returned with
  | case1 => cases accepted; exact .refl
  | case2 => cases accepted; exact .refl
  | case3 rest ih =>
    have first := (Step.parametric (P := P) (host := host) (s := s)
      (f := Frame.forCall module [] locals) ParametricStep.nop).steps.ctxtInstrs
      (vs := []) (rest := expression rest)
    apply Relation.ReflTransGen.trans ?_ (ih accepted)
    simpa [vals, expression] using first
  | case4 type bits rest ih =>
    have first := (Step.parametric (P := P) (host := host) (s := s)
      (f := Frame.forCall module [] locals)
      (ParametricStep.drop (.num ⟨.int type, bits⟩))).steps.ctxtInstrs
      (vs := []) (rest := expression rest)
    apply Relation.ReflTransGen.trans ?_ (ih accepted)
    simpa [vals, expression, Val.toAdmin] using first
  | case5 type bits rest ih =>
    have first := (Step.parametric (P := P) (host := host) (s := s)
      (f := Frame.forCall module [] locals)
      (ParametricStep.drop (.num ⟨.float type, bits⟩))).steps.ctxtInstrs
      (vs := []) (rest := expression rest)
    apply Relation.ReflTransGen.trans ?_ (ih accepted)
    simpa [vals, expression, Val.toAdmin] using first
  | case6 bits rest ih =>
    have first := (Step.parametric (P := P) (host := host) (s := s)
      (f := Frame.forCall module [] locals) (ParametricStep.drop (.vec bits))).steps.ctxtInstrs
      (vs := []) (rest := expression rest)
    apply Relation.ReflTransGen.trans ?_ (ih accepted)
    simpa [vals, expression, Val.toAdmin] using first
  | case7 index rest ih =>
    obtain ⟨type, lookup, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    split at accepted
    · next available =>
      obtain ⟨value, lookup⟩ := defaultLocal_lookup lookup available module
      have get := (Step.variable (P := P) (host := host)
        (VariableStep.localGet (s := s) lookup)).steps.ctxtInstrs
        (vs := []) (rest := .plain .drop :: expression rest)
      have drop := (Step.parametric (P := P) (host := host) (s := s)
        (f := Frame.forCall module [] locals) (ParametricStep.drop value)).steps.ctxtInstrs
        (vs := []) (rest := expression rest)
      have first : Steps P host
          ⟨s, Frame.forCall module [] locals, expression (.localGet index :: .drop :: rest)⟩
          ⟨s, Frame.forCall module [] locals, value.toAdmin :: .plain .drop :: expression rest⟩ := by
        simpa [vals, expression] using get
      have second : Steps P host
          ⟨s, Frame.forCall module [] locals, value.toAdmin :: .plain .drop :: expression rest⟩
          ⟨s, Frame.forCall module [] locals, expression rest⟩ := by
        simpa [vals] using drop
      exact first.trans (second.trans (ih accepted))
    · cases accepted
  | case8 => cases accepted

/-- A checked defined start call terminates with the exact original store and
outer frame, at every numerical profile and with every host relation. -/
theorem call_steps {s : Store H} {frame : Frame} {x : FuncIdx} {address : Nat}
    {tag : DefType} {module : ModuleInst} {code : Func}
    (index : frame.module.funcs[x.toNat]? = some address)
    (function : s.funcs[address]? = some ⟨tag, module, .wasm code⟩)
    (signature : Expand tag (.func .nil .nil))
    (silent : body? code.locals code.body = true) :
    Steps P host ⟨s, frame, [.plain (.call x)]⟩ ⟨s, frame, []⟩ := by
  obtain ⟨returned, accepted⟩ : ∃ returned, bodyResult? code.locals code.body = some returned := by
    exact Option.isSome_iff_exists.mp silent
  have enter : Steps P host ⟨s, frame, [.ref (.func address), .callRefType tag]⟩
      ⟨s, frame, [.frame 0 (Frame.forCall module [] code.locals)
        [.label 0 [] (expression code.body)]]⟩ := by
    simpa [vals, Ty.length] using (Step.callRefFunc (P := P) (host := host)
      (s := s) (f := frame) (c := .callRefType tag) (vs := []) (a := address)
      (fi := ⟨tag, module, .wasm code⟩) (ps := .nil) (rs := .nil)
      (by trivial) function signature rfl rfl).steps
  have body := ((bodyResult?_steps (P := P) (host := host) accepted s module).label
    (n := 0) (cont := [])).frame (f := frame) (n := 0)
  apply (Step.call index function).steps.trans
  apply enter.trans
  apply body.trans
  cases returned
  · exact (Step.ctxtFrame (Step.labelVals (vs := []))).steps.trans
      (Step.frameVals (vs := []) rfl).steps
  · have leave : Steps P host
        ⟨s, frame, [.frame 0 (Frame.forCall module [] code.locals)
          [.label 0 [] [.plain .return_]]]⟩
        ⟨s, frame, [.frame 0 (Frame.forCall module [] code.locals) [.plain .return_]]⟩ := by
      simpa [vals] using
        (Step.returnLabel (P := P) (host := host) (s := s)
          (f := Frame.forCall module [] code.locals) (n := 0) (cont := [])
          (vs := []) (rest := [])).steps.frame (f := frame) (n := 0)
    apply leave.trans
    simpa [vals] using
      (Step.returnFrame (P := P) (host := host) (s := s) (f := frame)
        (fi := Frame.forCall module [] code.locals) (vs' := []) (vs := [])
        (rest := []) rfl).steps

/-- Erasing a start does not change any module validation context or
function/segment/export proof. -/
theorem eraseStart_valid {m : Module} {type : CModuleType} (valid : ModuleOk m type) :
    ModuleOk {m with start := none} type := by
  cases valid with
  | mk ht hi hci hc hj hg hm htb hf hd he hs hx hn =>
    exact ModuleOk.mk ht hi hci hc hj hg hm htb hf hd he
      (by intro x impossible; cases impossible) hx hn

/-- The concrete allocator never consults the start field. -/
theorem eraseStart_allocation (s : Store H) (m : Module) (xas : List ExternAddr)
    (values : List Val) (refsT : List Ref) (refsE : List (List Ref)) :
    allocModule? s {m with start := none} xas values refsT refsE =
      allocModule? s m xas values refsT refsE := rfl

private theorem forall₂_lookup {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) {i : Nat} {x : α}
    (hx : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hx
  | @cons a b xs ys hab _ ih =>
    cases i with
    | zero => simp at hx; subst x; exact ⟨b, rfl, hab⟩
    | succ i => exact ih (by simpa using hx)

/-- The allocator's defined-function binding, for arbitrary external imports. -/
theorem allocation_function {s s' : Store H} {m : Module} {mi : ModuleInst}
    {xas : List ExternAddr} {values : List Val} {refsT : List Ref} {refsE : List (List Ref)}
    {n : Nat} {fn : Func} {tag : DefType}
    (allocated : allocModule? s m xas values refsT refsE = some (s', mi))
    (lookup : m.funcs[n]? = some fn) (typed : (allocTypes m.types)[fn.type.toNat]? = some tag) :
    mi.funcs[(ExternAddr.funcs xas).length + n]? = some (s.funcs.length + n) ∧
      s'.funcs[s.funcs.length + n]? = some ⟨tag, mi, .wasm fn⟩ := by
  obtain ⟨_, functionTypes, _, _, hft, _, hmi, hs'⟩ := allocModule?_inv allocated
  obtain ⟨tag', hdn, hd'⟩ := forall₂_lookup (forall₂_of_mapM hft) lookup
  have same : tag' = tag := Option.some.inj (hd'.symm.trans typed)
  subst tag'
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  have zipped : (functionTypes.zip m.funcs)[n]? = some (tag, fn) :=
    List.getElem?_zip_eq_some.mpr ⟨hdn, lookup⟩
  constructor
  · rw [hmi]
    simp [List.getElem?_append_right (Nat.le_add_right (ExternAddr.funcs xas).length n),
      List.getElem?_map, List.getElem?_range bound]
  · rw [hs']
    simp [List.getElem?_append_right (Nat.le_add_right s.funcs.length n),
      List.getElem?_map, zipped]

private theorem importedFunctions_filterMap (imports : List Import) :
    (imports.filterMap fun entry => match entry.type with | .func type => some type | _ => none).length =
      (imports.filter fun entry => match entry.type with | .func _ => true | _ => false).length := by
  induction imports with
  | nil => rfl
  | cons entry imports ih =>
    rcases entry with ⟨moduleName, name, type⟩
    cases type <;> simp_all

/-- Validated external bindings have exactly the checker's function-import count. -/
theorem importedFunctions_binding {s : Store H} {m : Module} {xas : List ExternAddr}
    {xtI xtE : List CExternType} (valid : ModuleOk m ⟨xtI, xtE⟩)
    (imports : List.Forall₂ (ExternAddrOk s) xas xtI) :
    (ExternAddr.funcs xas).length = importedFunctions m := by
  cases valid with
  | mk ht hi hci hc hj hg hm htb hf hd he hs hx hn =>
    exact (ExternAddrOk.forall₂_funcs imports).length_eq.trans
      ((Binaryen.InlineTy.importOk_funcs_length hi).trans (importedFunctions_filterMap m.imports))

/-- Restoring a checked silent start preserves the exact successful instance
and final store of the erased module. No deterministic numerical profile is
required. Segment-free is sufficient; memories, tables and nonfunction imports
are not excluded by this theorem. -/
theorem ready_restore {m erased : Module} {s s' : Store H} {xas : List ExternAddr}
    {mi : ModuleInst} (accepted : erase? m = some erased)
    (valid : ModuleValid m) (noData : m.data = []) (noElems : m.elems = [])
    (ready : Binaryen.Ready P SingleThreaded.Det.noHost s erased xas s' mi) :
    Binaryen.Ready P SingleThreaded.Det.noHost s m xas s' mi := by
  rcases erase?_sound accepted with ⟨_, rfl⟩ | ⟨⟨checked⟩, rfl⟩
  · exact ready
  obtain ⟨c, c', instantiated, run, _, finalStore, initialModule⟩ := ready
  obtain ⟨xtE, xtI, erasedValid, importTypes⟩ := instantiated.valid
  obtain ⟨type, sourceValid⟩ := valid
  have typeEq := (eraseStart_valid sourceValid).unique erasedValid
  cases typeEq
  have count := importedFunctions_binding sourceValid importTypes
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, values, refsT, refsE, installed,
    globals, tables, elems, allocation, initial⟩ := instantiated.run
  have initialEmpty : c = ⟨s₄, {module := installed}, []⟩ := by
    simpa [noData, noElems, expression] using initial
  rw [initialEmpty] at run initialModule
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨next, step, _⟩
  · have allocation' : allocModule? s₃ m xas values refsT refsE = some (s₄, installed) := allocation
    have bindings := allocation_function allocation' checked.codeLookup checked.typeLookup
    have startIndex : (ExternAddr.funcs xas).length +
        (checked.start.toNat - importedFunctions m) = checked.start.toNat := by
      rw [count]
      have defined := checked.defined
      omega
    rw [startIndex] at bindings
    have initialized : Instantiate P SingleThreaded.Det.noHost s m xas
        ⟨s₄, {module := installed}, [.plain (.call checked.start)]⟩ := by
      refine ⟨⟨xtE, xtI, sourceValid, importTypes⟩, instantiated.bounded, ?_⟩
      exact ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, values, refsT, refsE, installed,
        globals, tables, elems, allocation', by simp [noData, noElems, checked.startEq, expression]⟩
    have restored : Binaryen.Ready P SingleThreaded.Det.noHost s m xas s₄ installed := by
      exact ⟨_, _, initialized, call_steps bindings.1 bindings.2 checked.signature checked.silent,
        rfl, rfl, rfl⟩
    change s₄ = s' at finalStore
    change installed = mi at initialModule
    simpa only [finalStore, initialModule] using restored
  · exact (SingleThreaded.Det.not_step_vals (W := []) step).elim

end Silmaril.Wasm.Link.SilentStart
