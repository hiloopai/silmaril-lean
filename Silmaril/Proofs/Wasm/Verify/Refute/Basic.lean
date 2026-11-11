module

public import Silmaril.Wasm.Verify.Refute.Defs
public import Silmaril.Wasm.Spec.Run.Thms
public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Proofs.Wasm.Verify.Reach.Plays

/-!
# Counterexamples are plays

A counterexample found by `refuteStore` on the store of an instance `I` (`IsInstance m mt I`) is
a play `[call j args, icall i args']` of `I.strategy P I.store`, for every profile `P` admitting
the deterministic steps of `profile refOracle` (`refute_play`), hence a trace of `wasmSem P`
(`refute_trace`); and against every environment `K`, a Core run of the export call reaches the
callout of `i` (`refute_closed_world`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-! ## Candidate arguments -/

theorem candVal_hasVal (k : Nat) (t : ScalarType) : t.HasVal (candVal k t) := by
  cases t with
  | num t => exact ⟨_, rfl⟩
  | v128 => exact ⟨_, rfl⟩
  | i31 n => exact .inl ⟨_, rfl⟩

theorem candArgs_typed (k : Nat) : ∀ ps : List ScalarType,
    List.Forall₂ ScalarType.HasVal ps (candArgs k ps)
  | [] => .nil
  | t :: ps => .cons (candVal_hasVal k t) (candArgs_typed k ps)

/-! ## Runs -/

/-- A callout found by the interpreter is reached by a host-free Core run. -/
theorem calloutOf?_sound {s : Store Nat} {a : Nat} {args : List Val} {h : Nat}
    {args' : List Val} (hs : StoreOk s) (hi : InvokeOk s a args)
    (hc : calloutOf? s a args = some (h, args')) :
    ∃ d, Steps (profile refOracle) (Det.noHost : HostSemantics Nat) (invoke s a args) d ∧
      ∃ E a', decompose? d.store d.code = some (E, a', h, args') := by
  unfold calloutOf? at hc
  split at hc
  · rename_i c b r hrun
    split at hc
    · rename_i E a' h' args'' hd
      cases hc
      exact ⟨c, Exec.InvokeRun.runInvoke?_steps_noHost hs hi hrun, E, a', hd⟩
    · cases hc
  · cases hc

/-- What a hit of `tryExport` records. -/
theorem tryExport_inv {s : Store Nat} {addrs : List Nat} {imp : FnType} {i : Nat}
    {bad : List Val → Bool} {jk : Nat × Nat} {x : Cex}
    (h : tryExport s addrs imp i bad jk = some x) :
    ∃ a ft, addrs[x.exp]? = some a ∧ funcType? s a = some ft ∧
      x.args = candArgs jk.2 ft.params ∧ calloutOf? s a x.args = some (i, x.callArgs) ∧
      bad x.callArgs = true ∧ typedB imp.params x.callArgs = true := by
  obtain ⟨a, ha, h₁⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ft, hft, h₂⟩ := Option.bind_eq_some_iff.1 h₁
  obtain ⟨r, hco, h₃⟩ := Option.bind_eq_some_iff.1 h₂
  have hc : (r.1 == i && bad r.2 && typedB imp.params r.2) = true := by
    by_contra hc
    simp [hc] at h₃
  have hx : x = ⟨jk.1, candArgs jk.2 ft.params, r.2⟩ := by
    simpa only [hc, ↓reduceIte, Option.some.injEq, eq_comm] using h₃
  have hc' : (r.1 = i ∧ bad r.2 = true) ∧ typedB imp.params r.2 = true := by
    simpa only [Bool.and_eq_true, beq_iff_eq] using hc
  subst hx
  refine ⟨a, ft, ha, hft, rfl, ?_, hc'.1.2, hc'.2⟩
  rw [hco, ← hc'.1.1]

/-- What a counterexample of `refuteStore` records. -/
theorem refuteStore_inv {s : Store Nat} {addrs : List Nat} {imp : FnType} {i : Nat}
    {bad : List Val → Bool} {x : Cex} (h : refuteStore s addrs imp i bad = some x) :
    ∃ a ft k, addrs[x.exp]? = some a ∧ funcType? s a = some ft ∧
      x.args = candArgs k ft.params ∧ calloutOf? s a x.args = some (i, x.callArgs) ∧
      bad x.callArgs = true ∧ typedB imp.params x.callArgs = true := by
  obtain ⟨jk, -, hjk⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨a, ft, ha, hft, hargs, hco, hbad, hty⟩ := tryExport_inv hjk
  exact ⟨a, ft, jk.2, ha, hft, hargs, hco, hbad, hty⟩

/-! ## Plays -/

theorem forall₂_get {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {k : Nat} (h₁ : k < l₁.length)
      (h₂ : k < l₂.length), R l₁[k] l₂[k]
  | _ :: _, _ :: _, .cons hab _, 0, _, _ => hab
  | _ :: _, _ :: _, .cons _ hrest, _ + 1, h₁, h₂ =>
    forall₂_get hrest (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂)

/-- The export type of an instance is the type read off the store. -/
theorem export_type_eq {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {j : Nat} {a : Nat} {ft : FnType} (ha : I.addrs[j]? = some a)
    (hft : funcType? I.store a = some ft) :
    ∃ hj : j < I.exports.length, I.exports.get ⟨j, hj⟩ = ft ∧ I.addr ⟨j, hj⟩ = a := by
  have hlen : I.addrs.length = I.exports.length := hI.exportTypes.length_eq
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ha
  have hj' : j < I.exports.length := hlen ▸ hj
  obtain ⟨fi, hfi, hty⟩ := forall₂_get hI.exportTypes hj hj'
  have hft' : funcType? I.store I.addrs[j] = some I.exports[j] := by
    simp only [funcType?, hfi, Option.bind_some, hty]
  rw [hft'] at hft
  refine ⟨hj', Option.some.inj hft, ?_⟩
  simp [ScalarInstance.addr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

/-- The import type of an instance is the closed import type read as a scalar type. -/
theorem import_type_eq {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : Nat} {imp : FnType}
    (himp : ((CExternType.funcs mt.imports)[i]?).bind FnType.ofDefType? = some imp) :
    ∃ hi : i < I.imports.length, I.imports.get ⟨i, hi⟩ = imp := by
  obtain ⟨d, hd, hdi⟩ := Option.bind_eq_some_iff.1 himp
  have hlen : (CExternType.funcs mt.imports).length = I.imports.length :=
    hI.importTypes.length_eq
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hd
  have hi' : i < I.imports.length := hlen ▸ hi
  have hR : FnType.ofDefType? (CExternType.funcs mt.imports)[i] = some I.imports[i] :=
    forall₂_get hI.importTypes hi hi'
  rw [hR] at hdi
  exact ⟨hi', Option.some.inj hdi⟩

/-- Typed arguments of an import give its import question. -/
theorem importOp?_of_typedB {I : ScalarInstance} {i : Nat} (hi : i < I.imports.length)
    {args : List Val} (ht : typedB (I.imports.get ⟨i, hi⟩).params args = true) :
    ∃ e : I.E.Op, I.importOp? i args = some e ∧ e.1 = ⟨i, hi⟩ ∧ e.2.1 = args := by
  have hty : List.Forall₂ ScalarType.HasVal (I.imports.get ⟨i, hi⟩).params args := typedB_sound ht
  refine ⟨⟨⟨i, hi⟩, ⟨args, hty⟩⟩, ?_, rfl, rfl⟩
  unfold ScalarInstance.importOp? ifaceOp?
  simp only [hi, hty, ↓reduceDIte]

/-- **A recorded hit is a play** (every profile admitting the deterministic steps of the
refuter's profile): the question of export `x.exp` followed by the import question of `i`. -/
theorem refute_play_of {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : Nat} {imp : FnType}
    (himp : ((CExternType.funcs mt.imports)[i]?).bind FnType.ofDefType? = some imp)
    {bad : List Val → Bool} {x : Cex} {a : Nat} {ft : FnType} {k : Nat}
    (ha : I.addrs[x.exp]? = some a) (hft : funcType? I.store a = some ft)
    (hargs : x.args = candArgs k ft.params)
    (hco : calloutOf? I.store a x.args = some (i, x.callArgs))
    (hbad : bad x.callArgs = true) (hty : typedB imp.params x.callArgs = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ∃ (j : Fin I.exports.length) (a : Typed (I.exports.get j).params) (e : I.E.Op),
      j.val = x.exp ∧ a.1 = x.args ∧ e.1.val = i ∧ e.2.1 = x.callArgs ∧ bad x.callArgs = true ∧
      [.inr (.ask ⟨j, a⟩), .inl (.ask e)] ∈ I.strategy P I.store := by
  obtain ⟨hj, hexp, haddr⟩ := export_type_eq hI ha hft
  obtain ⟨hi, himp'⟩ := import_type_eq hI himp
  have htyped : List.Forall₂ ScalarType.HasVal (I.exports.get ⟨x.exp, hj⟩).params x.args := by
    rw [hexp, hargs]
    exact candArgs_typed k ft.params
  let w : Typed (I.exports.get ⟨x.exp, hj⟩).params := ⟨x.args, htyped⟩
  have hinv : InvokeOk I.store (I.addr ⟨x.exp, hj⟩) w.1 := invokeOk_of_wellFormed hI.ok _ w
  have hinv' : InvokeOk I.store a x.args := haddr ▸ hinv
  obtain ⟨d, hrun, E, a', hd⟩ := calloutOf?_sound hI.ok.storeOk hinv' hco
  have hrunP : Steps P (Det.noHost : HostSemantics Nat) (invoke I.store a x.args) d :=
    Relation.ReflTransGen.mono hP _ _ hrun
  obtain ⟨e, he, he1, he2⟩ := importOp?_of_typedB hi (himp' ▸ hty)
  have hplay : [.inr (.ask ⟨⟨x.exp, hj⟩, w⟩), .inl (.ask e)] ∈ I.strategy P I.store := by
    refine ScalarInstance.ask_call_iff.2 ⟨d, ?_, E, a', i, x.callArgs, hd, he⟩
    show Steps P Det.noHost (invoke I.store (I.addr ⟨x.exp, hj⟩) x.args) d
    rw [haddr]
    exact hrunP
  exact ⟨⟨x.exp, hj⟩, w, e, rfl, rfl, by rw [he1], he2, hbad, hplay⟩

/-- **A counterexample is a play** (every profile admitting the deterministic steps of the
refuter's profile): the export question followed by the import question of `i`. -/
theorem refute_play {m : Module} {mt : CModuleType} {I : ScalarInstance} (hI : IsInstance m mt I)
    {i : Nat} {imp : FnType}
    (himp : ((CExternType.funcs mt.imports)[i]?).bind FnType.ofDefType? = some imp)
    {bad : List Val → Bool} {x : Cex} (h : refuteStore I.store I.addrs imp i bad = some x)
    {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ∃ (j : Fin I.exports.length) (a : Typed (I.exports.get j).params) (e : I.E.Op),
      a.1 = x.args ∧ e.1.val = i ∧ e.2.1 = x.callArgs ∧ bad x.callArgs = true ∧
      [.inr (.ask ⟨j, a⟩), .inl (.ask e)] ∈ I.strategy P I.store := by
  obtain ⟨a, ft, k, ha, hft, hargs, hco, hbad, hty⟩ := refuteStore_inv h
  obtain ⟨j, w, e, -, h₁, h₂, h₃, h₄, h₅⟩ := refute_play_of hI himp ha hft hargs hco hbad hty hP
  exact ⟨j, w, e, h₁, h₂, h₃, h₄, h₅⟩

/-- **A counterexample is a trace** of the Wasm semantics of the instance. -/
theorem refute_trace {m : Module} {mt : CModuleType} {I : ScalarInstance} (hI : IsInstance m mt I)
    {i : (ifaceOf I).Imp} {imp : FnType}
    (himp : ((CExternType.funcs mt.imports)[i.val]?).bind FnType.ofDefType? = some imp)
    {bad : List Val → Bool} {x : Cex} (h : refuteStore I.store I.addrs imp i.val bad = some x)
    {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ∃ t ∈ (wasmSem P).traces (WasmProg.ofInstance I), Event.icall i x.callArgs ∈ t ∧
      bad x.callArgs = true := by
  obtain ⟨j, a, e, -, he1, he2, hbad, hplay⟩ := refute_play hI himp h hP
  have hei : e.1 = i := Fin.ext he1
  refine ⟨[.inr (.ask ⟨j, a⟩), .inl (.ask e)].map moveEvent, ⟨_, hplay, rfl⟩, ?_, hbad⟩
  have hev : moveEvent (X := ifaceOf I) (.inl (.ask e)) = Event.icall i x.callArgs := by
    simp only [moveEvent, Sum.map_inl, evOf, Event.icall, he2, hei]
  rw [← hev]
  exact List.mem_map_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))

/-- **Closed world**: against every environment `K`, a Core run of the export call of the
counterexample reaches the callout of import `i` (every profile admitting the deterministic
steps). -/
theorem refute_closed_world {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : Nat} {imp : FnType}
    {bad : List Val → Bool} {x : Cex} (h : refuteStore I.store I.addrs imp i bad = some x)
    {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ∃ (j : Fin I.exports.length) (w : Typed (I.exports.get j).params), w.1 = x.args ∧
      ∀ K : Env I.E, ∃ c : Config Nat,
        Steps P (hostOf I.imports K) (invoke I.store (I.addr j) w.1) c ∧
        ∃ E a, decompose? c.store c.code = some (E, a, i, x.callArgs) := by
  obtain ⟨a, ft, k, ha, hft, hargs, hco, -, -⟩ := refuteStore_inv h
  obtain ⟨hj, hexp, haddr⟩ := export_type_eq hI ha hft
  have htyped : List.Forall₂ ScalarType.HasVal (I.exports.get ⟨x.exp, hj⟩).params x.args := by
    rw [hexp, hargs]
    exact candArgs_typed k ft.params
  have hinv : InvokeOk I.store (I.addr ⟨x.exp, hj⟩) x.args :=
    invokeOk_of_wellFormed hI.ok _ ⟨x.args, htyped⟩
  obtain ⟨d, hrun, E, a', hd⟩ := calloutOf?_sound hI.ok.storeOk (haddr ▸ hinv) hco
  have hrunP : Steps P (Det.noHost : HostSemantics Nat) (invoke I.store a x.args) d :=
    Relation.ReflTransGen.mono hP _ _ hrun
  refine ⟨⟨x.exp, hj⟩, ⟨x.args, htyped⟩, rfl, fun K => ⟨d, ?_, E, a', hd⟩⟩
  show Steps P (hostOf I.imports K) (invoke I.store (I.addr ⟨x.exp, hj⟩) x.args) d
  rw [haddr]
  exact Exec.EndToEnd.Steps.of_noHost _ hrunP

end Silmaril.Wasm.Verify
