module

public import Silmaril.Wasm.Verify.From.Defs
public import Silmaril.Proofs.Wasm.Verify.Split.Plays
public import Silmaril.Proofs.Wasm.Verify.Check.Basic
public import Silmaril.Proofs.Wasm.Verify.Check.Refute

/-!
# Soundness of the per-export verifier

The certificate check `fromB` gives `SplitIn` for the instance, with the escaping set `V` and the
callable sets `Ce` (export `e`) and `A` (the other exports), and `Ce` avoids the import
(`splitIn_of_fromB`). Hence a `proved` verdict of `checkFrom` gives "import `i` is never called
while export `e` is active" in every profile (`checkFrom_sound`), and, closed world, no Core run
of a call of export `e` reaches a callout of `i` (`checkFrom_closed_world`). A `refuted` verdict
carries a play `[call e args, icall i args']` (`checkFrom_refuted_sound`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-! ## The certificate check -/

theorem closedVB_sound {s : Store Nat} {fs V G : List Nat} (hc : closedB s fs G = true)
    (hr : rfClosedB s fs V G = true) :
    FuncsClosed (· ∈ G) fs (PlVC (· ∈ V) (· ∈ G) fs) s.funcs := by
  intro a fi code ha hf hcode
  obtain ⟨hm, hb⟩ := closedB_sound hc a fi code ha hf hcode
  refine ⟨hm, fun i hi => .inr ⟨(hb i hi).instrIn, fun x hx b hb' => ?_⟩⟩
  have hall := List.all_eq_true.1 hr a ha
  simp only [rfSuccs, hf, hcode] at hall
  have hmem : b ∈ (exprRefFuncs code.body).filterMap fun x => fs[x]? :=
    List.mem_filterMap.2 ⟨x, mem_exprRefFuncs hi hx, hb'⟩
  simpa using List.all_eq_true.1 hall b hmem

/-- The callable sets of the per-export analysis: `Ce` for export `e`, `A` for the others. -/
def fromSets {I : ScalarInstance} (e : Nat) (A Ce : List Nat) (j : Fin I.exports.length) :
    Nat → Prop :=
  (· ∈ if j.val = e then Ce else A)

theorem fromB_parts {s : Store Nat} {fs addrs : List Nat} {i a : Nat} {A V Ce : List Nat}
    (h : fromB s fs addrs i a A V Ce = true) :
    (closedB s fs A = true ∧ rfClosedB s fs V A = true) ∧ rootsB A addrs = true ∧
      rootsB A V = true ∧ rootsB V (storeFuncs s) = true ∧
      (closedB s fs Ce = true ∧ rfClosedB s fs V Ce = true) ∧ rootsB Ce (a :: V) = true ∧
      avoidsB s Ce i = true := by
  simp only [fromB, Bool.and_eq_true] at h
  exact ⟨⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2⟩, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    ⟨h.1.1.1.2, h.1.1.2⟩, h.1.2, h.2⟩

theorem addr_mem_addrs {I : ScalarInstance} (hok : I.Ok) (j : Fin I.exports.length) :
    I.addr j ∈ I.addrs := by
  have hj : j.val < I.addrs.length := by rw [hok.addrs_length]; exact j.isLt
  simp only [ScalarInstance.addr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some]
  exact List.getElem_mem hj

/-- **The certificate gives the per-export invariant hypotheses.** -/
theorem splitIn_of_fromB {I : ScalarInstance} (hok : I.Ok) {fs : List Nat} {i e : Nat}
    {A V Ce : List Nat} (h : fromB I.store fs I.addrs i (I.addrs.getD e 0) A V Ce = true) :
    SplitIn I (· ∈ V) (fromSets e A Ce) fs ∧ ∀ j : Fin I.exports.length, j.val = e →
      Avoids (fromSets e A Ce j) I.store.funcs i := by
  obtain ⟨hA, haddrs, hVA, hstore, hCe, hroots, hav⟩ := fromB_parts h
  have hclA : FuncsClosed (· ∈ A) fs (PlVC (· ∈ V) (· ∈ A) fs) I.store.funcs :=
    closedVB_sound hA.1 hA.2
  have hclC : FuncsClosed (· ∈ Ce) fs (PlVC (· ∈ V) (· ∈ Ce) fs) I.store.funcs :=
    closedVB_sound hCe.1 hCe.2
  have hcases : ∀ j : Fin I.exports.length, (j.val = e ∧ fromSets e A Ce j = (· ∈ Ce)) ∨
      (j.val ≠ e ∧ fromSets e A Ce j = (· ∈ A)) := fun j => by
    by_cases hj : j.val = e
    · exact .inl ⟨hj, by unfold fromSets; simp only [hj, ↓reduceIte]⟩
    · exact .inr ⟨hj, by unfold fromSets; simp only [hj, ↓reduceIte]⟩
  refine ⟨⟨fun j => ?_, mem_storeFuncs_of (rootsB_mem hstore), fun j a ha => ?_, fun j => ?_⟩,
    fun j hj => ?_⟩
  · rcases hcases j with ⟨-, hj⟩ | ⟨-, hj⟩ <;> rw [hj]
    · exact hclC
    · exact hclA
  · rcases hcases j with ⟨-, hj⟩ | ⟨-, hj⟩ <;> rw [hj]
    · exact rootsB_mem hroots a (List.mem_cons_of_mem _ ha)
    · exact rootsB_mem hVA a ha
  · rcases hcases j with ⟨hje, hj⟩ | ⟨-, hj⟩ <;> rw [hj]
    · have ha : I.addr j = I.addrs.getD e 0 := by rw [← hje]; rfl
      exact rootsB_mem hroots _ (by rw [ha]; exact List.mem_cons_self)
    · exact rootsB_mem haddrs _ (addr_mem_addrs hok j)
  · rcases hcases j with ⟨-, hj'⟩ | ⟨hne, -⟩
    · rw [hj']
      exact avoidsB_sound hav
    · exact absurd hj hne

/-! ## Decisions -/

/-- A `proved` decision passed the certificate check. -/
theorem decideFrom_proved {s : Store Nat} {fs addrs : List Nat} {i e : Nat}
    {imp : Option FnType} (h : (decideFrom s fs addrs i e imp).verdict = .proved) :
    ∃ A V Ce, fromB s fs addrs i (addrs.getD e 0) A V Ce = true := by
  unfold decideFrom at h
  dsimp only at h
  split at h
  · exact ⟨_, _, _, by assumption⟩
  · split at h
    · cases h
    · split at h <;> cases h

/-- A `refuted` decision found a counterexample of export `e`. -/
theorem decideFrom_refuted {s : Store Nat} {fs addrs : List Nat} {i e : Nat}
    {imp : Option FnType} (h : (decideFrom s fs addrs i e imp).verdict = .refuted) :
    ∃ ft x, imp = some ft ∧ refuteFrom s addrs ft i anyCall e = some x ∧
      (decideFrom s fs addrs i e imp).reason = .counterexample x := by
  unfold decideFrom at h ⊢
  dsimp only at h ⊢
  split at h
  · cases h
  · rename_i h₁
    simp only [h₁, Bool.false_eq_true, ↓reduceIte]
    split at h
    · rename_i x hx
      obtain ⟨ft, hft, hr⟩ := Option.bind_eq_some_iff.1 hx
      exact ⟨ft, x, hft, hr, rfl⟩
    · split at h <;> cases h

/-- **On an instance, the per-export verifier is the decision on its store**, unless the import
or the export is out of range. -/
theorem checkFrom_cases {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) (i e : Nat) :
    checkFrom m i e = ⟨.unknown, .importOutOfRange⟩ ∨
      checkFrom m i e = ⟨.unknown, .exportOutOfRange⟩ ∨
      ∃ fs, checkFrom m i e = decideFrom I.store fs I.addrs i e (importType? mt i) := by
  obtain ⟨f, hinst, haddrs⟩ := hI.instantiated
  have hall : mt.imports.all isFuncImport = true := all_isFuncImport hI
  have hst : m.start = none := start_none hI
  by_cases hi : mt.imports.length ≤ i
  · left
    simp only [checkFrom, hI.valid, hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi]
  · right
    by_cases he : (exportFuncAddrs f.module).length ≤ e
    · left
      simp only [checkFrom, hI.valid, hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi,
        hst, Option.isSome_none, hinst, he]
    · right
      refine ⟨f.module.funcs, ?_⟩
      rw [haddrs] at he
      simp only [checkFrom, hI.valid, hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi,
        hst, Option.isSome_none, hinst, haddrs, he]

/-- A `proved` verdict of `checkFrom` gives the per-export invariant hypotheses. -/
theorem splitIn_of_checkFrom {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i e : Nat} (h : (checkFrom m i e).verdict = .proved) :
    ∃ (V : Nat → Prop) (Cs : Fin I.exports.length → Nat → Prop) (fs : List Nat),
      SplitIn I V Cs fs ∧
        ∀ j : Fin I.exports.length, j.val = e → Avoids (Cs j) I.store.funcs i := by
  rcases checkFrom_cases hI i e with hc | hc | ⟨fs, hc⟩
  · rw [hc] at h; cases h
  · rw [hc] at h; cases h
  · rw [hc] at h
    obtain ⟨A, V, Ce, hB⟩ := decideFrom_proved h
    exact ⟨_, _, fs, splitIn_of_fromB hI.ok hB⟩

/-! ## Soundness -/

/-- **Soundness of the per-export verifier** (every profile `P`): if `checkFrom` proves that
import `i` is never called while export `e` is active, the program of the instance satisfies
`neverCallFrom (i, e)`. -/
theorem checkFrom_sound {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : (ifaceOf I).Imp} {e : (ifaceOf I).Exp}
    (h : (checkFrom m i.val e.val).verdict = .proved) (P : Profile) :
    Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) (WasmProg.ofInstance I)
      (i, e) := by
  obtain ⟨V, Cs, fs, hS, hav⟩ := splitIn_of_checkFrom hI h
  exact neverCallFrom_of_splitIn hS (hav e rfl) P

/-- **The per-export verifier on a module**: both hypotheses decidable by kernel evaluation. -/
theorem checkFrom_neverCallFrom {m : Module} (hm : (instance? m).isSome = true)
    {i : (ifaceOf (instOf m)).Imp} {e : (ifaceOf (instOf m)).Exp}
    (h : (checkFrom m i.val e.val).verdict = .proved) (P : Profile) :
    Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf m) (i, e) :=
  checkFrom_sound (isInstance_instOf hm).choose_spec h P

/-! ## Closed world -/

theorem steps_cfgIn_pl {G : Nat → Prop} {fs : List Nat} {Pl : Instr → Prop}
    (hP : PlainOK G (fun _ => False) fs Pl) {P : Profile} {host : HostSemantics Nat}
    (hh : HostIn G host) {c d : Config Nat} (h : Steps P host c d)
    (hcl : FuncsClosed G fs Pl c.store.funcs) (hc : CfgIn G fs Pl c) :
    CfgIn G fs Pl d ∧ d.store.funcs = c.store.funcs := by
  induction h with
  | refl => exact ⟨hc, rfl⟩
  | tail _ hst ih =>
    obtain ⟨hc', hf'⟩ := ih
    obtain ⟨hc'', hf''⟩ := Step.cfgIn_of_empty hP hh hst (hf' ▸ hcl) hc'
    exact ⟨hc'', hf''.trans hf'⟩

theorem decompose_ne_pl {G : Nat → Prop} {fs : List Nat} {Pl : Instr → Prop} {c : Config Nat}
    (hc : CfgIn G fs Pl c) {i : Nat} (hav : Avoids G c.store.funcs i) (E : Ctx) (a : Nat)
    (args : List Val) : decompose? c.store c.code ≠ some (E, a, i, args) := by
  intro hd
  obtain ⟨fi, yy, ps, rs, hf, hcode, -, -, -, hfill⟩ := decompose?_sound hd
  have hr : Ref.func a ∈ codeRefs c.code := by
    rw [hfill]
    exact codeRefs_fill E _ _ (by simp)
  have ha : RefIn G (.func a) := hc.2.2.1 _ hr
  exact hav a fi (by simpa using ha) hf hcode

/-- **Closed world**: if `checkFrom` proves `neverCallFrom (i, e)`, then in every Core run of a
call of export `e` from the instance's store, against every environment `K`, no configuration
is about to call import `i`. Every profile. -/
theorem checkFrom_closed_world {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : Nat} {e : Fin I.exports.length}
    (h : (checkFrom m i e.val).verdict = .proved) (P : Profile) (K : Env I.E)
    (args : Typed (I.exports.get e).params) {c : Config Nat}
    (hrun : Steps P (hostOf I.imports K) (invoke I.store (I.addr e) args.1) c) :
    ∀ E a args', decompose? c.store c.code ≠ some (E, a, i, args') := by
  obtain ⟨V, Cs, fs, hS, hav⟩ := splitIn_of_checkFrom hI h
  have h₀ : CfgIn (Cs e) fs (PlVC V (Cs e) fs) (invoke I.store (I.addr e) args.1) :=
    (invoke_tInv hS.store (hS.sub e) (hS.exports e) (typed_refIn args.2)).1
  have hc := steps_cfgIn_pl plVC_plainOK hostIn_hostOf hrun (hS.closed e) h₀
  exact decompose_ne_pl hc.1 (hc.2 ▸ hav e rfl)

/-! ## Refutations -/

/-- What a counterexample of `refuteFrom` records: a hit of export `e`. -/
theorem refuteFrom_inv {s : Store Nat} {addrs : List Nat} {imp : FnType} {i : Nat}
    {bad : List Val → Bool} {e : Nat} {x : Cex} (h : refuteFrom s addrs imp i bad e = some x) :
    x.exp = e ∧ ∃ a ft k, addrs[x.exp]? = some a ∧ funcType? s a = some ft ∧
      x.args = candArgs k ft.params ∧ calloutOf? s a x.args = some (i, x.callArgs) ∧
      bad x.callArgs = true ∧ typedB imp.params x.callArgs = true := by
  obtain ⟨jk, hjk, hx⟩ := List.exists_of_findSome?_eq_some h
  have hjk' : jk.1 = e := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hjk
    rcases hjk with rfl | rfl <;> rfl
  have hexp : x.exp = jk.1 := by
    obtain ⟨a, ha, h₁⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨ft, hft, h₂⟩ := Option.bind_eq_some_iff.1 h₁
    obtain ⟨r, hco, h₃⟩ := Option.bind_eq_some_iff.1 h₂
    split at h₃
    · cases h₃; rfl
    · cases h₃
  obtain ⟨a, ft, ha, hft, hargs, hco, hbad, hty⟩ := tryExport_inv hx
  exact ⟨hexp.trans hjk', a, ft, jk.2, ha, hft, hargs, hco, hbad, hty⟩

/-- The counterexample of a `refuted` verdict of `checkFrom`: a hit of export `e`. -/
theorem checkFrom_refuted_cex {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i e : Nat} (h : (checkFrom m i e).verdict = .refuted) :
    ∃ imp x, importType? mt i = some imp ∧ refuteFrom I.store I.addrs imp i anyCall e = some x ∧
      (checkFrom m i e).reason = .counterexample x := by
  rcases checkFrom_cases hI i e with hc | hc | ⟨fs, hc⟩
  · rw [hc] at h; cases h
  · rw [hc] at h; cases h
  · rw [hc] at h ⊢
    obtain ⟨ft, x, hft, hr, hreason⟩ := decideFrom_refuted h
    exact ⟨ft, x, hft, hr, hreason⟩

/-- **Soundness of `refuted` for `neverCallFrom`**: the counterexample is a play
`[call e args, icall i args']`, so import `i` is called while export `e` is active, at every
profile `P` admitting the deterministic steps of `profile refOracle`. -/
theorem checkFrom_refuted_sound {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : (ifaceOf I).Imp} {e : (ifaceOf I).Exp}
    (h : (checkFrom m i.val e.val).verdict = .refuted) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ¬ Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P)
      (WasmProg.ofInstance I) (i, e) := by
  intro hm
  obtain ⟨imp, x, himp, hr, -⟩ := checkFrom_refuted_cex hI h
  obtain ⟨hxe, a, ft, k, ha, hft, hargs, hco, hbad, hty⟩ := refuteFrom_inv hr
  obtain ⟨j, w, e', hj, -, he1, he2, -, hplay⟩ :=
    refute_play_of hI himp ha hft hargs hco hbad hty hP
  have hje : j = e := Fin.ext (hj.trans hxe)
  have hei : e'.1 = i := Fin.ext he1
  have hev : moveEvent (X := ifaceOf I) (.inl (.ask e')) = Event.icall i x.callArgs := by
    simp only [moveEvent, Sum.map_inl, evOf, Event.icall, he2, hei]
  have ht : [.inr (.ask ⟨j, w⟩), .inl (.ask e')].map moveEvent ∈
      (wasmSem P).traces (WasmProg.ofInstance I) := ⟨_, hplay, rfl⟩
  have hsat := (models_iff _ _ _ _).1 hm _ ht [moveEvent (.inr (.ask ⟨j, w⟩))]
    (moveEvent (.inl (.ask e'))) [] rfl x.callArgs hev
  exact hsat (by rw [← hje]; rfl)

/-- `checkFrom_refuted_sound` at the specification profiles. -/
theorem checkFrom_refuted_sound_spec {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : (ifaceOf I).Imp} {e : (ifaceOf I).Exp}
    (h : (checkFrom m i.val e.val).verdict = .refuted) (nd : Bool) :
    ¬ Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (WasmProg.ofInstance I) (i, e) :=
  checkFrom_refuted_sound hI h fun _ _ hs => Step.deterministic_refines_spec nd hs

/-- `checkFrom_refuted_sound_spec` for the program of a module (hypotheses decidable by kernel
evaluation). -/
theorem checkFrom_refuted_neverCallFrom {m : Module} (hm : (instance? m).isSome = true)
    {i : (ifaceOf (instOf m)).Imp} {e : (ifaceOf (instOf m)).Exp}
    (h : (checkFrom m i.val e.val).verdict = .refuted) (nd : Bool) :
    ¬ Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf m) (i, e) :=
  checkFrom_refuted_sound_spec (isInstance_instOf hm).choose_spec h nd

end Silmaril.Wasm.Verify
