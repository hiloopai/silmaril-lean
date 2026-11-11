module

public import Silmaril.Wasm.Verify.Check.Defs
public import Silmaril.Proofs.Wasm.Verify.Reach.Plays
public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Proofs.Wasm.Verify.Check.Instance

/-!
# Soundness of the verifier

The Boolean certificate checks imply the invariant hypotheses (`closedB_sound`,
`avoidsB_sound`, `storeIn_of_rootsB`), so a `proved` decision on an instantiated store gives
`ReachIn` (`reachIn_of_decideStore`), and a `proved` verdict of `check` on a module gives
`ReachIn` for its instance (`reachIn_of_check`), hence "never calls import `i`" in every
profile (`check_sound`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-! ## The certificate checks -/

theorem closedB_sound {s : Store Nat} {fs G : List Nat} (h : closedB s fs G = true) :
    FuncsClosed (· ∈ G) fs (InstrIn (· ∈ G) fs) s.funcs := by
  intro a fi code ha hf hcode
  have hall := List.all_eq_true.1 h a ha
  simp only [hf, hcode, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hall
  refine ⟨hall.1, fun i hi => .inr fun x hx b hb => ?_⟩
  have hb' := hall.2 x (mem_exprCallees hi hx)
  simpa [hb] using hb'

theorem avoidsB_sound {s : Store Nat} {G : List Nat} {i : Nat} (h : avoidsB s G i = true) :
    Avoids (· ∈ G) s.funcs i := by
  intro a fi ha hf hcode
  have hall := List.all_eq_true.1 h a ha
  simp [isHost, hf, hcode] at hall

theorem mem_storeFuncs_of {H : Type} {s : Store H} {G : List Nat}
    (h : ∀ a ∈ storeFuncs s, a ∈ G) : StoreIn (· ∈ G) s where
  globals g hg r hr a ha := h a (by
    simp only [storeFuncs, List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inl (.inl (.inl ⟨g, hg, by simpa [valFuncs, hr] using ha⟩)))))
  tables t ht r hr a ha := h a (by
    simp only [storeFuncs, List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inl (.inl (.inr ⟨t, ht, r, hr, ha⟩)))))
  elems e he r hr a ha := h a (by
    simp only [storeFuncs, List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inl (.inr ⟨e, he, r, hr, ha⟩))))
  structs si hsi r hr a ha := h a (by
    simp only [storeFuncs, List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inr ⟨si, hsi, _, hr, by simpa [fieldFuncs, valFuncs] using ha⟩)))
  arrays ai hai r hr a ha := h a (by
    simp only [storeFuncs, List.mem_append, List.mem_flatMap]
    exact .inl (.inr ⟨ai, hai, _, hr, by simpa [fieldFuncs, valFuncs] using ha⟩))
  exns e he r hr a ha := h a (by
    simp only [storeFuncs, List.mem_append, List.mem_flatMap]
    exact .inr ⟨e, he, _, hr, by simpa [valFuncs] using ha⟩)

theorem rootsB_mem {G roots : List Nat} (h : rootsB G roots = true) : ∀ a ∈ roots, a ∈ G := by
  intro a ha
  simpa using List.all_eq_true.1 h a ha

theorem storeIn_of_rootsB {s : Store Nat} {G addrs : List Nat}
    (h : rootsB G (rootsOf s addrs) = true) : StoreIn (· ∈ G) s :=
  mem_storeFuncs_of fun a ha => rootsB_mem h a (by simp [rootsOf, ha])

/-! ## Decisions -/

/-- A `proved` decision passed the certificate check. -/
theorem decideStore_proved {s : Store Nat} {fs addrs : List Nat} {i : Nat} {imp : Option FnType}
    (h : (decideStore s fs addrs i imp).verdict = .proved) :
    ∃ G, closedB s fs G = true ∧ rootsB G (rootsOf s addrs) = true ∧ avoidsB s G i = true := by
  unfold decideStore at h
  dsimp only at h
  by_cases hc : (closedB s fs (closure s fs (rootsOf s addrs)) &&
      rootsB (closure s fs (rootsOf s addrs)) (rootsOf s addrs) &&
      avoidsB s (closure s fs (rootsOf s addrs)) i) = true
  · simp only [Bool.and_eq_true] at hc
    exact ⟨_, hc.1.1, hc.1.2, hc.2⟩
  · have hc' : (closedB s fs (closure s fs (rootsOf s addrs)) &&
        rootsB (closure s fs (rootsOf s addrs)) (rootsOf s addrs) &&
        avoidsB s (closure s fs (rootsOf s addrs)) i) = false := by simpa using hc
    rw [hc'] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · split at h <;> cases h

/-- A `refuted` decision found a counterexample, and reports it. -/
theorem decideStore_refuted {s : Store Nat} {fs addrs : List Nat} {i : Nat} {imp : Option FnType}
    (h : (decideStore s fs addrs i imp).verdict = .refuted) :
    ∃ x, refuteOpt s addrs imp i anyCall = some x ∧
      decideStore s fs addrs i imp = ⟨.refuted, .counterexample x⟩ := by
  unfold decideStore at h ⊢
  dsimp only at h ⊢
  split at h
  · cases h
  · rename_i h₁
    simp only [h₁, Bool.false_eq_true, ↓reduceIte]
    split at h
    · rename_i x hx
      exact ⟨x, hx, rfl⟩
    · split at h <;> cases h

/-- A `proved` decision on the store of an instance gives the invariant hypotheses. -/
theorem reachIn_of_decideStore {I : ScalarInstance} (hok : I.Ok) {fs : List Nat} {i : Nat}
    {imp : Option FnType} (h : (decideStore I.store fs I.addrs i imp).verdict = .proved) :
    ∃ G : List Nat, ReachIn I (· ∈ G) fs i := by
  obtain ⟨G, hc, hr, ha⟩ := decideStore_proved h
  refine ⟨G, closedB_sound hc, storeIn_of_rootsB hr, fun j => ?_, avoidsB_sound ha⟩
  have hj : j.val < I.addrs.length := by rw [hok.addrs_length]; exact j.isLt
  have hmem : I.addr j ∈ I.addrs := by
    simp only [ScalarInstance.addr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some]
    exact List.getElem_mem hj
  exact rootsB_mem hr _ (by simp [rootsOf, hmem])

/-- Every import of an instance is a function. -/
theorem all_isFuncImport {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) : mt.imports.all isFuncImport = true := by
  refine List.all_eq_true.2 fun xt hxt => ?_
  obtain ⟨d, rfl⟩ := hI.funcImports xt hxt
  rfl

/-- An instance has no start function. -/
theorem start_none {m : Module} {mt : CModuleType} {I : ScalarInstance} (hI : IsInstance m mt I) :
    m.start = none := by
  obtain ⟨f, hinst, -⟩ := hI.instantiated
  exact (instantiateOnce?_start hinst).symm

/-- **On an instance, the verifier for "never calls import `i`" is the decision on its store**
(or the import is out of range). -/
theorem check_neverCall_cases {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) (i : Nat) :
    check m (.neverCall i) = ⟨.unknown, .importOutOfRange⟩ ∨
      ∃ fs, check m (.neverCall i) = decideStore I.store fs I.addrs i (importType? mt i) := by
  obtain ⟨f, hinst, haddrs⟩ := hI.instantiated
  have hall : mt.imports.all isFuncImport = true := all_isFuncImport hI
  have hst : m.start = none := start_none hI
  by_cases hi : mt.imports.length ≤ i
  · left
    simp only [check, hI.valid, hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi]
  · right
    refine ⟨f.module.funcs, ?_⟩
    simp only [check, hI.valid, hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi, hst,
      Option.isSome_none, hinst, haddrs]

/-- A `proved` verdict of `check` on a module gives the invariant hypotheses for its
instance. -/
theorem reachIn_of_check {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : Nat} (h : (check m (.neverCall i)).verdict = .proved) :
    ∃ (G : List Nat) (fs : List Nat), ReachIn I (· ∈ G) fs i := by
  rcases check_neverCall_cases hI i with hc | ⟨fs, hc⟩
  · rw [hc] at h
    cases h
  · rw [hc] at h
    obtain ⟨G, hG⟩ := reachIn_of_decideStore hI.ok h
    exact ⟨G, fs, hG⟩

/-- **Soundness of the verifier for "never calls import `i`"** (every profile `P`). -/
theorem check_sound {m : Module} {mt : CModuleType} {I : ScalarInstance} (hI : IsInstance m mt I)
    {i : (ifaceOf I).Imp} (h : (check m (.neverCall i.val)).verdict = .proved) (P : Profile) :
    Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) (WasmProg.ofInstance I) i := by
  obtain ⟨G, fs, hR⟩ := reachIn_of_check hI h
  exact neverCall_of_reachIn hR P

/-- The computed instance of a module whose `instance?` succeeds is its instance. -/
theorem isInstance_instOf {m : Module} (hm : (instance? m).isSome = true) :
    ∃ mt, IsInstance m mt (instOf m) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hm
  have hI : instOf m = r.2 := by simp [instOf, hr]
  exact ⟨r.1, hI ▸ isInstance_of_instance? hr⟩

/-- **The verifier on a module**: if the module's instance is computed and `check` proves
"never calls import `i`", the module's program satisfies it, for every profile. -/
theorem check_neverCall {m : Module} (hm : (instance? m).isSome = true)
    {i : (ifaceOf (instOf m)).Imp} (h : (check m (.neverCall i.val)).verdict = .proved)
    (P : Profile) :
    Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf m) i :=
  check_sound (isInstance_instOf hm).choose_spec h P

/-- "Never called" implies "never called from export `e`". -/
theorem neverCallFrom_of_neverCall {P : Profile} {X : WIface} {p : WasmProg X} {i : X.Imp}
    (h : Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) p i) (e : X.Exp) :
    Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) p (i, e) := by
  rw [models_iff] at h ⊢
  intro t ht hs ev r hr a hev _
  exact h t ht a (by rw [hr, ← hev]; simp)

/-- **The verifier for "never called from export `e`"**: through "never called". -/
theorem check_neverCallFrom {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : (ifaceOf I).Imp}
    (h : (check m (.neverCall i.val)).verdict = .proved) (e : (ifaceOf I).Exp) (P : Profile) :
    Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) (WasmProg.ofInstance I)
      (i, e) :=
  neverCallFrom_of_neverCall (check_sound hI h P) e

/-- **Closed-world soundness of the verifier**: if `check` proves "never calls import `i`",
then in every Core run of every export call of the module's instance, against every
environment, no configuration is about to call import `i`. Every profile. -/
theorem check_closed_world {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : Nat} (h : (check m (.neverCall i)).verdict = .proved)
    (P : Profile) (K : Env I.E) (j : Fin I.exports.length) (args : Typed (I.exports.get j).params)
    {c : Config Nat} (hrun : Steps P (hostOf I.imports K) (invoke I.store (I.addr j) args.1) c) :
    ∀ E a args', decompose? c.store c.code ≠ some (E, a, i, args') := by
  obtain ⟨G, fs, hR⟩ := reachIn_of_check hI h
  exact neverCall_closed_world hR P K j args hrun

end Silmaril.Wasm.Verify
