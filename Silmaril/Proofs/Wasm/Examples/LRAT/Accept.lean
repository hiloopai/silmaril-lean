module

public import Silmaril.Proofs.Wasm.Examples.LRAT.Tests
public import Silmaril.Wasm.Verify.Kernel.Thms
public import Silmaril.Wasm.Verify.Check.Thms
public import Silmaril.Wasm.Spec.Run.Thms
public import Silmaril.Wasm.Spec.Multi.Thms
public import Silmaril.Wasm.Game.Adequacy.Thms
public import Silmaril.Wasm.Game.Instantiate.Thms

@[expose] public section

/-!
# The LRAT checker accepts a refutation: a kernel-checked session

`wasmCheck F proof` (`Tests`) runs silmaril-lean's verified interpreter `runInvoke?` on the
export calls of the DIMACS input of `F`, the LRAT steps of `proof` and a final `unsat`, one call
at a time from the instantiated store `lratS`. `runCallsF` is `runCalls` over `runInvokeF`
(`Silmaril.Wasm.Verify.Kernel`), equal to it (`runCallsF_eq`, from `runInvokeF_eq`) and reducible
by the kernel.

* `unitPair_acceptsAll` (`kernel_rfl` on `acceptsAllF`): on the
  unsatisfiable `unitPair = [[1], [-1]]` and its one-step RUP refutation `unitPairProof =
  [.add 3 [] [1, 2]]` the interpreter answers every call and `unsat` answers `1`;
  **`unitPair_accepted`**: `wasmCheck unitPair unitPairProof = true`; `unitPair_check`,
  `unitPair_unsat`: the reference checker accepts the same proof (`check_sound`);
* `session_of_runCalls` (any instance): interpreter answers to every call of a list of export
  questions, from a store where the instance is well formed, form a closed-world Core 3.0
  `Session` at every profile admitting the interpreter's deterministic steps, against every
  environment throwing only existing exceptions (`runInvoke?_steps_noHost`, `answer_of_run`,
  `wellFormed_after_run`);
* **`unitPair_session`**: at every such profile and against every environment, there is a Core
  session of `lratI` from its instantiated store whose calls are those of `unitPair` and
  `unitPairProof` and whose last call (`unsat`) answers `1`.

This is one accepted run, not completeness or a performance guarantee.

New proofs.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Verify.Kernel
open Silmaril.Logic.SAT Silmaril.Logic.SAT.LRAT

/-- `runCall` over `runInvokeF`. -/
noncomputable def runCallF (s : Store Nat) (j : Nat) (args : List Val) :
    Option (Store Nat × Option Result) :=
  match runInvokeF refOracle refFuel s j args with
  | some (c, _, r) => some (c.store, r)
  | none => none

/-- `runCalls` over `runCallF`. -/
noncomputable def runCallsF (s : Store Nat) : List (Nat × List Val) → List (Option Result)
  | [] => []
  | (j, args) :: rest =>
    match runCallF s j args with
    | some (s', r) => r :: runCallsF s' rest
    | none => [none]

theorem runCallF_eq : runCallF = runCall := by
  funext s j args
  simp only [runCallF, runCall, runInvokeF_eq]
  rfl

theorem runCallsF_eq : runCallsF = runCalls := by
  funext s l
  induction l generalizing s with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨j, args⟩ := c
    simp only [runCallsF, runCalls, runCallF_eq, ih]
    rfl

/-- Two unit clauses `x₁` and `¬x₁`. -/
def unitPair : CNF := [[1], [-1]]

/-- The empty clause by RUP along clauses `1` and `2`. -/
def unitPairProof : List Step := [.add 3 [] [1, 2]]

theorem unitPair_check : check unitPair unitPairProof = true := by decide

theorem unitPair_unsat : unitPair.Unsat := check_sound unitPair_check

/-! ## Core sessions from interpreter runs -/

section Sessions

open Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Multi Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance} {P : Profile} {K : Env I.E}

/-- The interpreter calls of a list of export questions. -/
def callsOf (fs : List I.F.Op) : List (Nat × List Val) := fs.map fun f => (I.addr f.1, f.2.1)

/-- **Interpreter runs are Core sessions.** If the verified interpreter answers every call of
`fs` from a store at which `I` is well formed, the calls with these answers form a Core 3.0
session (`Session`) at every profile `P` admitting the steps of the interpreter's deterministic
profile, against every environment `K` throwing only existing exceptions. -/
theorem session_of_runCalls
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' →
      Step P Det.noHost c c') :
    ∀ (fs : List I.F.Op) (s : Store Nat), I.WellFormed s → ThrowsBelow K s.exns.length →
      (runCalls s (callsOf fs)).all Option.isSome = true →
      ∃ l : List (Call I), l.map Sigma.fst = fs ∧ Session P I K s l ∧
        l.map (fun c => some (Answer.toResult c.2)) = runCalls s (callsOf fs)
  | [], s, _, _, _ => ⟨[], rfl, .nil s, rfl⟩
  | f :: fs, s, hw, hK, hall => by
    have hi : InvokeOk s (I.addr f.1) f.2.1 := invokeOk_of_wellFormed hw f.1 f.2
    obtain ⟨c, b, r, hrun⟩ : ∃ c b r,
        Exec.runInvoke? refOracle refFuel s (I.addr f.1) f.2.1 = some (c, b, r) :=
      ⟨_, _, _, rfl⟩
    have hcalls : runCalls s (callsOf (f :: fs)) = r :: runCalls c.store (callsOf fs) := by
      simp only [callsOf, List.map_cons, runCalls, runCall, hrun]
    rw [hcalls, List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨res, rfl⟩ := Option.isSome_iff_exists.mp hall.1
    have hout : c.outcome? = some res := (Exec.InvokeRun.runInvoke?_eq_some hrun).2.symm
    have final : c.code = res.toAdmin := Config.outcome?_sound hout
    have run₀ := Exec.InvokeRun.runInvoke?_steps_noHost hw.storeOk hi hrun
    have run : Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c :=
      Exec.EndToEnd.Steps.of_noHost _ (Relation.ReflTransGen.mono hP _ _ run₀)
    obtain ⟨w, hw', -⟩ := ScalarInstance.answer_of_run hw hK run final
    obtain ⟨hw₂, hK₂⟩ := ScalarInstance.wellFormed_after_run hw hK run final
    obtain ⟨l, hl, hs, hres⟩ := session_of_runCalls hP fs c.store hw₂ hK₂ hall.2
    refine ⟨⟨f, w⟩ :: l, by rw [List.map_cons, hl], .cons c res run final hw' hs, ?_⟩
    rw [hcalls, List.map_cons, hres, Answer.toResult_of_ofResult? hw']

end Sessions

/-! ## The accepting session of `unitPair` -/

/-- The export question of an interpreter call `(j, args)` of `lratI`, if typed. -/
def opOf? (c : Nat × List Val) : Option lratI.F.Op :=
  if h : c.1 < lratI.exports.length then
    if ht : Silmaril.Wasm.Spec.typedB (lratI.exports.get ⟨c.1, h⟩).params c.2 = true then
      some ⟨⟨c.1, h⟩, ⟨c.2, Silmaril.Wasm.Spec.typedB_sound ht⟩⟩
    else none
  else none

theorem opOf?_eq {c : Nat × List Val} {f : lratI.F.Op} (h : opOf? c = some f) :
    (f.1.val, f.2.1) = c := by
  unfold opOf? at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h

theorem mapM_opOf? : ∀ {cs : List (Nat × List Val)} {fs : List lratI.F.Op},
    cs.mapM opOf? = some fs → fs.map (fun f => (f.1.val, f.2.1)) = cs
  | [], fs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    rfl
  | c :: cs, fs, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨f, hf, fs', hfs', rfl⟩ := h
    rw [List.map_cons, opOf?_eq hf, mapM_opOf? hfs']

theorem lrat_addr (j : Fin lratI.exports.length) : lratI.addr j = j.val := by
  have hj : j.val < 10 := lrat_exports.1 ▸ j.isLt
  have ha : lratI.addrs = List.range 10 := lrat_addrs
  simp only [Silmaril.Wasm.Game.ScalarInstance.addr, ha, List.getD_eq_getElem?_getD,
    List.getElem?_range hj, Option.getD_some]

theorem lrat_wellFormed : lratI.WellFormed lratI.store := by
  obtain ⟨mt, hmt⟩ := isInstance_instOf lrat_instance
  have hI : lratI = instOf lratModule := by
    unfold lratI
    rfl
  rw [hI]
  exact hmt.ok

theorem lrat_throwsBelow (K : Silmaril.Wasm.Game.Env lratI.E) (n : Nat) :
    Silmaril.Wasm.Game.ThrowsBelow K n := by
  intro e
  have := e.1.isLt
  simp [lrat_exports.2] at this

/-- The interpreter answers every call of the session of `F` and `proof`, the last one `1`. -/
def acceptsAll (F : CNF) (proof : List Step) : Bool :=
  let rs := runCalls lratS (checkCalls F proof)
  rs.all Option.isSome && rs.getLast? == some (some (.values [Val.i32 1]))

/-- `acceptsAll` over `runCallsF`. -/
noncomputable def acceptsAllF (F : CNF) (proof : List Step) : Bool :=
  let rs := runCallsF lratS (checkCalls F proof)
  rs.all Option.isSome && rs.getLast? == some (some (.values [Val.i32 1]))

theorem acceptsAllF_eq : acceptsAllF = acceptsAll := by
  funext F proof
  simp only [acceptsAllF, acceptsAll, runCallsF_eq]

set_option maxRecDepth 100000 in
/-- The interpreter answers every call of the session of `unitPair`, `unsat` with `1`
(kernel evaluation). -/
theorem unitPair_acceptsAll : acceptsAll unitPair unitPairProof = true := by
  rw [← acceptsAllF_eq]
  kernel_rfl

/-- **The Wasm LRAT checker accepts the refutation of `unitPair`**: the verified interpreter's
run of the session (two `add_lit`/`end_clause` clauses, `step_begin(3)`, `step_hint(1)`,
`step_hint(2)`, `step_end()`, `unsat()`) answers `1` to `unsat`. -/
theorem unitPair_accepted : wasmCheck unitPair unitPairProof = true := by
  have h := unitPair_acceptsAll
  simp only [acceptsAll, Bool.and_eq_true] at h
  simp only [wasmCheck, h.2]

theorem unitPair_ops : ((checkCalls unitPair unitPairProof).mapM opOf?).isSome = true := by
  decide +kernel

/-- **The Wasm LRAT checker has an accepting Core 3.0 session for `unitPair`**: at every
profile `P` admitting the deterministic steps of the interpreter's profile, against every
environment, the export calls of the DIMACS input of `unitPair = [[1], [-1]]` and of its RUP
refutation `[.add 3 [] [1, 2]]`, then `unsat`, form a closed-world Core session
(`Silmaril.Wasm.Spec.Multi.Session`) from the instantiated store whose last call (`unsat`) answers
`1`. -/
theorem unitPair_session {P : Silmaril.Wasm.Numerics.Profile}
    (hP : ∀ c c' : Config Nat, Step (Silmaril.Wasm.SingleThreaded.profile refOracle)
      Silmaril.Wasm.SingleThreaded.Det.noHost c c' →
      Step P Silmaril.Wasm.SingleThreaded.Det.noHost c c')
    (K : Silmaril.Wasm.Game.Env lratI.E) :
    ∃ l : List (Silmaril.Wasm.Spec.Multi.Call lratI),
      Silmaril.Wasm.Spec.Multi.Session P lratI K lratI.store l ∧
      l.map (fun c => (c.1.1.val, c.1.2.1)) = checkCalls unitPair unitPairProof ∧
      l.getLast?.map (fun c => Silmaril.Wasm.Game.Answer.toResult c.2) =
        some (.values [Val.i32 1]) := by
  obtain ⟨fs, hfs⟩ : ∃ fs, (checkCalls unitPair unitPairProof).mapM opOf? = some fs :=
    Option.isSome_iff_exists.mp unitPair_ops
  have hcalls : callsOf fs = checkCalls unitPair unitPairProof := by
    rw [← mapM_opOf? hfs, callsOf]
    exact List.map_congr_left fun f _ => by rw [lrat_addr]
  have hacc : (runCalls lratI.store (callsOf fs)).all Option.isSome = true ∧
      (runCalls lratI.store (callsOf fs)).getLast? = some (some (.values [Val.i32 1])) := by
    rw [hcalls, lratI_store]
    simpa only [acceptsAll, Bool.and_eq_true, beq_iff_eq] using unitPair_acceptsAll
  obtain ⟨l, hl, hs, hres⟩ := session_of_runCalls hP fs lratI.store lrat_wellFormed
    (lrat_throwsBelow K _) hacc.1
  have hmap : l.map (fun c => (c.1.1.val, c.1.2.1)) = checkCalls unitPair unitPairProof := by
    rw [← mapM_opOf? hfs, ← hl, List.map_map]
    rfl
  have hlast : ((l.getLast?.map fun c => Silmaril.Wasm.Game.Answer.toResult c.2).map some) =
      some (some (.values [Val.i32 1])) := by
    rw [Option.map_map, ← List.getLast?_map]
    exact (congrArg List.getLast? hres).trans hacc.2
  obtain ⟨v, hv, hvv⟩ := Option.map_eq_some_iff.mp hlast
  exact ⟨l, hs, hmap, hv.trans (congrArg some (Option.some.inj hvv))⟩

end Silmaril.Wasm.Examples.LRAT
