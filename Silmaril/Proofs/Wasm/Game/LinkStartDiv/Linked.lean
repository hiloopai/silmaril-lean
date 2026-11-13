module

public import Silmaril.Proofs.Wasm.Game.Linking.DivShared
public import Silmaril.Proofs.Wasm.Game.LinkStart.Phases

/-!
# Linked = shared with start sequences, divergence observed

For a start-free link `S` (`Linking.Setup`) and a list `starts` of start functions typed in
the shared store, the instantiable systems of the shared world and of the linked module whose
instantiation runs `starts` (`ScalarInstance.instSysSeq`) have the same divergence-observing
strategies, for every profile (`linked_eq_shared`).

Both directions are lock-step divergence-sensitive simulations (`LTS.DivSimulation`, empty
measure) along the linker relation, as in `Silmaril.Proofs.Wasm.Game.Linking.DivShared`:

* during instantiation, the start thread is either *at rest* (both threads returned
  `values []`, the stores `Persistent`, the next start function not yet invoked) or *running*
  (`Simulation.Matching` configurations, the shared one typed by the start type);
* invoking the next start function from rest starts matching invocations
  (`Simulation.Matching.invoke`);
* after instantiation the relation is that of `DivShared` (`Persistent` stores when idle,
  matching configurations when an export call runs).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.LinkStartDiv

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game
  Silmaril.Proofs.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game.LinkStart Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Link.GC
  Silmaril.Wasm.Link.GC.AdminRelation Silmaril.Wasm.Validation

variable {S : Setup} {P : Profile} {starts : List Nat}

/-- The instantiable system of the shared world running `starts`. -/
noncomputable abbrev ShSys (S : Setup) (P : Profile) (starts : List Nat) :
    InstSystem S.sharedI.E S.sharedI.F (Behaviour Val) :=
  S.sharedI.instSysSeq P S.sc starts

/-- The instantiable system of the linked module running `starts`. -/
noncomputable abbrev LiSys (S : Setup) (P : Profile) (starts : List Nat) :
    InstSystem S.linkedI.E S.linkedI.F (Behaviour Val) :=
  S.linkedI.instSysSeq P S.sl starts

/-- The relation between states of the shared and of the linked instantiable systems. -/
inductive SLI (S : Setup) (P : Profile) (starts : List Nat) :
    (ShSys S P starts).St → (LiSys S P starts).St → Prop where
  | fresh : SLI S P starts .fresh .fresh
  | rest {σ l : Store Nat} {ts tl : Thread} {rest : List Nat} (hp : S.Persistent σ l)
      (hf : σ.funcs = S.sc.funcs) (hty : ∀ a ∈ rest, StartTyped S.sc a)
      (hs : ResultAt σ ts (.values [])) (hl : ResultAt l tl (.values [])) :
      SLI S P starts (.inst (σ, ts, rest)) (.inst (l, tl, rest))
  | irun {σ l : Store Nat} {ts tl : Thread} {rest : List Nat} (hw : S.sharedI.WellFormed σ)
      (hf : σ.funcs = S.sc.funcs) (hty : ∀ a ∈ rest, StartTyped S.sc a)
      (typed : ConfigOk (ts.config σ) (Split.resC startType))
      (m : Simulation.Matching .same (ts.config σ) (tl.config l)) :
      SLI S P starts (.inst (σ, ts, rest)) (.inst (l, tl, rest))
  | idle {σ l : Store Nat} (hp : S.Persistent σ l) : SLI S P starts (.ready σ) (.ready l)
  | run {f : S.sharedI.F.Op} {σ l : Store Nat} {ts tl : Thread} {tys : List CValType}
      (hw : S.sharedI.WellFormed σ) (typed : ConfigOk (ts.config σ) tys)
      (m : Simulation.Matching .same (ts.config σ) (tl.config l)) :
      SLI S P starts (.run f (σ, ts)) (.run f (l, tl))
  | dead : SLI S P starts .dead .dead

/-! ### Facts used by both directions -/

/-- The empty finished thread has returned `values []`. -/
theorem resultAt_finished (s : Store Nat) : ResultAt s (.active {} []) (.values []) := rfl

/-- Invoking the next start function from rest starts related running threads. -/
theorem invoke_rel {σ l : Store Nat} {a : Nat} {rest : List Nat} (hp : S.Persistent σ l)
    (hf : σ.funcs = S.sc.funcs) (hty : ∀ b ∈ a :: rest, StartTyped S.sc b) :
    SLI S P starts (.inst (σ, .pending a [], rest)) (.inst (l, .pending a [], rest)) := by
  have ha : StartTyped σ a := Setup.startTyped_of_funcs (hty a (List.mem_cons_self ..)) hf
  obtain ⟨fi, hfi, -⟩ := id ha
  have typed : ThreadOk σ (.pending a []) (Split.resC startType) := Split.start_typed hp.2 ha
  exact .irun hp.2 hf (fun b hb => hty b (List.mem_cons_of_mem a hb)) typed
    (Simulation.Matching.invoke hp.1 hfi [])

/-- A start thread at rest has no host-free step. -/
theorem rest_no_internal {s : Store Nat} {t : Thread} (h : ResultAt s t (.values []))
    (y : Store Nat × Thread) : ¬ InternalP P (s, t) y :=
  resultAt_no_internal h y

/-- A thread at rest has not failed. -/
theorem rest_not_failed {s : Store Nat} {t : Thread} {b : Behaviour Val}
    (h : ResultAt s t (.values [])) : ¬ StartFailed (s, t) b := by
  intro hf
  obtain ⟨r, hr, -, -⟩ := LinkStart.StartSetup.result_of_startFailed hf
  have he : Result.values [] = r := resultAt_unique h hr
  rcases hf with ⟨h', -⟩ | ⟨a, h', -⟩
  · exact absurd (resultAt_unique h h') (by simp)
  · exact absurd (resultAt_unique h h') (by simp)

/-- A host-free step keeps the function instances. -/
theorem funcs_step {s s' : Store Nat} {t t' : Thread} (h : InternalP P (s, t) (s', t'))
    (hf : s.funcs = S.sc.funcs) : s'.funcs = S.sc.funcs :=
  (InternalP.funcs_prefix h).trans hf

/-! ### Shared to linked -/

/-- The shared world's instantiation step from a related running thread. -/
theorem fwd_irun {σ l σ' : Store Nat} {ts tl ts' : Thread} {rest : List Nat}
    (hw : S.sharedI.WellFormed σ) (hf : σ.funcs = S.sc.funcs)
    (hty : ∀ a ∈ rest, StartTyped S.sc a)
    (typed : ConfigOk (ts.config σ) (Split.resC startType))
    (m : Simulation.Matching .same (ts.config σ) (tl.config l))
    (hi : InternalP P (σ, ts) (σ', ts')) :
    ∃ y', (LiSys S P starts).toLTS.step (.inst (l, tl, rest)) none y' ∧
      SLI S P starts (.inst (σ', ts', rest)) y' := by
  obtain ⟨y', hi', m'⟩ := internal_simulation (x' := (l, tl)) hi typed m
  obtain ⟨hw', typed'⟩ := DivShared.step_typed hw typed hi
  exact ⟨.inst (y'.1, y'.2, rest), .itau (SeqStep.run hi'),
    .irun hw' (funcs_step hi hf) hty typed' m'⟩

/-- An instantiation step of the shared world. -/
theorem fwd_itau {c c' : SeqConf} {y : (LiSys S P starts).St} (hR : SLI S P starts (.inst c) y)
    (hs : SeqStep P c c') :
    ∃ y', (LiSys S P starts).toLTS.step y none y' ∧ SLI S P starts (.inst c') y' := by
  cases hs with
  | run hi =>
    cases hR with
    | rest hp hf hty hs hl => exact absurd hi (rest_no_internal hs _)
    | irun hw hf hty typed m => exact fwd_irun hw hf hty typed m hi
  | next hres =>
    cases hR with
    | rest hp hf hty hs hl => exact ⟨_, .itau (SeqStep.next hl), invoke_rel hp hf hty⟩
    | irun hw hf hty typed m =>
      obtain ⟨hl, hp⟩ := DivShared.answer_rel hw m hres
      exact ⟨_, .itau (SeqStep.next hl), invoke_rel hp hf hty⟩

/-- The shared world is ready. -/
theorem fwd_iready {c : SeqConf} {st : Store Nat} {y : (LiSys S P starts).St}
    (hR : SLI S P starts (.inst c) y) (h : (ShSys S P starts).iready c st) :
    ∃ y', (LiSys S P starts).toLTS.step y (some (Inst.ansInst .ready)) y' ∧
      SLI S P starts (.ready st) y' := by
  obtain ⟨hres, hnil, rfl⟩ := h
  cases hR with
  | rest hp hf hty hs hl => exact ⟨_, .iready ⟨hl, hnil, rfl⟩, .idle hp⟩
  | irun hw hf hty typed m =>
    obtain ⟨hl, hp⟩ := DivShared.answer_rel hw m hres
    exact ⟨_, .iready ⟨hl, hnil, rfl⟩, .idle hp⟩

/-- The shared world fails. -/
theorem fwd_ifail {c : SeqConf} {b : Behaviour Val} {y : (LiSys S P starts).St}
    (hR : SLI S P starts (.inst c) y) (h : (ShSys S P starts).ifail c b) :
    ∃ y', (LiSys S P starts).toLTS.step y (some (Inst.ansInst (.fail b))) y' ∧
      SLI S P starts .dead y' := by
  cases hR with
  | rest hp hf hty hs hl => exact absurd h (rest_not_failed hs)
  | irun hw hf hty typed m =>
    obtain ⟨r, hr, -, hback⟩ := LinkStart.StartSetup.result_of_startFailed h
    exact ⟨_, .ifail (hback (resultAt_matching hr m)), .dead⟩

/-- An export call of the shared world. -/
theorem fwd_askEx {st : Store Nat} {q : S.sharedI.F.Op} {y : (LiSys S P starts).St}
    (hR : SLI S P starts (.ready st) y) :
    ∃ y', (LiSys S P starts).toLTS.step y (some (Inst.askEx q)) y' ∧
      SLI S P starts (.run q ((ShSys S P starts).start q st)) y' := by
  cases hR with
  | idle hp =>
    cases DivShared.start_rel hp q with
    | run hw typed m => exact ⟨_, .askEx _ q, .run hw typed m⟩

/-- A host-free step of an export call of the shared world. -/
theorem fwd_tau {q : S.sharedI.F.Op} {c c' : Store Nat × Thread} {y : (LiSys S P starts).St}
    (hR : SLI S P starts (.run q c) y) (hi : InternalP P c c') :
    ∃ y', (LiSys S P starts).toLTS.step y none y' ∧ SLI S P starts (.run q c') y' := by
  cases hR with
  | @run _ _ l _ tl _ hw typed m =>
    obtain ⟨y', hi', m'⟩ := internal_simulation (x' := (l, tl)) hi typed m
    obtain ⟨hw', typed'⟩ := DivShared.step_typed hw typed hi
    exact ⟨.run _ y', .tau hi', .run hw' typed' m'⟩

/-- An answer of the shared world to an export call. -/
theorem fwd_ret {q : S.sharedI.F.Op} {c : Store Nat × Thread} {v : S.sharedI.F.Ar q}
    {st : Store Nat} {y : (LiSys S P starts).St} (hR : SLI S P starts (.run q c) y)
    (h : (ShSys S P starts).done c v st) :
    ∃ y', (LiSys S P starts).toLTS.step y (some (Inst.ansEx q v)) y' ∧
      SLI S P starts (.ready st) y' := by
  obtain ⟨r, hres, hans, rfl⟩ := h
  cases hR with
  | run hw typed m =>
    obtain ⟨hl, hp⟩ := DivShared.answer_rel hw m hres
    exact ⟨_, .ret ⟨r, hl, hans, rfl⟩, .idle hp⟩

/-- Steps of the shared instantiable system are matched by single linked steps. -/
theorem fwd_step (hS : S.Scalar) (hty₀ : ∀ a ∈ starts, StartTyped S.sc a)
    {x x' : (ShSys S P starts).St} {y : (LiSys S P starts).St}
    {o : Option (Move S.sharedI.E (S.sharedI.F.withInst (Behaviour Val)))}
    (hR : SLI S P starts x y) (h : (ShSys S P starts).toLTS.step x o x') :
    ∃ y', (LiSys S P starts).toLTS.step y o y' ∧ SLI S P starts x' y' := by
  cases h with
  | askInst =>
    cases hR
    exact ⟨_, .askInst, .rest (S.persistent_initial hS) rfl hty₀ (resultAt_finished _)
      (resultAt_finished _)⟩
  | itau hs => exact fwd_itau hR hs
  | icall h => exact DivShared.closed_op_elim (by assumption)
  | iresume m _ _ => exact DivShared.closed_op_elim m
  | iready h => exact fwd_iready hR h
  | ifail h => exact fwd_ifail hR h
  | askEx st q => exact fwd_askEx hR
  | tau hi => exact fwd_tau hR hi
  | call h => exact DivShared.closed_op_elim (by assumption)
  | resume q m _ _ => exact DivShared.closed_op_elim m
  | ret h => exact fwd_ret hR h

/-! ### Linked to shared -/

/-- The linked module's instantiation step from a related running thread. -/
theorem bwd_irun {σ l l' : Store Nat} {ts tl tl' : Thread} {rest : List Nat}
    (hw : S.sharedI.WellFormed σ) (hf : σ.funcs = S.sc.funcs)
    (hty : ∀ a ∈ rest, StartTyped S.sc a)
    (typed : ConfigOk (ts.config σ) (Split.resC startType))
    (m : Simulation.Matching .same (ts.config σ) (tl.config l))
    (hi : InternalP P (l, tl) (l', tl')) :
    ∃ x', (ShSys S P starts).toLTS.step (.inst (σ, ts, rest)) none x' ∧
      SLI S P starts x' (.inst (l', tl', rest)) := by
  obtain ⟨x', hx', m'⟩ := internal_reverse (x := (σ, ts)) typed m hi
  obtain ⟨hw', typed'⟩ := DivShared.step_typed hw typed hx'
  exact ⟨.inst (x'.1, x'.2, rest), .itau (SeqStep.run hx'),
    .irun hw' (funcs_step hx' hf) hty typed' m'⟩

/-- An instantiation step of the linked module. -/
theorem bwd_itau {c c' : SeqConf} {x : (ShSys S P starts).St} (hR : SLI S P starts x (.inst c))
    (hs : SeqStep P c c') :
    ∃ x', (ShSys S P starts).toLTS.step x none x' ∧ SLI S P starts x' (.inst c') := by
  cases hs with
  | run hi =>
    cases hR with
    | rest hp hf hty hs hl => exact absurd hi (rest_no_internal hl _)
    | irun hw hf hty typed m => exact bwd_irun hw hf hty typed m hi
  | next hres =>
    cases hR with
    | rest hp hf hty hs hl => exact ⟨_, .itau (SeqStep.next hs), invoke_rel hp hf hty⟩
    | irun hw hf hty typed m =>
      have hs : ResultAt _ _ (.values []) := DivShared.answer_rel' m hres
      exact ⟨_, .itau (SeqStep.next hs), invoke_rel (DivShared.answer_rel hw m hs).2 hf hty⟩

/-- The linked module is ready. -/
theorem bwd_iready {c : SeqConf} {st : Store Nat} {x : (ShSys S P starts).St}
    (hR : SLI S P starts x (.inst c)) (h : (LiSys S P starts).iready c st) :
    ∃ x', (ShSys S P starts).toLTS.step x (some (Inst.ansInst .ready)) x' ∧
      SLI S P starts x' (.ready st) := by
  obtain ⟨hres, hnil, rfl⟩ := h
  cases hR with
  | rest hp hf hty hs hl => exact ⟨_, .iready ⟨hs, hnil, rfl⟩, .idle hp⟩
  | irun hw hf hty typed m =>
    have hs : ResultAt _ _ (.values []) := DivShared.answer_rel' m hres
    exact ⟨_, .iready ⟨hs, hnil, rfl⟩, .idle (DivShared.answer_rel hw m hs).2⟩

/-- The linked module fails. -/
theorem bwd_ifail {c : SeqConf} {b : Behaviour Val} {x : (ShSys S P starts).St}
    (hR : SLI S P starts x (.inst c)) (h : (LiSys S P starts).ifail c b) :
    ∃ x', (ShSys S P starts).toLTS.step x (some (Inst.ansInst (.fail b))) x' ∧
      SLI S P starts x' .dead := by
  cases hR with
  | rest hp hf hty hs hl => exact absurd h (rest_not_failed hl)
  | irun hw hf hty typed m =>
    obtain ⟨r, hr, -, hback⟩ := LinkStart.StartSetup.result_of_startFailed h
    exact ⟨_, .ifail (hback (DivShared.answer_rel' m hr)), .dead⟩

/-- An export call of the linked module. -/
theorem bwd_askEx {st : Store Nat} {q : S.linkedI.F.Op} {x : (ShSys S P starts).St}
    (hR : SLI S P starts x (.ready st)) :
    ∃ x', (ShSys S P starts).toLTS.step x (some (Inst.askEx q)) x' ∧
      SLI S P starts x' (.run q ((LiSys S P starts).start q st)) := by
  cases hR with
  | idle hp =>
    cases DivShared.start_rel hp q with
    | run hw typed m => exact ⟨_, .askEx _ q, .run hw typed m⟩

/-- A host-free step of an export call of the linked module. -/
theorem bwd_tau {q : S.linkedI.F.Op} {c c' : Store Nat × Thread} {x : (ShSys S P starts).St}
    (hR : SLI S P starts x (.run q c)) (hi : InternalP P c c') :
    ∃ x', (ShSys S P starts).toLTS.step x none x' ∧ SLI S P starts x' (.run q c') := by
  cases hR with
  | @run _ σ _ ts _ _ hw typed m =>
    obtain ⟨x', hx', m'⟩ := internal_reverse (x := (σ, ts)) typed m hi
    obtain ⟨hw', typed'⟩ := DivShared.step_typed hw typed hx'
    exact ⟨.run _ x', .tau hx', .run hw' typed' m'⟩

/-- An answer of the linked module to an export call. -/
theorem bwd_ret {q : S.linkedI.F.Op} {c : Store Nat × Thread} {v : S.linkedI.F.Ar q}
    {st : Store Nat} {x : (ShSys S P starts).St} (hR : SLI S P starts x (.run q c))
    (h : (LiSys S P starts).done c v st) :
    ∃ x', (ShSys S P starts).toLTS.step x (some (Inst.ansEx q v)) x' ∧
      SLI S P starts x' (.ready st) := by
  obtain ⟨r, hres, hans, rfl⟩ := h
  cases hR with
  | run hw typed m =>
    have hs : ResultAt _ _ r := DivShared.answer_rel' m hres
    exact ⟨_, .ret ⟨r, hs, hans, rfl⟩, .idle (DivShared.answer_rel hw m hs).2⟩

/-- Steps of the linked instantiable system are matched by single shared steps. -/
theorem bwd_step (hS : S.Scalar) (hty₀ : ∀ a ∈ starts, StartTyped S.sc a)
    {x : (ShSys S P starts).St} {y y' : (LiSys S P starts).St}
    {o : Option (Move S.linkedI.E (S.linkedI.F.withInst (Behaviour Val)))}
    (hR : SLI S P starts x y) (h : (LiSys S P starts).toLTS.step y o y') :
    ∃ x', (ShSys S P starts).toLTS.step x o x' ∧ SLI S P starts x' y' := by
  cases h with
  | askInst =>
    cases hR
    exact ⟨_, .askInst, .rest (S.persistent_initial hS) rfl hty₀ (resultAt_finished _)
      (resultAt_finished _)⟩
  | itau hs => exact bwd_itau hR hs
  | icall h => exact DivShared.closed_op_elim (by assumption)
  | iresume m _ _ => exact DivShared.closed_op_elim m
  | iready h => exact bwd_iready hR h
  | ifail h => exact bwd_ifail hR h
  | askEx st q => exact bwd_askEx hR
  | tau hi => exact bwd_tau hR hi
  | call h => exact DivShared.closed_op_elim (by assumption)
  | resume q m _ _ => exact DivShared.closed_op_elim m
  | ret h => exact bwd_ret hR h

/-! ### The simulations -/

/-- **Shared to linked, divergence-sensitive**, with start sequences. -/
def fwdSimI (hS : S.Scalar) (P : Profile) (hty₀ : ∀ a ∈ starts, StartTyped S.sc a) :
    LTS.DivSimulation (ShSys S P starts).toLTS (LiSys S P starts).toLTS where
  R := SLI S P starts
  init := .fresh
  step hR h := by
    obtain ⟨y', hy', hR'⟩ := fwd_step hS hty₀ hR h
    exact ⟨y', LTS.Run.of_step hy', hR'⟩
  lt := DivShared.noLt
  wf := DivShared.noLt_wf
  tau hR h := by
    obtain ⟨y', hy', hR'⟩ := fwd_step hS hty₀ hR h
    exact .inl ⟨y', .single hy', hR'⟩

/-- **Linked to shared, divergence-sensitive**, with start sequences. -/
def bwdSimI (hS : S.Scalar) (P : Profile) (hty₀ : ∀ a ∈ starts, StartTyped S.sc a) :
    LTS.DivSimulation (LiSys S P starts).toLTS (ShSys S P starts).toLTS where
  R y x := SLI S P starts x y
  init := .fresh
  step hR h := by
    obtain ⟨x', hx', hR'⟩ := bwd_step hS hty₀ hR h
    exact ⟨x', LTS.Run.of_step hx', hR'⟩
  lt := DivShared.noLt
  wf := DivShared.noLt_wf
  tau hR h := by
    obtain ⟨x', hx', hR'⟩ := bwd_step hS hty₀ hR h
    exact .inl ⟨x', .single hx', hR'⟩

/-- **Linked = shared with start sequences, divergence observed, every profile.** -/
theorem linked_eq_shared (hS : S.Scalar) (P : Profile) (hty₀ : ∀ a ∈ starts, StartTyped S.sc a) :
    DStrategy.ofInst (LiSys S P starts) = DStrategy.ofInst (ShSys S P starts) :=
  le_antisymm (bwdSimI hS P hty₀).ofLTS_le (fwdSimI hS P hty₀).ofLTS_le

end Silmaril.Proofs.Wasm.Game.LinkStartDiv
