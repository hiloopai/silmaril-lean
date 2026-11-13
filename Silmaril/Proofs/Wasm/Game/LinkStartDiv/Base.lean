module

public import Silmaril.Proofs.Wasm.Game.LinkStartDiv.Complete
public import Silmaril.Proofs.Wasm.Game.LinkStartDiv.Linked
public import Silmaril.Proofs.Wasm.Game.Linking.Split.DivSub

/-!
# Static links with start functions, divergence observed: the systems compared

For a link with start functions `S` (`StartSetup`) and a profile `P`:

* `LP S P`, `LC S P`: the provider's instantiable system and the consumer's link system
  (`Silmaril.Games.Inst`), whose divergence-observing strategies are linked by
  `StartSetup.linkInst`;
* `LSH S P`: the shared world (provider and consumer in one store) whose instantiation runs the
  linked start sequence `S.linkedStarts`;
* their receptive completions (`complete`, along the positions of
  `Silmaril.Proofs.Wasm.Game.GamesAux.InstSystem`), and the composite `CompC S P` of the completed
  provider and consumer.

Also: the *phases* in which the consumer runs a thread (`none`: its start function, `some f`: the
export call `f`), with the states and steps of each system in a phase, and the stuck states of
the composite that the completions add.

New.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.LinkStartDiv

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking
  Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril.Proofs.Wasm.Game.Linking.Split
  Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

/-! ## Positions of instantiable systems -/

section Pos

variable {E F : Sig.{0}} {R : Type} (Sy : InstSystem E F R)

theorem path_nil_eq {E' F' : Sig.{0}} {a b : Pos E' F'} (h : Path a [] b) : a = b := by
  cases h
  rfl

theorem path_single {E' F' : Sig.{0}} {a b : Pos E' F'} {o : Move E' F'} (h : Path a [o] b) :
    Step a o b := by
  cases h with
  | cons hst hnil => cases hnil; exact hst

theorem posMap_toLTS : PosMap Sy.toLTS (InstSystem.pos Sy) where
  init := rfl
  vis h := path_single (InstSystem.run_path Sy (LTS.Run.of_step h))
  tau h := (path_nil_eq (InstSystem.run_path Sy (LTS.Run.of_step h))).symm

theorem posMap_consumer : PosMap Sy.consumerLTS (InstSystem.cpos Sy) where
  init := rfl
  vis h := path_single (InstSystem.consumer_run_path Sy (LTS.Run.of_step h))
  tau h := (path_nil_eq (InstSystem.consumer_run_path Sy (LTS.Run.of_step h))).symm

theorem running_toLTS {x y : Sy.toLTS.State} (h : Sy.toLTS.step x none y) :
    ∃ q, InstSystem.pos Sy x = .run q := by
  cases h with
  | itau _ => exact ⟨none, rfl⟩
  | tau _ => exact ⟨some _, rfl⟩

theorem running_consumer {x y : Sy.consumerLTS.State} (h : Sy.consumerLTS.step x none y) :
    ∃ q, InstSystem.cpos Sy x = .run q := by
  cases h with
  | itau _ => exact ⟨none, rfl⟩
  | tau _ => exact ⟨some _, rfl⟩

end Pos

/-- No Opponent move is legal in a running position. -/
theorem not_isO_run {E F : Sig.{0}} {q : F.Op} {o : Move E F} {p : Pos E F}
    (h : Step (.run q) o p) (ho : o.IsO) : False := by
  cases h with
  | call => exact ho
  | ret => exact ho

/-! ## The systems -/

variable (S : StartSetup) (P : Profile)

/-- The provider's instantiable system. -/
noncomputable abbrev LP : LTS S.providerI.E (S.providerI.F.withInst (Behaviour Val)) :=
  (S.providerI.instSys P S.sp S.provStart).toLTS

/-- The consumer's link system. -/
noncomputable abbrev LC : LTS (S.consumerI.E.withInst (Behaviour Val))
    (S.consumerI.F.withInst (Behaviour Val)) :=
  (S.consumerI.instSys P S.scs S.consStart).consumerLTS

/-- The shared world running the linked start sequence. -/
noncomputable abbrev LSH : LTS S.sharedI.E (S.sharedI.F.withInst (Behaviour Val)) :=
  (ShSys S.toSetup P S.linkedStarts).toLTS

/-- The completed provider. -/
noncomputable abbrev LPc : LTS S.providerI.E (S.providerI.F.withInst (Behaviour Val)) :=
  complete (LP S P) (InstSystem.pos _)

/-- The completed consumer. -/
noncomputable abbrev LCc : LTS (S.consumerI.E.withInst (Behaviour Val))
    (S.consumerI.F.withInst (Behaviour Val)) :=
  complete (LC S P) (InstSystem.cpos _)

/-- The completed shared world. -/
noncomputable abbrev LSHc : LTS S.sharedI.E (S.sharedI.F.withInst (Behaviour Val)) :=
  complete (LSH S P) (InstSystem.pos _)

/-- The composite of the completed provider and consumer. -/
noncomputable abbrev CompC : LTS S.providerI.E (S.consumerI.F.withInst (Behaviour Val)) :=
  (LPc S P).comp (LCc S P)

/-! ## Phases -/

/-- The phase of a running consumer thread: its start function (`none`) or an export call. -/
abbrev Ph : Type := Option S.consumerI.F.Op

variable {S}

/-- The function type of a phase. -/
def phF : Ph S → FnType
  | none => startType
  | some f => S.consumerI.exports.get f.1

/-- The shared state running a phase. -/
def shRun : Ph S → Store Nat × Thread → (ShSys S.toSetup P S.linkedStarts).St
  | none, c => .inst (c.1, c.2, [])
  | some f, c => .run f c

/-- The consumer's state running a phase. -/
def cRun : Ph S → Store Nat × Thread → (S.consumerI.instSys P S.scs S.consStart).St
  | none, c => .inst c
  | some f, c => .run f c

/-- The consumer's state waiting for the provider's answer to `e` in a phase. -/
def cWait : Ph S → (e : S.consumerI.E.Op) → (S.consumerI.E.Ar e → Store Nat × Thread) →
    (S.consumerI.instSys P S.scs S.consStart).St
  | none, e, k => .iwait e k
  | some f, e, k => .wait f e k

/-! ### Steps in a phase -/

theorem sh_tau (ph : Ph S) {c c' : Store Nat × Thread} (h : InternalP P c c') :
    (LSH S P).step (shRun P ph c) none (shRun P ph c') := by
  cases ph with
  | none => exact .itau (SeqStep.run h)
  | some f => exact .tau h

/-- A silent shared step in a phase is a host-free step. -/
theorem sh_silent (ph : Ph S) {c : Store Nat × Thread} {y : (LSH S P).State}
    (h : (LSH S P).step (shRun P ph c) none y) : ∃ c', InternalP P c c' ∧ y = shRun P ph c' := by
  cases ph with
  | none =>
    cases h with
    | itau hs =>
      cases hs with
      | run hi => exact ⟨_, hi, rfl⟩
  | some f =>
    cases h with
    | tau hi => exact ⟨_, hi, rfl⟩

theorem lc_tau (ph : Ph S) {c c' : Store Nat × Thread} (h : InternalP P c c') :
    (LC S P).step (cRun P ph c) none (cRun P ph c') := by
  cases ph with
  | none => exact .itau h
  | some f => exact .tau h

/-- A silent consumer step in a phase is a host-free step. -/
theorem lc_silent (ph : Ph S) {c : Store Nat × Thread} {y : (LC S P).State}
    (h : (LC S P).step (cRun P ph c) none y) : ∃ c', InternalP P c c' ∧ y = cRun P ph c' := by
  cases ph with
  | none =>
    cases h with
    | itau hi => exact ⟨_, hi, rfl⟩
  | some f =>
    cases h with
    | tau hi => exact ⟨_, hi, rfl⟩

theorem lc_call (ph : Ph S) {c : Store Nat × Thread} {e : S.consumerI.E.Op}
    (h : S.consumerI.CallsOut c e) :
    (LC S P).step (cRun P ph c) (some (.inl (.ask (some e))))
      (cWait P ph e (S.consumerI.resumeK c.1 c.2 e)) := by
  cases ph with
  | none => exact .icall (S := S.consumerI.instSys P S.scs S.consStart) ⟨h, rfl⟩
  | some f => exact .call (S := S.consumerI.instSys P S.scs S.consStart) ⟨h, rfl⟩

/-- A lower question of the consumer in a phase is an import call. -/
theorem lc_ask (ph : Ph S) {c : Store Nat × Thread} {m : (S.consumerI.E.withInst (Behaviour Val)).Op}
    {y : (LC S P).State} (h : (LC S P).step (cRun P ph c) (some (.inl (.ask m))) y) :
    ∃ e, m = some e ∧ S.consumerI.CallsOut c e ∧ y = cWait P ph e (S.consumerI.resumeK c.1 c.2 e) := by
  cases ph with
  | none =>
    cases h with
    | icall h' => obtain ⟨hc, rfl⟩ := h'; exact ⟨_, rfl, hc, rfl⟩
  | some f =>
    cases h with
    | call h' => obtain ⟨hc, rfl⟩ := h'; exact ⟨_, rfl, hc, rfl⟩

theorem lc_resume (ph : Ph S) (e : S.consumerI.E.Op) (k : S.consumerI.E.Ar e → Store Nat × Thread)
    (n : S.consumerI.E.Ar e) :
    (LC S P).step (cWait P ph e k) (some (.inl (.ans (m := some e) n))) (cRun P ph (k n)) := by
  cases ph with
  | none => exact InstSystem.LinkStep.iresume (S := S.consumerI.instSys P S.scs S.consStart) e k n
  | some f => exact InstSystem.LinkStep.resume (S := S.consumerI.instSys P S.scs S.consStart) f e k n

/-- An answer received while waiting in a phase resumes the waiting continuation. -/
theorem lc_wait_ans (ph : Ph S) {e : S.consumerI.E.Op} {k : S.consumerI.E.Ar e → Store Nat × Thread}
    {m : (S.consumerI.E.withInst (Behaviour Val)).Op} {n : (S.consumerI.E.withInst (Behaviour Val)).Ar m}
    {y : (LC S P).State} (h : (LC S P).step (cWait P ph e k) (some (.inl (.ans m n))) y) :
    ∃ n' : S.consumerI.E.Ar e, m = some e ∧ HEq n n' ∧ y = cRun P ph (k n') := by
  cases ph with
  | none =>
    cases h with
    | iresume _ _ n' => exact ⟨n', rfl, HEq.rfl, rfl⟩
  | some f =>
    cases h with
    | resume _ _ _ n' => exact ⟨n', rfl, HEq.rfl, rfl⟩

/-- A waiting consumer takes no silent step and no upper step. -/
theorem lc_wait_quiet (ph : Ph S) {e : S.consumerI.E.Op} {k : S.consumerI.E.Ar e → Store Nat × Thread}
    {l : Option (Move (S.consumerI.E.withInst (Behaviour Val)) (S.consumerI.F.withInst (Behaviour Val)))}
    {y : (LC S P).State} (h : (LC S P).step (cWait P ph e k) l y) : ∃ g, l = some (.inl g) := by
  cases ph with
  | none => cases h with | iresume _ _ n => exact ⟨_, rfl⟩
  | some f => cases h with | resume _ _ _ n => exact ⟨_, rfl⟩

theorem shRun_pos (ph : Ph S) (c : Store Nat × Thread) :
    ∃ q, InstSystem.pos (ShSys S.toSetup P S.linkedStarts) (shRun P ph c) = .run q := by
  cases ph with
  | none => exact ⟨none, rfl⟩
  | some f => exact ⟨some f, rfl⟩

theorem cRun_pos (ph : Ph S) (c : Store Nat × Thread) :
    ∃ q, InstSystem.cpos (S.consumerI.instSys P S.scs S.consStart) (cRun P ph c) = .run q := by
  cases ph with
  | none => exact ⟨none, rfl⟩
  | some f => exact ⟨some f, rfl⟩

/-! ### Composite steps -/

theorem ic_tau (ph : Ph S) {xp : (LPc S P).State} {c c' : Store Nat × Thread}
    (h : InternalP P c c') :
    (CompC S P).Silent (xp, .inl (cRun P ph c)) (xp, .inl (cRun P ph c')) :=
  LTS.CompStep.tau₂ (CStep.base (lc_tau P ph h))

theorem ip_tau {e : S.providerI.F.Op} {c c' : Store Nat × Thread} {xc : (LCc S P).State}
    (h : InternalP P c c') :
    (CompC S P).Silent (.inl (.run e c), xc) (.inl (.run e c'), xc) :=
  LTS.CompStep.tau₁ (CStep.base (.tau h))

/-- A consumer run in a phase is a silent composite run. -/
theorem ic_reach (ph : Ph S) {xp : (LPc S P).State} {c c' : Store Nat × Thread}
    (h : Reach P c c') :
    Relation.ReflTransGen (CompC S P).Silent (xp, .inl (cRun P ph c)) (xp, .inl (cRun P ph c')) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (ic_tau P ph hst)

/-- A provider run of an export call is a silent composite run. -/
theorem ip_reach {e : S.providerI.F.Op} {c c' : Store Nat × Thread} {xc : (LCc S P).State}
    (h : Reach P c c') :
    Relation.ReflTransGen (CompC S P).Silent (.inl (.run e c), xc) (.inl (.run e c'), xc) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (ip_tau P hst)

/-- The consumer calls the provider in a phase. -/
theorem isync_call (ph : Ph S) {π : Store Nat} {c : Store Nat × Thread} {e : S.consumerI.E.Op}
    (h : S.consumerI.CallsOut c e) :
    (CompC S P).Silent (.inl (.ready π), .inl (cRun P ph c))
      (.inl (.run e (π, S.providerI.initThread e)),
        .inl (cWait P ph e (S.consumerI.resumeK c.1 c.2 e))) :=
  LTS.CompStep.sync (.ask (some e)) (CStep.base (InstSystem.Step.askEx (S := S.providerI.instSys P S.sp S.provStart) π e)) (CStep.base (lc_call P ph h))

/-- The provider answers `w` in a phase and the consumer resumes. -/
theorem isync_ret (ph : Ph S) {e : S.consumerI.E.Op} {π : Store Nat} {tp : Thread}
    {c : Store Nat × Thread} {r : Result} {w : S.consumerI.E.Ar e} (hr : ResultAt π tp r)
    (hw : Answer.ofResult? (S.stubTypes.get e.1) r = some w) :
    (CompC S P).Silent (.inl (.run e (π, tp)), .inl (cWait P ph e (S.consumerI.resumeK c.1 c.2 e)))
      (.inl (.ready π), .inl (cRun P ph (S.consumerI.resumeK c.1 c.2 e w))) :=
  LTS.CompStep.sync (.ans (m := some e) w)
    (CStep.base (.ret (S := S.providerI.instSys P S.sp S.provStart) ⟨r, hr, hw, rfl⟩))
    (CStep.base (lc_resume P ph e _ w))

/-! ## Stuck states added by the completions -/

/-- A composite state without any step. -/
def Stuck (x : (CompC S P).State) : Prop := ∀ l x', ¬ (CompC S P).step x l x'

/-- The provider waits for a question (no silent step). -/
def PIdle (xp : (LP S P).State) : Prop :=
  xp = .fresh ∨ (∃ π, xp = .ready π) ∨ xp = .dead

/-- The consumer waits for an answer of the provider. -/
def CWait (xc : (LC S P).State) : Prop :=
  xc = .pwait ∨ ∃ ph e k, xc = cWait P ph e k

theorem pIdle_quiet {xp : (LP S P).State} (hp : PIdle P xp) {y : (LP S P).State}
    (h : (LP S P).step xp none y) : False := by
  rcases hp with rfl | ⟨π, rfl⟩ | rfl <;> cases h

/-- The provider has no lower interface. -/
theorem prov_ev_elim {α : Prop} (e : Ev S.providerI.E) : α := by
  cases e with
  | ask m => exact m.1.elim0
  | ans m _ => exact m.1.elim0

/-- An idle provider beside a sink is stuck. -/
theorem stuck_pIdle {xp : (LP S P).State} (hp : PIdle P xp) (p : Pos _ _) :
    Stuck P (.inl xp, .inr p) := by
  intro l x' h
  cases h with
  | tau₁ h₁ =>
    cases h₁ with
    | base hb => exact pIdle_quiet P hp hb
  | tau₂ h₂ => cases h₂
  | left e _ => exact prov_ev_elim e
  | right _ h₂ => cases h₂
  | sync _ _ h₂ => cases h₂

/-- A waiting consumer moves only by receiving an answer, and no upper move is legal. -/
theorem cWait_quiet {xc : (LC S P).State} (hc : CWait P xc) :
    (∀ l y, (LC S P).step xc l y → ∃ g, l = some (.inl g)) ∧
      ∀ g p, ¬ Step (InstSystem.cpos _ xc) (.inr g) p := by
  rcases hc with rfl | ⟨ph, e, k, rfl⟩
  · exact ⟨fun l y h => by cases h <;> exact ⟨_, rfl⟩, fun g p h => by cases h⟩
  · refine ⟨fun l y h => lc_wait_quiet P ph h, fun g p h => ?_⟩
    cases ph <;> cases h

/-- A waiting consumer beside a sink is stuck. -/
theorem stuck_cWait {xc : (LC S P).State} (hc : CWait P xc) (p : Pos _ _) :
    Stuck P (.inr p, .inl xc) := by
  have hq := cWait_quiet P hc
  intro l x' h
  cases h with
  | tau₁ h₁ => cases h₁
  | tau₂ h₂ => cases h₂ with | base hb => obtain ⟨g, hg⟩ := hq.1 _ _ hb; cases hg
  | left e _ => exact prov_ev_elim e
  | right g h₂ =>
    cases h₂ with
    | base hb => obtain ⟨g', hg⟩ := hq.1 _ _ hb; cases hg
    | sink _ hst => exact hq.2 _ _ hst
  | sync _ h₁ _ => cases h₁

/-- After a provider answer, the provider is idle. -/
theorem pIdle_of_ans {xp xp' : (LP S P).State} {m : (S.providerI.F.withInst (Behaviour Val)).Op}
    {v : (S.providerI.F.withInst (Behaviour Val)).Ar m}
    (h : (LP S P).step xp (some (.inr (.ans m v))) xp') : PIdle P xp' := by
  cases h with
  | iready _ => exact .inr (.inl ⟨_, rfl⟩)
  | ifail _ => exact .inr (.inr rfl)
  | ret _ => exact .inr (.inl ⟨_, rfl⟩)

/-- After a lower question, the consumer waits. -/
theorem cWait_of_ask {xc xc' : (LC S P).State} {m : (S.consumerI.E.withInst (Behaviour Val)).Op}
    (h : (LC S P).step xc (some (.inl (.ask m))) xc') : CWait P xc' := by
  cases h with
  | pcall => exact .inl rfl
  | icall _ => exact .inr ⟨none, _, _, rfl⟩
  | call _ => exact .inr ⟨some _, _, _, rfl⟩

/-- A completed step of an `L` state without a label is a step of `L`. -/
theorem complete_silent {E F : Sig.{0}} {L : LTS E F} {pos : L.State → Pos E F} {x : L.State}
    {z : (complete L pos).State} (h : (complete L pos).step (.inl x) none z) :
    ∃ y, L.step x none y ∧ z = .inl y := by
  cases h with
  | base hb => exact ⟨_, hb, rfl⟩

end Silmaril.Proofs.Wasm.Game.LinkStartDiv
