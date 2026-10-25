module
/- Portions derived from Binaryen version_133, src/ir/effects.h.
Copyright 2017 WebAssembly Community Group participants.
Licensed under Apache-2.0; see NOTICES/Binaryen/LICENSE.txt.
Modified as a scoped Lean transcription with original definitions/proofs.
-/
public import Silmaril.Wasm.Binaryen.Joinable
public import Silmaril.Wasm.Binaryen.EffectRun

@[expose] public section

/-! # Effect analysis

A transcription of Binaryen's `EffectAnalyzer` (`src/ir/effects.h`, version_133:
fields `:60–146`, `hasSideEffects`/`hasUnremovableSideEffects` `:273–300`,
`orderedBefore` `:340`, `invalidates` `:456`) for the profile, computed on
folded trees. Read and write sets are lists (deduplication is irrelevant to
soundness). Anything outside the profile is `any`, Binaryen's conservative
default. `breakTargets` are the free de Bruijn labels of the lowering
(`BExpr.labelsList`), so the analysis is anchored on the defining semantics.

Soundness statements (all about Core 3.0 runs of the lowered code):

* **S1** `effects_pure_run`: removable, typed code reaches values in
  host-free steps with store and frame unchanged.
* **S2** `effects_frame_local`, `effects_frame_global`: unwritten locals and
  globals are unchanged on every partial run.
* **control** `effects_control_br`/`_trap`/`_diverge`: a branch escapes only to
  `breakTargets`, a trap implies `trap ∨ implicitTrap`, divergence implies
  `mayNotReturn ∨ calls`.
* **S3** `commute` and the `ignoreImplicitTraps` counterexample
  `iit_hoist_unsound` are in `Commute.lean`.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics Validation

/-- `EffectAnalyzer` for the profile. -/
structure Effects where
  /-- Unknown behaviour (outside the profile): every other field is to be ignored. -/
  any : Bool := false
  localsRead : List Nat := []
  localsWritten : List Nat := []
  globalsRead : List Nat := []
  globalsWritten : List Nat := []
  /-- Contains a call (`calls`): may do anything a function may. -/
  calls : Bool := false
  /-- An explicit trap (`unreachable`). -/
  trap : Bool := false
  /-- May trap implicitly (integer division and remainder). -/
  implicitTrap : Bool := false
  /-- Returns (`branchesOut` for `return`). -/
  branchesOut : Bool := false
  /-- May not terminate (loops). -/
  mayNotReturn : Bool := false
  /-- Free branch targets (de Bruijn depths). -/
  breakTargets : List Nat := []
  deriving DecidableEq, Repr

namespace Effects

/-- Everything (unknown code). -/
def top : Effects := { any := true }

/-- Sequential composition (`EffectAnalyzer::mergeIn`). -/
def merge (a b : Effects) : Effects where
  any := a.any || b.any
  localsRead := a.localsRead ++ b.localsRead
  localsWritten := a.localsWritten ++ b.localsWritten
  globalsRead := a.globalsRead ++ b.globalsRead
  globalsWritten := a.globalsWritten ++ b.globalsWritten
  calls := a.calls || b.calls
  trap := a.trap || b.trap
  implicitTrap := a.implicitTrap || b.implicitTrap
  branchesOut := a.branchesOut || b.branchesOut
  mayNotReturn := a.mayNotReturn || b.mayNotReturn
  breakTargets := a.breakTargets ++ b.breakTargets

/-- Transfers control or may not complete normally (`transfersControlFlow`, plus
traps and non-termination). -/
def transfers (e : Effects) : Bool :=
  e.any || e.calls || e.branchesOut || !e.breakTargets.isEmpty || e.trap || e.implicitTrap ||
    e.mayNotReturn

/-- Writes state. -/
def writes (e : Effects) : Bool := !e.localsWritten.isEmpty || !e.globalsWritten.isEmpty

/-- `hasSideEffects`. -/
def hasSideEffects (e : Effects) : Bool := e.writes || e.transfers

/-- **Removability** (`!hasUnremovableSideEffects`; with `tnh`, traps are assumed
not to happen and are therefore removable, as `trapsNeverHappen` does). -/
def removable (tnh : Bool) (e : Effects) : Bool :=
  !e.any && !e.writes && !e.calls && !e.branchesOut && e.breakTargets.isEmpty &&
    !e.mayNotReturn && (tnh || (!e.trap && !e.implicitTrap))

/-- Read/write conflicts. -/
def conflict (a b : Effects) : Bool :=
  a.localsWritten.any (fun x => b.localsRead.contains x || b.localsWritten.contains x) ||
  a.localsRead.any (fun x => b.localsWritten.contains x) ||
  a.globalsWritten.any (fun x => b.globalsRead.contains x || b.globalsWritten.contains x) ||
  a.globalsRead.any (fun x => b.globalsWritten.contains x)

/-- `orderedBefore` (`src/ir/effects.h:340`): `a` must stay before `b`. -/
def orderedBefore (a b : Effects) : Bool :=
  a.any || b.any || (a.transfers && b.hasSideEffects) || (b.transfers && a.hasSideEffects) ||
    conflict a b

/-- `invalidates` (`src/ir/effects.h:456`). -/
def invalidates (a b : Effects) : Bool := orderedBefore a b || orderedBefore b a

/-- Drop branches to label `0` and shift (leaving a scope). -/
def unbindLabel (e : Effects) : Effects := { e with breakTargets := unbind e.breakTargets }

end Effects

/-- Effects of a flat instruction (operands excluded). -/
def instrEffects : Instr → Effects
  | .nop | .drop | .select _ | .intConst _ _ | .intUnOp _ _ | .intTestOp _ _
  | .intRelOp _ _ => {}
  | .intBinOp _ (.div _) | .intBinOp _ (.rem _) => { implicitTrap := true }
  | .intBinOp _ _ => {}
  | .unreachable => { trap := true }
  | .localGet x => { localsRead := [x.toNat] }
  | .localSet x | .localTee x => { localsWritten := [x.toNat] }
  | .globalGet g => { globalsRead := [g.toNat] }
  | .globalSet g => { globalsWritten := [g.toNat] }
  | .br l | .brIf l => { breakTargets := [l.toNat] }
  | .brTable ls d => { breakTargets := d.toNat :: ls.map Idx.toNat }
  | .return_ => { branchesOut := true }
  | .call _ => { calls := true, mayNotReturn := true }
  | _ => Effects.top

mutual
/-- Effects of a folded tree. Loops may not return (Binaryen marks a loop
`mayNotReturn` when it has a back edge; this is the conservative reading). -/
def effects : BExpr → Effects
  | .op i args => (effectsList args).merge (instrEffects i)
  | .block _ body => (effectsList body).unbindLabel
  | .loop _ body => { (effectsList body).unbindLabel with mayNotReturn := true }
  | .if_ _ c t e => (effectsList c).merge ((effectsList t).merge (effectsList e)).unbindLabel
  | .tryTable .. => Effects.top
/-- Effects of a sequence. -/
def effectsList : List BExpr → Effects
  | [] => {}
  | e :: es => (effects e).merge (effectsList es)
end

/-- The effects of `ignoreImplicitTraps` mode: implicit traps are forgotten. -/
def effectsIIT (e : BExpr) : Effects := { effects e with implicitTrap := false }

/-! ## Effects as a budget

The soundness proofs run the lowered code under the effect budget `budOf` of its
effects (`Binaryen/EffectRun.lean`): every step of budgeted code keeps the
budget, writes only budgeted locals and globals, and, without calls or loops,
decreases a size. -/

/-- The effects `e` fit the budget `b`, with branch targets in `S`. -/
structure EffLe (e : Effects) (b : Bud) (S : Nat → Prop) : Prop where
  any : e.any = false
  lw : ∀ x ∈ e.localsWritten, b.lw x
  gw : ∀ g ∈ e.globalsWritten, b.gw g
  calls : e.calls = true → b.calls
  trap : e.trap = true → b.trap
  itrap : e.implicitTrap = true → b.trap
  ret : e.branchesOut = true → b.ret
  loops : e.mayNotReturn = true → b.loops
  br : ∀ l ∈ e.breakTargets, S l

/-- The budget of an effect summary (a call may trap). -/
def budOf (e : Effects) : Bud where
  lw x := x ∈ e.localsWritten
  gw g := g ∈ e.globalsWritten
  calls := e.calls = true
  trap := e.calls = true ∨ e.trap = true ∨ e.implicitTrap = true
  loops := e.mayNotReturn = true
  ret := e.branchesOut = true

theorem effLe_budOf {e : Effects} (h : e.any = false) :
    EffLe e (budOf e) (· ∈ e.breakTargets) :=
  ⟨h, fun _ hx => hx, fun _ hg => hg, id, fun ht => .inr (.inl ht), fun ht => .inr (.inr ht),
    id, id, fun _ hl => hl⟩

theorem EffLe.merge {a c : Effects} {b : Bud} {S : Nat → Prop} (h : EffLe (a.merge c) b S) :
    EffLe a b S ∧ EffLe c b S := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  simp only [Effects.merge, Bool.or_eq_false_iff, Bool.or_eq_true, List.mem_append]
    at h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨⟨h1.1, fun x hx => h2 x (.inl hx), fun g hg => h3 g (.inl hg), fun hc => h4 (.inl hc),
      fun ht => h5 (.inl ht), fun ht => h6 (.inl ht), fun hb => h7 (.inl hb),
      fun hm => h8 (.inl hm), fun l hl => h9 l (.inl hl)⟩,
    ⟨h1.2, fun x hx => h2 x (.inr hx), fun g hg => h3 g (.inr hg), fun hc => h4 (.inr hc),
      fun ht => h5 (.inr ht), fun ht => h6 (.inr ht), fun hb => h7 (.inr hb),
      fun hm => h8 (.inr hm), fun l hl => h9 l (.inr hl)⟩⟩

theorem EffLe.unbindLabel {e : Effects} {b : Bud} {S : Nat → Prop}
    (h : EffLe e.unbindLabel b S) : EffLe e b (shiftP S) :=
  ⟨h.any, h.lw, h.gw, h.calls, h.trap, h.itrap, h.ret, h.loops, shiftP_of_unbind h.br⟩

/-- A flat instruction within the budget of its effects. -/
theorem instrB_of_effLe {i : Instr} {b : Bud} {S : Nat → Prop}
    (h : EffLe (instrEffects i) b S) : InstrB b S i := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  apply InstrB.flat
  cases i
  case intBinOp t op =>
    cases op <;> simp_all [instrEffects, binTraps]
  all_goals simp_all [instrEffects, Effects.top]

mutual
/-- The lowering of a tree is within the budget of its effects. -/
theorem instrB_lower {b : Bud} :
    ∀ (e : BExpr) {S : Nat → Prop}, EffLe (effects e) b S → ∀ j ∈ e.lower, InstrB b S j
  | .op i args, S, h, j, hj => by
    have h' : EffLe ((effectsList args).merge (instrEffects i)) b S := h
    obtain ⟨ha, hi⟩ := h'.merge
    simp only [BExpr.lower_op, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact instrB_lowerList args ha j hj
    · exact instrB_of_effLe hi
  | .block _ body, S, h, j, hj => by
    have h' : EffLe (effectsList body).unbindLabel b S := h
    simp only [BExpr.lower, List.mem_singleton] at hj
    subst hj
    exact InstrB.block (instrB_lowerList body h'.unbindLabel)
  | .loop _ body, S, h, j, hj => by
    have h' : EffLe { (effectsList body).unbindLabel with mayNotReturn := true } b S := h
    simp only [BExpr.lower, List.mem_singleton] at hj
    subst hj
    exact InstrB.loop (h'.loops rfl) (instrB_lowerList body
      ⟨h'.any, h'.lw, h'.gw, h'.calls, h'.trap, h'.itrap, h'.ret, fun _ => h'.loops rfl,
        shiftP_of_unbind h'.br⟩)
  | .if_ _ c t e, S, h, j, hj => by
    have h' : EffLe ((effectsList c).merge ((effectsList t).merge (effectsList e)).unbindLabel)
      b S := h
    obtain ⟨hc, hte⟩ := h'.merge
    obtain ⟨ht, he⟩ := hte.unbindLabel.merge
    simp only [BExpr.lower, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact instrB_lowerList c hc j hj
    · exact InstrB.if_ (instrB_lowerList t ht) (instrB_lowerList e he)
  | .tryTable _ _ _, _, h, _, _ => absurd h.any (by simp [effects, Effects.top])
/-- The lowering of a sequence is within the budget of its effects. -/
theorem instrB_lowerList {b : Bud} :
    ∀ (es : List BExpr) {S : Nat → Prop}, EffLe (effectsList es) b S →
      ∀ j ∈ BExpr.lowerList es, InstrB b S j
  | [], _, _, j, hj => by simp at hj
  | e :: es, S, h, j, hj => by
    have h' : EffLe ((effects e).merge (effectsList es)) b S := h
    obtain ⟨he, hes⟩ := h'.merge
    simp only [BExpr.lowerList_cons, List.mem_append] at hj
    rcases hj with hj | hj
    · exact instrB_lower e he j hj
    · exact instrB_lowerList es hes j hj
end

/-- The code of a configuration running `es` is within the budget of its effects. -/
theorem admsB_code {b : Bud} {S : Nat → Prop} {es : List BExpr}
    (h : EffLe (effectsList es) b S) {H : Type} (s : Store H) (f : Frame) (vs : List Val) :
    AdmsB b S (codeConfig s f vs es).code := by
  simp only [codeConfig, AdmsB_append, AdmsB_vals, true_and, AdmsB_expression]
  exact instrB_lowerList es h

/-- The fields of removable effects. -/
theorem removable_fields {e : Effects} (h : e.removable false = true) :
    e.any = false ∧ e.localsWritten = [] ∧ e.globalsWritten = [] ∧ e.calls = false ∧
      e.branchesOut = false ∧ e.breakTargets = [] ∧ e.mayNotReturn = false ∧ e.trap = false ∧
      e.implicitTrap = false := by
  simp_all [Effects.removable, Effects.writes]

mutual
/-- A syntactically bottom tree lowers to code containing a bottom instruction. -/
theorem instrBot_of_isBot : ∀ e : BExpr, e.isBot = true → ∃ j ∈ e.lower, InstrBot j
  | .op i args, h => by
    simp only [BExpr.isBot, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨j, hj, hb⟩ := instrBot_of_listBot args h
      exact ⟨j, by simp [hj], hb⟩
    · exact ⟨i, by simp, .flat h⟩
  | .block _ body, h => by
    simp only [BExpr.isBot, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    obtain ⟨j, hj, hb⟩ := instrBot_of_listBot body h.1
    exact ⟨_, List.mem_singleton_self _, .block hj hb h.2⟩
  | .loop _ body, h => by
    simp only [BExpr.isBot] at h
    obtain ⟨j, hj, hb⟩ := instrBot_of_listBot body h
    exact ⟨_, List.mem_singleton_self _, .loop hj hb⟩
  | .if_ bt c t e, h => by
    simp only [BExpr.isBot, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at h
    rcases h with h | ⟨⟨⟨ht, he⟩, h0t⟩, h0e⟩
    · obtain ⟨j, hj, hb⟩ := instrBot_of_listBot c h
      exact ⟨j, by simp [BExpr.lower, hj], hb⟩
    · obtain ⟨j, hj, hb⟩ := instrBot_of_listBot t ht
      obtain ⟨k, hk, hc⟩ := instrBot_of_listBot e he
      exact ⟨.if_ bt (BExpr.lowerList t) (BExpr.lowerList e), by simp [BExpr.lower],
        .if_ hj hb hk hc h0t h0e⟩
  | .tryTable _ _ _, h => by simp [BExpr.isBot] at h
/-- `instrBot_of_isBot` on sequences. -/
theorem instrBot_of_listBot : ∀ es : List BExpr, BExpr.listBot es = true →
    ∃ j ∈ BExpr.lowerList es, InstrBot j
  | [], h => by simp [BExpr.listBot] at h
  | e :: es, h => by
    simp only [BExpr.listBot, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨j, hj, hb⟩ := instrBot_of_isBot e h
      exact ⟨j, by simp [hj], hb⟩
    · obtain ⟨j, hj, hb⟩ := instrBot_of_listBot es h
      exact ⟨j, by simp [hj], hb⟩
end

/-! ## Soundness -/

/-- Code consisting of statements only: no branches out, no calls, no loops. -/
def StraightLine (es : List BExpr) : Prop :=
  let e := effectsList es
  e.any = false ∧ e.calls = false ∧ e.branchesOut = false ∧ e.breakTargets = [] ∧
    e.mayNotReturn = false

/-- **S1.** Removable typed code computes values without touching the store or
the frame, in host-free steps. -/
theorem effects_pure_run {P : Profile} {C : Context} {it : InstrType} {es : List BExpr}
    (hrem : (effectsList es).removable false = true) (hok : SeqOk C es it)
    {H : Type} {s : Store H} {f : Frame} {vs : List Val} (hfit : Fits C it s f vs) :
    ∃ ws, Steps P closedHost (codeConfig s f vs es) ⟨s, f, vals ws⟩ := by
  obtain ⟨hs, hf, hv⟩ := hfit
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := removable_fields hrem
  exact pure_run (b := budOf (effectsList es)) (S := (· ∈ (effectsList es).breakTargets))
    (by simp [budOf, h4]) (by simp [budOf, h7]) (by simp [budOf, h4, h8, h9])
    (by simp [budOf, h5]) (by simp [h6]) (by simp [budOf, h2]) (by simp [budOf, h3]) hok
    (instrB_lowerList es (effLe_budOf h1)) hs hf hv

/-- **S2 (locals).** A local not in `localsWritten` is unchanged along every partial
run (calls run in their own frames). -/
theorem effects_frame_local {P : Profile} {es : List BExpr} (hany : (effectsList es).any = false)
    {x : Nat} (hx : x ∉ (effectsList es).localsWritten)
    {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {vs : List Val} {c : Config H}
    (run : Steps P host (codeConfig s f vs es) c) :
    c.frame.locals[x]? = f.locals[x]? :=
  (Steps.bud run (admsB_code (effLe_budOf hany) s f vs)).2.2.1 x hx

/-- **S2 (globals).** A global not in `globalsWritten` is unchanged along every partial
run of call-free code, provided no other global index of the module refers to the
same global instance. -/
-- FLAG(statement-change): added `hal` (no other index of `f.module.globals` aliases
-- address `a`). Without it the statement is false: a module may import the same global
-- twice, and a `global.set` through the other index changes it
-- (`effects_frame_global_alias_cex`).
theorem effects_frame_global {P : Profile} {es : List BExpr} (hany : (effectsList es).any = false)
    (hcalls : (effectsList es).calls = false) {g a : Nat}
    (hg : g ∉ (effectsList es).globalsWritten)
    {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {vs : List Val} {c : Config H}
    (ha : f.module.globals[g]? = some a) (hal : ∀ g', f.module.globals[g']? = some a → g' = g)
    (run : Steps P host (codeConfig s f vs es) c) :
    (c.store.globals[a]?).map GlobalInst.value = (s.globals[a]?).map GlobalInst.value := by
  have _ := ha
  exact (Steps.bud run (admsB_code (effLe_budOf hany) s f vs)).2.2.2 (by simp [budOf, hcalls]) a
    (fun g' hg' => by rw [hal g' hg']; exact hg)

/-- The statement of `effects_frame_global` without the aliasing hypothesis is false:
global indices `0` and `1` of the module both refer to address `0`, and
`global.set 1` changes the global read through index `0`. -/
theorem effects_frame_global_alias_cex :
    ¬ ∀ (es : List BExpr) (s : Store Unit) (f : Frame) (g a : Nat) (c : Config Unit),
      (effectsList es).any = false → (effectsList es).calls = false →
      g ∉ (effectsList es).globalsWritten → f.module.globals[g]? = some a →
      Steps (Profile.spec) closedHost (codeConfig s f [] es) c →
      (c.store.globals[a]?).map GlobalInst.value = (s.globals[a]?).map GlobalInst.value := by
  intro h
  have hstep : Step (Profile.spec) closedHost
      (codeConfig ({ globals := [⟨⟨.var, .num (.int .i32)⟩, Val.i32 0⟩] } : Store Unit)
        { module := { globals := [0, 0] } }
        [] [.op (.globalSet ⟨⟨1, by decide⟩⟩) [.op (.intConst .i32 5) []]])
      ⟨({ globals := [⟨⟨.var, .num (.int .i32)⟩, Val.i32 0⟩] } : Store Unit).setGlobal 0
        (Val.i32 5), { module := { globals := [0, 0] } }, []⟩ :=
    Step.variable (VariableStep.globalSet (x := ⟨⟨1, by decide⟩⟩) (a := 0)
      (g := ⟨⟨.var, .num (.int .i32)⟩, Val.i32 0⟩) (v := Val.i32 5) rfl)
  have := h _ _ _ 0 0 _ (by decide) (by decide) (by decide) rfl (.single hstep)
  exact absurd this (by decide)

/-- **Control (branches).** A branch reaching the top of the sequence targets a
label in `breakTargets`. -/
theorem effects_control_br {P : Profile} {es : List BExpr} (hany : (effectsList es).any = false)
    {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {vs ws : List Val}
    {c : Config H} {l : LabelIdx} {junk : List Admin}
    (run : Steps P host (codeConfig s f vs es) c)
    (hc : c.code = vals ws ++ .plain (.br l) :: junk) :
    l.toNat ∈ (effectsList es).breakTargets := by
  have hl := Steps.admsLab run (AdmsB.lab (admsB_code (effLe_budOf hany) s f vs))
  rw [hc] at hl
  exact AdmsLab_mem hl (a := .plain (.br l)) (by simp) l.toNat (by simp)

/-- **Control (traps).** Trapping code is flagged. -/
theorem effects_control_trap {P : Profile} {es : List BExpr} (hany : (effectsList es).any = false)
    (hcalls : (effectsList es).calls = false)
    {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {vs : List Val}
    {c : Config H} {junk : List Admin}
    (run : Steps P host (codeConfig s f vs es) c) (hc : c.code = .trap :: junk) :
    (effectsList es).trap = true ∨ (effectsList es).implicitTrap = true := by
  have hb := (Steps.bud run (admsB_code (effLe_budOf hany) s f vs)).1
  rw [hc] at hb
  have ht := AdmsB_mem hb (a := .trap) (by simp)
  simpa [budOf, hcalls] using ht

/-- **Control (divergence).** Diverging code is flagged. -/
theorem effects_control_diverge {P : Profile} {es : List BExpr}
    (hany : (effectsList es).any = false)
    {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {vs : List Val}
    (hd : Diverges P host (codeConfig s f vs es)) :
    (effectsList es).mayNotReturn = true ∨ (effectsList es).calls = true := by
  by_contra hne
  simp only [not_or, Bool.not_eq_true] at hne
  exact not_diverges_bud (b := budOf (effectsList es)) (S := (· ∈ (effectsList es).breakTargets))
    (by simp [budOf, hne.2]) (by simp [budOf, hne.1]) _ _ (Nat.lt_succ_self _)
    (admsB_code (effLe_budOf hany) s f vs) hd

/-- **Bottom is semantic.** A tree with `isBot` never falls through: no run of it
reaches plain values (it traps, branches, returns or diverges). -/
theorem isBot_sound {P : Profile} {e : BExpr} (hb : e.isBot = true)
    {H : Type} {host : HostSemantics H} {s s' : Store H} {f f' : Frame} {vs ws : List Val} :
    ¬ Steps P host (codeConfig s f vs [e]) ⟨s', f', vals ws⟩ := by
  intro hrun
  obtain ⟨j, hj, hbj⟩ := instrBot_of_isBot e hb
  have h0 : AdmsBot (codeConfig s f vs [e]).code := by
    simp only [codeConfig, AdmsBot_append, AdmsBot_vals, false_or, AdmsBot_expression,
      BExpr.lowerList_singleton]
    exact ⟨j, hj, hbj⟩
  exact AdmsBot_vals ws (Steps.admsBot hrun h0)

/-! ## The ignoreImplicitTraps example

The refutation `iit_hoist_unsound` is in `Commute.lean`. -/

/-- `i32.div_u 1 0`: an implicit trap. -/
def divByZero : BExpr :=
  .op (.intBinOp .i32 (.div .unsigned)) [.op (.intConst .i32 1) [], .op (.intConst .i32 0) []]

/-- `if (local.get 0) (drop (i32.div_u 1 0))`. -/
def iitSource : List BExpr :=
  [.if_ .empty [.op (.localGet ⟨⟨0, by decide⟩⟩) []] [.op .drop [divByZero]] []]

/-- The `ignoreImplicitTraps` hoist: the dropped division moves before the `if`. -/
def iitTarget : List BExpr :=
  [.op .drop [divByZero], .if_ .empty [.op (.localGet ⟨⟨0, by decide⟩⟩) []] [] []]

/-- One i32 local. -/
def iitCtx : Context := { locals := [⟨.set, .num (.int .i32)⟩] }

/-- Under `ignoreImplicitTraps` the hoisted code looks removable and unordered
with the condition. -/
theorem iit_effects : (effectsIIT (.op .drop [divByZero])).removable false = true := by
  decide

end Silmaril.Wasm.Binaryen
