module

public import Silmaril.Wasm.FnInst.Ground.Forced.Defs
public import Silmaril.Proofs.Wasm.FnInst.Ground.Sim
public import Silmaril.Wasm.Binaryen.Deferred.Thms

@[expose] public section

/-! # The deferred bridge: equal runs of local code give a deferred simulation

`wDeferredSim`: `DeferredBaseSim P F GWI GW` (`Silmaril.Wasm.Binaryen.Deferred`) at every
numerical profile `P` and function relation `F`. At the left side's first non-constant
step:

* `local.get` or `local.set` (`commit_matched`): the right side runs its whole code
  (`run_steps`), and the left side completes its own run as a chain of forced steps
  (`run_normalizes`), so both end in the same frame with the same values;
* `local.tee` (`tee_matched`): its first step is the expansion `v; v; local.set x`, which
  keeps the frame; the right side stutters and the pair continues with `local.set`.

`exportRefines_of_goodW`: modules whose bodies differ by `GoodW` pairs refine each other's
exports under the closed host, at every numerical profile.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.Deferred

variable {H : Type} {P : Profile}

theorem kvalsW_eq (ks : List (BitVec 32)) : kvalsW ks = kvals ks := rfl

/-! ## Local code runs as a forced chain -/

/-- A constant is already a value: no step. -/
theorem const_normalizes {k : BitVec 32} {s : Store H} {f f' : Frame} {X Y : List Val}
    (h : step1 (.const k) f X = some (f', Y)) (rest : List Admin) :
    Normalizes ⟨s, f, vals X.reverse ++ .plain (GInstr.const k).lower :: rest⟩
      ⟨s, f', vals Y.reverse ++ rest⟩ := by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have e : vals X.reverse ++ Admin.plain (GInstr.const k).lower :: rest =
      vals (Val.i32 k :: X).reverse ++ rest := by
    simp [vals, GInstr.lower, Val.toAdmin, Val.i32]
  rw [e]
  exact .refl _

/-- `local.tee` is two forced steps: the expansion and the store. -/
theorem tee_normalizes {x : LocalIdx} {s : Store H} {f f' : Frame} {X Y : List Val}
    (h : step1 (.localTee x) f X = some (f', Y)) (rest : List Admin) :
    Normalizes ⟨s, f, vals X.reverse ++ .plain (GInstr.localTee x).lower :: rest⟩
      ⟨s, f', vals Y.reverse ++ rest⟩ := by
  obtain ⟨v, X', rfl, rfl, hx, rfl⟩ := step1_tee_inv h
  have h₁ := Forced.tee s f X'.reverse v x rest
  have h₂ := Forced.set s f (X'.reverse ++ [v]) v x rest hx
  have e : vals (X'.reverse ++ [v]) ++ [v.toAdmin, .plain (.localSet x)] ++ rest =
      vals X'.reverse ++ [v.toAdmin, v.toAdmin, .plain (.localSet x)] ++ rest := by
    simp [vals]
  rw [e] at h₂
  simpa [GInstr.lower, vals] using Normalizes.cons h₁ (Normalizes.single h₂)

/-- One local instruction of the interpreter is a chain of forced steps. -/
theorem step1_normalizes {i : GInstr} (hi : i.loc = true) {s : Store H} {f f' : Frame}
    {X Y : List Val} (h : step1 i f X = some (f', Y)) (rest : List Admin) :
    Normalizes ⟨s, f, vals X.reverse ++ .plain i.lower :: rest⟩ ⟨s, f', vals Y.reverse ++ rest⟩ := by
  cases i with
  | const k => exact const_normalizes h rest
  | localGet x =>
    obtain ⟨v, hv, rfl, rfl⟩ := step1_get_inv h
    simpa [GInstr.lower, vals] using Normalizes.single (Forced.get s f X.reverse x v rest hv)
  | localSet x =>
    obtain ⟨v, rfl, hx, rfl⟩ := step1_set_inv h
    simpa [GInstr.lower, vals] using Normalizes.single (Forced.set s f Y.reverse v x rest hx)
  | localTee x => exact tee_normalizes h rest
  | bin _ | eqz | drop | nop => cases hi

/-- **A run of local code is a chain of forced steps.** -/
theorem run_normalizes {c : List GInstr} (hc : ∀ j ∈ c, j.loc = true) {s : Store H}
    {f f' : Frame} {X Y : List Val} (h : run c f X = some (f', Y)) (rest : List Admin) :
    Normalizes ⟨s, f, vals X.reverse ++ expression (lower c) ++ rest⟩
      ⟨s, f', vals Y.reverse ++ rest⟩ := by
  induction c generalizing f X with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simpa [lower, expression] using Normalizes.refl (H := H) ⟨s, f, vals X.reverse ++ rest⟩
  | cons i c ih =>
    obtain ⟨⟨f₁, X₁⟩, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    have hs := step1_normalizes (s := s) (hc i (by simp)) h₁ (expression (lower c) ++ rest)
    have e : vals X.reverse ++ expression (lower (i :: c)) ++ rest =
        vals X.reverse ++ .plain i.lower :: (expression (lower c) ++ rest) := by
      simp [lower, expression]
    rw [e]
    exact hs.trans (by simpa using ih (fun j hj => hc j (by simp [hj])) h₂)

/-! ## Inverting the first step -/

/-- The machine's step at `local.set`. -/
theorem set_inv {s : Store H} {f : Frame} {W : List Val} {x : LocalIdx} {rest : List Admin}
    {c' : Config H} (h : Step P closedHost ⟨s, f, vals W ++ .plain (.localSet x) :: rest⟩ c') :
    ∃ W₀ v, W = W₀ ++ [v] ∧ x.toNat < f.locals.length ∧
      c' = ⟨s, f.setLocal x v, vals W₀ ++ rest⟩ := by
  obtain ⟨vs, args, c₀, rfl, hh, rfl⟩ := GuardSim.head_inv rfl (by simp) (by simp) h
  obtain ⟨v, rfl, hx, rfl⟩ := SimplifyLocalsLite.head_localSet hh
  exact ⟨vs, v, rfl, hx, by simp⟩

/-- The machine's step at `local.tee`: the expansion. -/
theorem tee_inv {s : Store H} {f : Frame} {W : List Val} {x : LocalIdx} {rest : List Admin}
    {c' : Config H} (h : Step P closedHost ⟨s, f, vals W ++ .plain (.localTee x) :: rest⟩ c') :
    ∃ W₀ v, W = W₀ ++ [v] ∧
      c' = ⟨s, f, vals (W₀ ++ [v, v]) ++ .plain (.localSet x) :: rest⟩ := by
  obtain ⟨vs, args, c₀, rfl, hh, rfl⟩ := GuardSim.head_inv rfl (by simp) (by simp) h
  obtain ⟨v, rfl, rfl⟩ := SimplifyLocalsLite.head_localTee hh
  exact ⟨vs, v, rfl, by simp [vals]⟩

/-- `local.set` after a duplicated value is `local.tee`. -/
theorem step1_set_tee (x : LocalIdx) (f : Frame) (v : Val) (X : List Val) :
    step1 (.localSet x) f (v :: v :: X) = step1 (.localTee x) f (v :: X) := rfl

/-! ## The step law -/

theorem locStk_cons {i : GInstr} {a₁ : List GInstr} (hi : i.loc = true) (h : LocStk a₁) :
    LocStk (i :: a₁) := by
  obtain ⟨l, p, rfl, hl, hp⟩ := h
  refine ⟨i :: l, p, rfl, fun j hj => ?_, hp⟩
  rcases List.mem_cons.mp hj with rfl | hj
  · exact hi
  · exact hl j hj

theorem lower_append (c d : List GInstr) :
    expression (lower (c ++ d)) = expression (lower c) ++ expression (lower d) := by
  simp [lower, expression]

/-- The shape of the conclusion of `locStk_finish`. -/
def Finished (s : Store H) (f₁ f₂ : Frame) (Y Z : List Val) (a₁ : List GInstr)
    (rest rest' : List Admin) : Prop :=
  ∃ c₁ : Config H, Normalizes ⟨s, f₁, vals Y.reverse ++ (expression (lower a₁) ++ rest)⟩ c₁ ∧
    c₁.store = s ∧ c₁.frame = f₂ ∧ AdminsRel GWI (WithCuts GW) c₁.code (vals Z.reverse ++ rest')

/-- The rest is local code (here followed by constants only): a forced chain to the values. -/
theorem loc_finish {s : Store H} {f₁ f₂ : Frame} {Y Z : List Val} {c : List GInstr}
    {rest rest' : List Admin} (hc : ∀ j ∈ c, j.loc = true) (hZ : run c f₁ Y = some (f₂, Z))
    (hrest : AdminsRel GWI (WithCuts GW) rest rest') : Finished s f₁ f₂ Y Z c rest rest' := by
  have hN := run_normalizes (s := s) hc hZ rest
  rw [List.append_assoc] at hN
  exact ⟨_, hN, rfl, rfl, (AdminsRel.vals _).append hrest⟩

/-- The stack-only rest of a run is a frame-free pair against the values it reaches. -/
theorem stk_rest_pair {f : Frame} {Y Z : List Val} {p : List GInstr}
    (hpS : ∀ j ∈ p, j.stk = true) (hop : ∃ j ∈ p, j.isConst = false)
    (hp₁ : run p f Y = some (f, Z)) :
    GW (vals Y.reverse ++ expression (lower p)) (vals Z.reverse) := by
  obtain ⟨-, hstk⟩ := run_stk hpS hp₁
  have hpr : PairRef Y.reverse p Z.reverse [] := by
    intro f₀ S res h
    have h₁ : run p f₀ (Y ++ S) = some res := by simpa using h
    rw [hstk f₀ S] at h₁
    show run [] f₀ (Z.reverse.reverse ++ S) = some res
    rw [List.reverse_reverse, ← h₁]
    rfl
  exact Or.inr ⟨_, _, _, rfl, rfl, ⟨hpS, hop⟩, hpr⟩

/-- Local code, then stack-only code that is not all constants. -/
theorem split_finish {s : Store H} {f₁ f₂ : Frame} {Y Z : List Val} {l p : List GInstr}
    {rest rest' : List Admin} (hl : ∀ j ∈ l, j.loc = true) (hpS : ∀ j ∈ p, j.stk = true)
    (hop : ∃ j ∈ p, j.isConst = false) (hZ : run (l ++ p) f₁ Y = some (f₂, Z))
    (hrest : AdminsRel GWI (WithCuts GW) rest rest') :
    Finished s f₁ f₂ Y Z (l ++ p) rest rest' := by
  have hZ' : (run l f₁ Y).bind (fun r => run p r.1 r.2) = some (f₂, Z) := by
    rw [← run_append]; exact hZ
  obtain ⟨⟨f₃, Y₃⟩, hl₁, hp₁⟩ := Option.bind_eq_some_iff.mp hZ'
  obtain ⟨rfl, -⟩ := run_stk hpS hp₁
  have hN := run_normalizes (s := s) hl hl₁ (expression (lower p) ++ rest)
  have hB := stk_rest_pair hpS hop hp₁
  rw [Finished, lower_append, List.append_assoc]
  refine ⟨_, by simpa [List.append_assoc] using hN, rfl, rfl, ?_⟩
  simpa [List.append_assoc] using (AdminsRel.base (Or.inl hB)).append hrest

/-- Constants are local code. -/
theorem loc_append_consts {l : List GInstr} (hl : ∀ j ∈ l, j.loc = true) (ks : List (BitVec 32)) :
    ∀ j ∈ l ++ ks.map GInstr.const, j.loc = true := by
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  · exact hl j hj
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hj
    rfl

/-- After the commit, the left side runs its local code as a forced chain and is left with its
stack-only rest, related (frame-free) to the values the right side has reached. -/
theorem locStk_finish {s : Store H} {f₁ f₂ : Frame} {Y Z : List Val} {a₁ : List GInstr}
    {rest rest' : List Admin} (hlp : LocStk a₁) (hZ : run a₁ f₁ Y = some (f₂, Z))
    (hrest : AdminsRel GWI (WithCuts GW) rest rest') : Finished s f₁ f₂ Y Z a₁ rest rest' := by
  obtain ⟨l, p, rfl, hl, hpS⟩ := hlp
  by_cases hop : ∃ j ∈ p, j.isConst = false
  · exact split_finish hl hpS hop hZ hrest
  · obtain ⟨ks₂, rfl⟩ := all_consts hop
    exact loc_finish (loc_append_consts hl ks₂) hZ hrest

/-- **The right side commits**: after the left side's first step at `local.get` or
`local.set`, the right side runs its whole code and the left side completes its run as a
forced chain, to the same frame and values. -/
theorem commit_matched {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f f₁ : Frame}
    {vs q r Y : List Val} {ks : List (BitVec 32)} {i : GInstr} {a₁ b : List GInstr}
    {rest rest' : List Admin} {m : Nat} (hst : StoreRel F s t)
    (hlp : LocStk a₁) (hcom : Commits q ks i a₁)
    (hp : PairRef q (ks.map GInstr.const ++ i :: a₁) r b)
    (h1 : step1 i f (vs ++ q ++ kvals ks).reverse = some (f₁, Y))
    (hrank : fwRank (vals Y.reverse ++ (expression (lower a₁) ++ rest)) < m)
    (hrest : AdminsRel GWI (WithCuts GW) rest rest') :
    DeferredMatched P F GWI GW ⟨s, f₁, vals Y.reverse ++ (expression (lower a₁) ++ rest)⟩
      ⟨t, f, vals vs ++ (vals r ++ expression (lower b)) ++ rest'⟩ m := by
  have eW : (vs ++ q ++ kvals ks).reverse = (q ++ kvalsW ks).reverse ++ vs.reverse := by
    simp [kvalsW_eq]
  obtain ⟨⟨f₂, Z⟩, hZ⟩ := Option.isSome_iff_exists.mp (hcom f vs.reverse (f₁, Y) (eW ▸ h1))
  have hA : run (ks.map GInstr.const ++ i :: a₁) f (q.reverse ++ vs.reverse) = some (f₂, Z) := by
    rw [run_consts, run_cons]
    have e : (kvals ks).reverse ++ (q.reverse ++ vs.reverse) = (vs ++ q ++ kvals ks).reverse := by
      simp
    rw [e, h1]
    exact hZ
  have hb : run b f (r.reverse ++ vs.reverse) = some (f₂, Z) := hp f vs.reverse _ hA
  have hR := run_steps (P := P) (host := closedHost) (s := t) hb rest'
  have eR : vals (r.reverse ++ vs.reverse).reverse ++ expression (lower b) ++ rest' =
      vals vs ++ (vals r ++ expression (lower b)) ++ rest' := by simp
  rw [eR] at hR
  obtain ⟨c₁, hN, hcs, hcf, hcr⟩ := locStk_finish (s := s) hlp hZ hrest
  refine ⟨c₁, ⟨t, f₂, vals Z.reverse ++ rest'⟩, hN, ?_, ⟨hcs ▸ hst, hcf, hcr⟩⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hR with he | ht
  · exact Or.inr ⟨he, hrank⟩
  · exact Or.inl ht

/-- The pair after the expansion of `local.tee`: the same right side, `local.set` next. -/
theorem tee_pair {vs q r W₀ : List Val} {v : Val} {ks : List (BitVec 32)} {x : LocalIdx}
    {a₁ b : List GInstr} (hW : vs ++ q ++ kvals ks = W₀ ++ [v])
    (hlp : LocStk a₁) (hcom : Commits q ks (.localTee x) a₁)
    (hp : PairRef q (ks.map GInstr.const ++ .localTee x :: a₁) r b) :
    WPair (W₀ ++ [v, v]) (.localSet x :: a₁) (vs ++ r) b := by
  have hW' : ∀ S, (kvals ks).reverse ++ (q.reverse ++ (vs.reverse ++ S)) =
      v :: (W₀.reverse ++ S) := by
    intro S
    have h0 : (kvals ks).reverse ++ (q.reverse ++ vs.reverse) = v :: W₀.reverse := by
      simpa using congrArg List.reverse hW
    rw [← List.append_assoc q.reverse, ← List.append_assoc, h0]
    rfl
  have hrun : ∀ f S, run (ks.map GInstr.const ++ .localTee x :: a₁) f (q.reverse ++
      (vs.reverse ++ S)) = run (.localSet x :: a₁) f ((W₀ ++ [v, v]).reverse ++ S) := by
    intro f S
    rw [run_consts, run_cons, run_cons]
    rw [hW' S]
    simp [step1_set_tee]
  refine ⟨[], .localSet x, a₁, rfl, rfl, rfl, hlp, ?_, ?_⟩
  · intro f S res h
    have h' : step1 (.localTee x) f ((q ++ kvalsW ks).reverse ++ (vs.reverse ++ S)) = some res := by
      rw [kvalsW_eq, List.reverse_append, List.append_assoc, hW' S, ← step1_set_tee]
      simpa [kvalsW] using h
    exact hcom f (vs.reverse ++ S) res h'
  · intro f S res h
    have h₁ := hp f (vs.reverse ++ S) res ((hrun f S).trans h)
    simpa using h₁

/-- **The step at `local.tee`**: the right side stutters. -/
theorem tee_matched {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {vs q r W₀ : List Val} {v : Val} {ks : List (BitVec 32)} {x : LocalIdx}
    {a₁ b : List GInstr} {rest rest' : List Admin} (hst : StoreRel F s t)
    (hW : vs ++ q ++ kvals ks = W₀ ++ [v])
    (hlp : LocStk a₁) (hcom : Commits q ks (.localTee x) a₁)
    (hp : PairRef q (ks.map GInstr.const ++ .localTee x :: a₁) r b)
    (hrest : AdminsRel GWI (WithCuts GW) rest rest') :
    DeferredMatched P F GWI GW
      ⟨s, f, vals (W₀ ++ [v, v]) ++ .plain (.localSet x) :: (expression (lower a₁) ++ rest)⟩
      ⟨t, f, vals vs ++ (vals r ++ expression (lower b)) ++ rest'⟩
      (fwRank (vals (vs ++ q ++ kvals ks) ++ .plain (GInstr.localTee x).lower ::
        (expression (lower a₁) ++ rest))) := by
  have hB : GW (vals (W₀ ++ [v, v]) ++ expression (lower (.localSet x :: a₁)))
      (vals (vs ++ r) ++ expression (lower b)) :=
    Or.inl ⟨_, _, _, _, rfl, rfl, tee_pair hW hlp hcom hp⟩
  have eL : vals (W₀ ++ [v, v]) ++ .plain (.localSet x) :: (expression (lower a₁) ++ rest) =
      vals (W₀ ++ [v, v]) ++ expression (lower (.localSet x :: a₁)) ++ rest := by
    simp [lower, expression, GInstr.lower]
  have eR : vals vs ++ (vals r ++ expression (lower b)) ++ rest' =
      vals (vs ++ r) ++ expression (lower b) ++ rest' := by simp
  refine ⟨_, _, .refl _, Or.inr ⟨rfl, ?_⟩, ⟨hst, rfl, ?_⟩⟩
  · rw [hW]
    simp [fwAdminRank, GInstr.lower]
    omega
  · simp only
    rw [eL, eR]
    exact (AdminsRel.base (Or.inl hB)).append hrest

/-- A stack-only step never grows the stack. -/
theorem stk_len {i : GInstr} (hi : i.stk = true) (hc : i.isConst = false) {f f' : Frame}
    {X Y : List Val} (h : step1 i f X = some (f', Y)) : Y.length ≤ X.length := by
  obtain ⟨-, h'⟩ := step1_stk_inv hi h
  cases i with
  | const _ => cases hc
  | localGet _ | localSet _ | localTee _ => cases hi
  | bin _ => obtain ⟨_, _, _, rfl, rfl⟩ := stepS_bin_inv h'; simp
  | eqz => obtain ⟨_, _, rfl, rfl⟩ := stepS_eqz_inv h'; simp
  | drop => obtain ⟨_, rfl⟩ := stepS_drop_inv h'; simp
  | nop => obtain rfl := Option.some.inj h'; simp

/-- Some frame (stack-only code ignores it). -/
def frame₀ : Frame := ⟨[], {}⟩

/-- The code reached by a stack-only step is related to the right side's values. -/
theorem s_code {vs r Y : List Val} {a₁ : List GInstr} {rest rest' : List Admin}
    (ha₁ : ∀ j ∈ a₁, j.stk = true) (hp' : PairRef Y.reverse a₁ (vs ++ r) [])
    (hrest : AdminsRel GWI (WithCuts GW) rest rest') :
    AdminsRel GWI (WithCuts GW) (vals Y.reverse ++ (expression (lower a₁) ++ rest))
      (vals vs ++ vals r ++ rest') := by
  have eR : vals vs ++ vals r ++ rest' = vals (vs ++ r) ++ rest' := by simp
  rw [eR]
  by_cases hop : ∃ j ∈ a₁, j.isConst = false
  · have hB : GW (vals Y.reverse ++ expression (lower a₁)) (vals (vs ++ r)) :=
      Or.inr ⟨_, _, _, rfl, rfl, ⟨ha₁, hop⟩, hp'⟩
    simpa [List.append_assoc] using (AdminsRel.base (Or.inl hB)).append hrest
  · obtain ⟨ks₂, rfl⟩ := all_consts hop
    have hb : run [] frame₀ (vs ++ r).reverse =
        some (frame₀, (kvals ks₂).reverse ++ Y) := by
      simpa using hp' _ [] _ (by simpa using run_consts_only ks₂ frame₀ Y)
    have e : (vs ++ r).reverse = (kvals ks₂).reverse ++ Y := (Prod.mk.inj (Option.some.inj hb)).2
    have e₂ : vals Y.reverse ++ (expression (lower (ks₂.map GInstr.const)) ++ rest) =
        vals (vs ++ r) ++ rest := by
      rw [expression_consts, ← List.append_assoc, ← vals_append]
      congr 2
      simpa [kvals] using (congrArg List.reverse e).symm
    rw [e₂]
    exact (AdminsRel.vals _).append hrest

/-- **The step law for a stack-only rest**: the right side has its values and stutters. -/
theorem s_step {F : FuncInst H → FuncInst H → Prop} {s t s' : Store H} {f f' : Frame}
    {vs q r : List Val} {a : List GInstr} {rest rest' es' : List Admin} (hst : StoreRel F s t)
    (ha : StkOp a) (hp : PairRef q a r []) (hrest : AdminsRel GWI (WithCuts GW) rest rest')
    (hstep : Step P closedHost ⟨s, f, vals vs ++ (vals q ++ expression (lower a)) ++ rest⟩
      ⟨s', f', es'⟩) :
    DeferredMatched P F GWI GW ⟨s', f', es'⟩ ⟨t, f, vals vs ++ vals r ++ rest'⟩
      (fwRank (vals vs ++ (vals q ++ expression (lower a)) ++ rest)) := by
  obtain ⟨ks, i, a₁, rfl, hi⟩ := split_op ha.2
  have hiS : i.stk = true := ha.1 i (by simp)
  rw [code_split] at hstep ⊢
  obtain ⟨Y, hY, hc⟩ := step_inv ⟨Or.inl hiS, hi⟩ hstep
  cases hc
  have hp' : PairRef Y.reverse a₁ (vs ++ r) [] := pairRef_step hiS hp hY
  have hlen : Y.length ≤ (vs ++ q ++ kvals ks).reverse.length := stk_len hiS hi hY
  have hpos : 0 < fwAdminRank (.plain i.lower) := fwAdminRank_pos _
  have hrank : fwRank (vals Y.reverse ++ (expression (lower a₁) ++ rest)) <
      fwRank (vals (vs ++ q ++ kvals ks) ++ .plain i.lower :: (expression (lower a₁) ++ rest)) := by
    simp only [fwRank_append, fwRank_vals, fwRank_cons, List.length_reverse] at hlen ⊢
    omega
  have hcode := s_code (fun j hj => ha.1 j (by simp [hj])) hp' hrest
  exact ⟨_, _, .refl _, Or.inr ⟨rfl, hrank⟩, ⟨hst, rfl, hcode⟩⟩

/-- The step at `local.get`: the right side commits. -/
theorem get_matched {F : FuncInst H → FuncInst H → Prop} {s t s' : Store H} {f f' : Frame}
    {vs q r : List Val} {ks : List (BitVec 32)} {x₀ : LocalIdx} {a₁ b : List GInstr}
    {rest rest' es' : List Admin} (hst : StoreRel F s t) (hlp : LocStk a₁)
    (hcom : Commits q ks (.localGet x₀) a₁)
    (hp : PairRef q (ks.map GInstr.const ++ .localGet x₀ :: a₁) r b)
    (hrest : AdminsRel GWI (WithCuts GW) rest rest')
    (hstep : Step P closedHost ⟨s, f, vals (vs ++ q ++ kvals ks) ++
      .plain (GInstr.localGet x₀).lower :: (expression (lower a₁) ++ rest)⟩ ⟨s', f', es'⟩) :
    DeferredMatched P F GWI GW ⟨s', f', es'⟩
      ⟨t, f, vals vs ++ (vals r ++ expression (lower b)) ++ rest'⟩
      (fwRank (vals (vs ++ q ++ kvals ks) ++ .plain (GInstr.localGet x₀).lower ::
        (expression (lower a₁) ++ rest))) := by
  obtain ⟨Y, hY, hc⟩ := step_inv ⟨Or.inr ⟨x₀, rfl⟩, rfl⟩ hstep
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hc
  refine commit_matched hst hlp hcom hp hY ?_ hrest
  obtain ⟨v, -, -, rfl⟩ := step1_get_inv hY
  simp [fwAdminRank, GInstr.lower]

/-- The step at `local.set`: the right side commits. -/
theorem set_matched {F : FuncInst H → FuncInst H → Prop} {s t s' : Store H} {f f' : Frame}
    {vs q r : List Val} {ks : List (BitVec 32)} {x₀ : LocalIdx} {a₁ b : List GInstr}
    {rest rest' es' : List Admin} (hst : StoreRel F s t) (hlp : LocStk a₁)
    (hcom : Commits q ks (.localSet x₀) a₁)
    (hp : PairRef q (ks.map GInstr.const ++ .localSet x₀ :: a₁) r b)
    (hrest : AdminsRel GWI (WithCuts GW) rest rest')
    (hstep : Step P closedHost ⟨s, f, vals (vs ++ q ++ kvals ks) ++
      .plain (GInstr.localSet x₀).lower :: (expression (lower a₁) ++ rest)⟩ ⟨s', f', es'⟩) :
    DeferredMatched P F GWI GW ⟨s', f', es'⟩
      ⟨t, f, vals vs ++ (vals r ++ expression (lower b)) ++ rest'⟩
      (fwRank (vals (vs ++ q ++ kvals ks) ++ .plain (GInstr.localSet x₀).lower ::
        (expression (lower a₁) ++ rest))) := by
  obtain ⟨W₀, v, hW, hx, hc⟩ := set_inv hstep
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hc
  have hY : step1 (.localSet x₀) f (vs ++ q ++ kvals ks).reverse =
      some (f.setLocal x₀ v, W₀.reverse) := by
    rw [hW]
    simp [step1, hx]
  have hrank : fwRank (vals W₀.reverse.reverse ++ (expression (lower a₁) ++ rest)) <
      fwRank (vals (vs ++ q ++ kvals ks) ++ .plain (GInstr.localSet x₀).lower ::
        (expression (lower a₁) ++ rest)) := by
    rw [hW]
    simp [fwAdminRank, GInstr.lower]
    omega
  simpa using commit_matched hst hlp hcom hp hY hrank hrest

/-- **The step law of the deferred bridge.** -/
theorem w_step {F : FuncInst H → FuncInst H → Prop} {s t s' : Store H} {f f' : Frame}
    {vs : List Val} {x y rest rest' es' : List Admin} (hst : StoreRel F s t) (hxy : GW x y)
    (hrest : AdminsRel GWI (WithCuts GW) rest rest')
    (hstep : Step P closedHost ⟨s, f, vals vs ++ x ++ rest⟩ ⟨s', f', es'⟩) :
    DeferredMatched P F GWI GW ⟨s', f', es'⟩ ⟨t, f, vals vs ++ y ++ rest'⟩
      (fwRank (vals vs ++ x ++ rest)) := by
  rcases hxy with ⟨q, a, r, b, rfl, rfl, ks, i, a₁, rfl, hi, hiL, hlp, hcom, hp⟩ |
    ⟨q, a, r, rfl, rfl, ha, hp⟩
  · rw [code_split vs q ks i a₁ rest] at hstep ⊢
    cases i with
    | localGet x₀ => exact get_matched hst hlp hcom hp hrest hstep
    | localSet x₀ => exact set_matched hst hlp hcom hp hrest hstep
    | localTee x₀ =>
      obtain ⟨W₀, v, hW, hc⟩ := tee_inv hstep
      obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hc
      exact tee_matched hst hW hlp hcom hp hrest
    | const _ => cases hi
    | _ => exact absurd hiL (by simp [GInstr.loc])
  · exact s_step hst ha hp hrest hstep

/-! ## The deferred simulation -/

/-- Every left side has a non-value head that is not an exit. -/
theorem gw_head {x y : List Admin} (h : GW x y) (vs : List Val) :
    ∃ (W : List Val) (i : GInstr) (R : List Admin), i.isConst = false ∧
      vals vs ++ x = vals W ++ .plain i.lower :: R := by
  rcases h with ⟨q, a, r, b, rfl, -, ks, i, a₁, rfl, hi, -⟩ | ⟨q, a, r, rfl, -, ha, -⟩
  · exact ⟨vs ++ q ++ kvals ks, i, expression (lower a₁), hi,
      by simpa using code_split vs q ks i a₁ []⟩
  · obtain ⟨ks, i, a₁, rfl, hi⟩ := split_op ha.2
    exact ⟨vs ++ q ++ kvals ks, i, expression (lower a₁), hi,
      by simpa using code_split vs q ks i a₁ []⟩

/-- **The deferred bridge**: `GoodW` pairs satisfy the base laws of Silmaril's deferred
simulation, at every numerical profile, for every function relation. -/
theorem wDeferredSim {F : FuncInst H → FuncInst H → Prop} : DeferredBaseSim P F GWI GW where
  facts := {
    src := by
      rintro x y ⟨a, b, hg, rfl, rfl⟩
      exact Or.inl ⟨[], a, [], b, rfl, rfl, hg⟩
    exit := by
      intro s t f vs us x y k j hst hxy hk he
      obtain ⟨W, i, R, hi, hW⟩ := gw_head hxy vs
      exact absurd (hW.symm.trans he) (fun h => not_exit_lower hi hk h)
    values := by
      intro s t f vs us x y hst hxy hx
      exfalso
      obtain ⟨W, i, R, hi, hW⟩ := gw_head hxy vs
      have hm : Admin.plain i.lower ∈ vals (vs ++ us) := by
        rw [vals_append, ← hx, hW]
        simp
      exact SingleThreaded.Det.mem_vals hm (lower_val hi) }
  step := fun hst hxy hrest hstep => w_step hst hxy hrest hstep

/-- **The deferred transfer**: bodies differing by `GoodW` pairs give export refinement
under the closed host, at every numerical profile. -/
theorem exportRefines_of_goodW {m m' : Module} (hrel : ModuleBodiesRel GWI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportRefines (· = ·) P (closedHost (H := H)) m m' :=
  deferred_exportRefines_of_bodiesRel wDeferredSim hrel hm hm'

end Silmaril.Wasm.FnInst.Ground
