module

public import Silmaril.Wasm.Binaryen.CodeSimModule
public import Silmaril.Wasm.Binaryen.UniformWf
public import Silmaril.Wasm.Binaryen.HostCode
public import Silmaril.Wasm.Binaryen.Pass.Vacuum
public import Silmaril.Wasm.Binaryen.Pass.VacuumLite

@[expose] public section

/-! # Anchored vacuum as a code simulation

`VacuumLite.vacuumLite` (`Pass/VacuumLite.lean`) removes `nop` and `drop` of a constant
when an **anchor** follows: constants, then a flat non-constant instruction `c` other
than `throw_ref`. The base pairs are

* source `vacBI`: `l ++ [c]` ~ `l' ++ [c]`, where `l` interleaves constants with removable
  units (`nop`, `const; drop`), `l'` keeps the constants, and `l` has a unit (`SegI`);
* runtime `vacB`: the same over administrative instructions (`SegA`), values for the
  constants.

Both directions are `BaseSim` instances (`Sim/Closure/Basic.lean`), for every profile,
store relation and (in the reverse direction) host respecting it:

* `vacBaseSim`: the left side has the units; it runs one away while the right side
  stutters (the code shrinks);
* `vacBaseSim_flip`: the right side has the units; when the left side steps its anchor,
  the right side first runs its units away (`SegA.run`) and then takes the matching step
  of the anchor (`Step.match_storeRel`). Without an anchor the reverse step obligation
  fails: on `[]` ~ `[nop]` the left side may step in any related suffix.

`exportEquiv_vacuumLite` lifts the two simulations to modules with related bodies
(`exportRefines_of_bodiesRel`, `CodeSimModule.lean`), and `vacL_rel` relates every
body to its vacuumed form. Typing is a `TyRepl` chain (`vacL_typed`).
-/

namespace Silmaril.Wasm.Binaryen.VacuumLite

open Execution.Core Execution.Core.Sim Validation Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Base relations -/

theorem constInstr_val {k : Instr} (h : constInstr k = true) :
    ∃ v : Val, Admin.plain k = v.toAdmin := by
  cases k <;> simp [constInstr] at h
  all_goals exact ⟨_, Admin.eq_of_val? rfl⟩

theorem anchorInstr_val {c : Instr} (h : anchorInstr c = true) : (Admin.plain c).val? = none := by
  cases c <;> simp_all [anchorInstr, constInstr, Admin.val?]

theorem anchorInstr_ne {c : Instr} (h : anchorInstr c = true) : c ≠ .throwRef := by
  rintro rfl
  simp [anchorInstr, constInstr] at h

/-- Source segments: constants and removable units on the left, the constants on the
right. -/
inductive SegI : List Instr → List Instr → Prop where
  | nil : SegI [] []
  | const {k : Instr} {l l' : List Instr} : constInstr k = true → SegI l l' → SegI (k :: l) (k :: l')
  | nop {l l' : List Instr} : SegI l l' → SegI (.nop :: l) l'
  | drop {k : Instr} {l l' : List Instr} : constInstr k = true → SegI l l' →
      SegI (k :: .drop :: l) l'

/-- Source base pairs: a segment with at least one unit, then the same anchor. -/
def vacBI (x y : List Instr) : Prop :=
  ∃ (l l' : List Instr) (c : Instr), SegI l l' ∧ l ≠ l' ∧ anchorInstr c = true ∧
    x = l ++ [c] ∧ y = l' ++ [c]

/-- Runtime segments: values and removable units on the left, the values on the right. -/
inductive SegA : List Admin → List Admin → Prop where
  | nil : SegA [] []
  | val (v : Val) {l l' : List Admin} : SegA l l' → SegA (v.toAdmin :: l) (v.toAdmin :: l')
  | nop {l l' : List Admin} : SegA l l' → SegA (.plain .nop :: l) l'
  | drop (v : Val) {l l' : List Admin} : SegA l l' → SegA (v.toAdmin :: .plain .drop :: l) l'

/-- Runtime base pairs: a segment with at least one unit, then the same anchor, a
non-value that is neither `trap` nor `throw_ref`. -/
def vacB (x y : List Admin) : Prop :=
  ∃ (l l' : List Admin) (c : Admin), SegA l l' ∧ l ≠ l' ∧ c.val? = none ∧ c ≠ .trap ∧
    c ≠ .plain .throwRef ∧ x = l ++ [c] ∧ y = l' ++ [c]

theorem SegI.length_le {l l' : List Instr} (h : SegI l l') : l'.length ≤ l.length := by
  induction h <;> simp <;> omega

theorem SegI.of_const : ∀ {l : List Instr}, (∀ k ∈ l, constInstr k = true) → SegI l l
  | [], _ => .nil
  | k :: l, h => .const (h k (by simp)) (SegI.of_const fun k hk => h k (by simp [hk]))

theorem SegI.const_append : ∀ {p : List Instr} {l l' : List Instr},
    (∀ k ∈ p, constInstr k = true) → SegI l l' → SegI (p ++ l) (p ++ l')
  | [], _, _, _, h => h
  | k :: p, _, _, hp, h =>
    .const (hp k (by simp)) (SegI.const_append (fun k hk => hp k (by simp [hk])) h)

theorem SegI.lower {l l' : List Instr} (h : SegI l l') :
    SegA (expression l) (expression l') := by
  induction h with
  | nil => exact .nil
  | const hk _ ih =>
    obtain ⟨v, hv⟩ := constInstr_val hk
    simp only [Execution.Core.expression, List.map_cons] at ih ⊢
    rw [hv]
    exact .val v ih
  | nop _ ih => exact .nop ih
  | drop hk _ ih =>
    obtain ⟨v, hv⟩ := constInstr_val hk
    simp only [Execution.Core.expression, List.map_cons] at ih ⊢
    rw [hv]
    exact .drop v ih

theorem SegA.vals_right {l l' : List Admin} (h : SegA l l') : ∃ ws, l' = vals ws := by
  induction h with
  | nil => exact ⟨[], rfl⟩
  | val v _ ih =>
    obtain ⟨ws, rfl⟩ := ih
    exact ⟨v :: ws, rfl⟩
  | nop _ ih => exact ih
  | drop _ _ ih => exact ih

theorem SegA.vals_left {l l' : List Admin} (h : SegA l l') :
    ∀ ks : List Val, SegA (vals ks ++ l) (vals ks ++ l')
  | [] => h
  | k :: ks => .val k (SegA.vals_left h ks)

/-- The first unit of a segment that has one. -/
theorem SegA.first {l l' : List Admin} (h : SegA l l') (hne : l ≠ l') :
    ∃ (ks : List Val) (u l₂ l₂' : List Admin), l = vals ks ++ u ++ l₂ ∧ l' = vals ks ++ l₂' ∧
      SegA l₂ l₂' ∧ (u = [.plain .nop] ∨ ∃ v : Val, u = [v.toAdmin, .plain .drop]) := by
  induction h with
  | nil => exact absurd rfl hne
  | @val v l l' h ih =>
    have hne' : l ≠ l' := fun e => hne (by rw [e])
    obtain ⟨ks, u, l₂, l₂', rfl, rfl, h₂, hu⟩ := ih hne'
    exact ⟨v :: ks, u, l₂, l₂', rfl, rfl, h₂, hu⟩
  | @nop l l' h _ => exact ⟨[], _, l, l', rfl, rfl, h, Or.inl rfl⟩
  | @drop v l l' h _ => exact ⟨[], _, l, l', rfl, rfl, h, Or.inr ⟨v, rfl⟩⟩

/-- The units of a segment run away. -/
theorem SegA.run {l l' : List Admin} (h : SegA l l') :
    ∀ (t : Store H) (f : Frame) (vs : List Val) (rest : List Admin),
      Steps P host ⟨t, f, vals vs ++ l ++ rest⟩ ⟨t, f, vals vs ++ l' ++ rest⟩ := by
  induction h with
  | nil => intros; exact .refl
  | @val v l l' _ ih =>
    intro t f vs rest
    have := ih t f (vs ++ [v]) rest
    simpa [vals] using this
  | @nop l l' _ ih =>
    intro t f vs rest
    refine Relation.ReflTransGen.head ?_ (ih t f vs rest)
    have := Step.append_right (Step.vals_left (Step.parametric (P := P) (host := host) (s := t)
      (f := f) ParametricStep.nop) vs) (l ++ rest)
    simpa using this
  | @drop v l l' _ ih =>
    intro t f vs rest
    refine Relation.ReflTransGen.head ?_ (ih t f vs rest)
    have := Step.append_right (Step.vals_left (Step.parametric (P := P) (host := host) (s := t)
      (f := f) (ParametricStep.drop v)) vs) (l ++ rest)
    simpa using this

/-! ## Inverting the steps of `nop` and `drop` -/

theorem toAdmin_inj {v w : Val} (h : v.toAdmin = w.toAdmin) : v = w := by
  have := congrArg Admin.val? h
  simpa using this

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `val* nop` steps only to `val*`. -/
theorem step_nop_inv {c c' : Config H} (h : Step P host c c') :
    ∀ us : List Val, c.code = vals us ++ [.plain .nop] →
      c'.store = c.store ∧ c'.frame = c.frame ∧ c'.code = vals us := by
  induction h with
  | parametric hp =>
    intro us hc
    dsimp only at hc ⊢
    cases hp with
    | nop =>
      have hl := congrArg List.length hc
      simp only [List.length_cons, List.length_nil, List.length_append, vals_length] at hl
      obtain rfl : us = [] := List.length_eq_zero_iff.mp (by omega)
      exact ⟨rfl, rfl, rfl⟩
    | _ =>
      have hl := congrArg List.getLast? hc
      simp [constI32] at hl
  | numeric hp | vector hp =>
    intro us hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | «variable» hp | table hp | memory hp | reference hp | aggregate hp =>
    intro us hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | @ctxtInstrs _ _ _ _ vs₀ is _ rest hs hne ih =>
    intro us hc
    have hna : is.all Admin.isVal = false := hs.not_all_isVal
    obtain ⟨vs₁, b, es₁, hb, rfl⟩ := exists_head_of_not_all hna
    dsimp only at hc ⊢
    have hc' : vals (vs₀ ++ vs₁) ++ b :: (es₁ ++ rest) = vals us ++ Admin.plain .nop :: [] := by
      rw [← hc]; simp
    obtain ⟨rfl, rfl, h3⟩ := vals_append_cons_inj hb rfl hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
    obtain ⟨h1, h2, h3⟩ := ih vs₁ (by simp)
    dsimp only at h1 h2 h3
    refine ⟨h1, h2, ?_⟩
    rw [h3]
    simp
  | @trapInstrs s f vs₀ rest hne =>
    intro us hc
    dsimp only at hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals us ++ Admin.plain .nop :: [] := by
      rw [← hc]; simp
    obtain ⟨-, h, -⟩ := vals_append_cons_inj rfl rfl hc'
    cases h
  | @throwRefInstrs s f vs₀ x rest hne =>
    intro us hc
    dsimp only at hc
    have hc' : vals (vs₀ ++ [.ref (.exn x)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ Admin.plain .nop :: [] := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    obtain ⟨-, h, -⟩ := vals_append_cons_inj rfl rfl hc'
    cases h
  | _ =>
    intro us hc
    have hl := congrArg List.getLast? hc
    simp [constI32] at hl
    all_goals (subst hl; simp_all [Admin.IsCallRef, Admin.IsReturnCallRef])

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `val* v drop` steps only to `val*`. -/
theorem step_drop_inv {c c' : Config H} (h : Step P host c c') :
    ∀ us : List Val, c.code = vals us ++ [.plain .drop] →
      ∃ (us₀ : List Val) (v : Val), us = us₀ ++ [v] ∧
        c'.store = c.store ∧ c'.frame = c.frame ∧ c'.code = vals us₀ := by
  induction h with
  | parametric hp =>
    intro us hc
    dsimp only at hc ⊢
    cases hp with
    | drop v =>
      have h₁ : [v.toAdmin] = vals us := by
        have := congrArg List.dropLast hc
        simpa using this
      obtain ⟨w, rfl⟩ : ∃ w, us = [w] := by
        have hl := congrArg List.length h₁
        simp only [List.length_singleton, vals_length] at hl
        match us, hl with
        | [w], _ => exact ⟨w, rfl⟩
      have : v = w := toAdmin_inj (by simpa [vals] using h₁)
      subst this
      exact ⟨[], v, rfl, rfl, rfl, rfl⟩
    | _ =>
      have hl := congrArg List.getLast? hc
      simp [constI32] at hl
  | numeric hp | vector hp =>
    intro us hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | «variable» hp | table hp | memory hp | reference hp | aggregate hp =>
    intro us hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | @ctxtInstrs _ _ _ _ vs₀ is _ rest hs hne ih =>
    intro us hc
    have hna : is.all Admin.isVal = false := hs.not_all_isVal
    obtain ⟨vs₁, b, es₁, hb, rfl⟩ := exists_head_of_not_all hna
    dsimp only at hc ⊢
    have hc' : vals (vs₀ ++ vs₁) ++ b :: (es₁ ++ rest) = vals us ++ Admin.plain .drop :: [] := by
      rw [← hc]; simp
    obtain ⟨rfl, rfl, h3⟩ := vals_append_cons_inj hb rfl hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
    obtain ⟨us₀, v, rfl, h1, h2, h3⟩ := ih vs₁ (by simp)
    dsimp only at h1 h2 h3
    refine ⟨vs₀ ++ us₀, v, by simp, h1, h2, ?_⟩
    rw [h3]
    simp
  | @trapInstrs s f vs₀ rest hne =>
    intro us hc
    dsimp only at hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals us ++ Admin.plain .drop :: [] := by
      rw [← hc]; simp
    obtain ⟨-, h, -⟩ := vals_append_cons_inj rfl rfl hc'
    cases h
  | @throwRefInstrs s f vs₀ x rest hne =>
    intro us hc
    dsimp only at hc
    have hc' : vals (vs₀ ++ [.ref (.exn x)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ Admin.plain .drop :: [] := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    obtain ⟨-, h, -⟩ := vals_append_cons_inj rfl rfl hc'
    cases h
  | _ =>
    intro us hc
    have hl := congrArg List.getLast? hc
    simp [constI32] at hl
    all_goals (subst hl; simp_all [Admin.IsCallRef, Admin.IsReturnCallRef])

/-- An exit kernel holds neither `nop` nor `drop`. -/
theorem exit_not_unit {k : List Admin} (hk : Exit k) :
    ∀ a ∈ k, a ≠ .plain .nop ∧ a ≠ .plain .drop := by
  cases hk with
  | @returnCallRef c hc =>
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    constructor <;> rintro rfl <;> simp [Admin.IsReturnCallRef] at hc
  | _ => simp [throwing]

/-! ## The two simulations -/

/-- A step of the left side of a base pair runs its first unit away. -/
theorem step_unit {s s' : Store H} {f f' : Frame} {vs ks : List Val} {u r es' : List Admin}
    (hu : u = [.plain .nop] ∨ ∃ v : Val, u = [v.toAdmin, .plain .drop])
    (h : Step P host ⟨s, f, vals (vs ++ ks) ++ u ++ r⟩ ⟨s', f', es'⟩) :
    s' = s ∧ f' = f ∧ es' = vals (vs ++ ks) ++ r := by
  rcases hu with rfl | ⟨v, rfl⟩
  · have heq : vals (vs ++ ks) ++ [Admin.plain .nop] ++ r =
        vals (vs ++ ks) ++ Admin.plain .nop :: r := by simp
    rw [heq] at h
    rcases Step.split_head rfl h with ⟨ws, us, is', hV, hs1, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · obtain ⟨h1, h2, h3⟩ := step_nop_inv hs1 us rfl
      dsimp only at h1 h2 h3
      subst h1 h2 h3
      refine ⟨rfl, rfl, ?_⟩
      rw [hV]
      simp
    · cases h
    · cases h
  · have heq : vals (vs ++ ks) ++ [v.toAdmin, Admin.plain .drop] ++ r =
        vals (vs ++ ks ++ [v]) ++ Admin.plain .drop :: r := by simp [vals]
    rw [heq] at h
    rcases Step.split_head rfl h with ⟨ws, us, is', hV, hs1, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · obtain ⟨us₀, w, rfl, h1, h2, h3⟩ := step_drop_inv hs1 us rfl
      dsimp only at h1 h2 h3
      subst h1 h2 h3
      refine ⟨rfl, rfl, ?_⟩
      have : vs ++ ks = ws ++ us₀ := by
        have := congrArg List.dropLast hV
        simpa [← List.append_assoc] using this
      rw [this]
      simp
    · cases h
    · cases h

/-- **Forward simulation**: the left side holds the units. -/
theorem vacBaseSim {F : FuncInst H → FuncInst H → Prop} : BaseSim P host F vacBI vacB where
  src := by
    rintro x y ⟨l, l', c, hs, hne, hc, rfl, rfl⟩
    refine ⟨Execution.Core.expression l, Execution.Core.expression l', .plain c, hs.lower, ?_, anchorInstr_val hc,
      by simp, ?_, by simp [Execution.Core.expression], by simp [Execution.Core.expression]⟩
    · intro h
      exact hne (List.map_injective_iff.mpr (fun _ _ h => Admin.plain.inj h) h)
    · intro h
      exact anchorInstr_ne hc (Admin.plain.inj h)
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    obtain ⟨l, l', c, hs, hne, hcv, hct, hcr, rfl, rfl⟩ := hxy
    obtain ⟨ks, u, l₂, l₂', rfl, rfl, hs₂, hu⟩ := hs.first hne
    have hune : u ≠ [] := by rcases hu with rfl | ⟨v, rfl⟩ <;> simp
    have heq : vals vs ++ (vals ks ++ u ++ l₂ ++ [c]) ++ rest =
        vals (vs ++ ks) ++ u ++ (l₂ ++ c :: rest) := by simp
    rw [heq] at hstep ⊢
    obtain ⟨rfl, rfl, rfl⟩ := step_unit hu hstep
    refine ⟨t, vals vs ++ (vals ks ++ l₂' ++ [c]) ++ rest',
      Or.inr ⟨rfl, rfl, rfl, codeSize_lt_of_infix _ _ _ hune⟩, hst, ?_⟩
    have e : vals (vs ++ ks) ++ (l₂ ++ c :: rest) = vals vs ++ (vals ks ++ l₂ ++ [c]) ++ rest := by
      simp
    rw [e]
    refine AdminsRel.append (AdminsRel.append (.refl _) ?_) hrest
    by_cases hl : l₂ = l₂'
    · subst hl
      exact .refl _
    · refine .base ⟨vals ks ++ l₂, vals ks ++ l₂', c, hs₂.vals_left ks, ?_, hcv, hct, hcr, by simp,
        by simp⟩
      simpa using hl
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    obtain ⟨l, l', c, hs, hne, -, -, -, rfl, rfl⟩ := hxy
    obtain ⟨ks, u, l₂, l₂', rfl, rfl, -, hu⟩ := hs.first hne
    obtain ⟨pre, e, hen, rfl⟩ := hk.eq_vals_append
    have hmem : e ∈ vals pre ++ [e] := by simp
    have hnot := exit_not_unit hk e hmem
    rcases hu with rfl | ⟨v, rfl⟩
    · have h1 : vals (vs ++ ks) ++ Admin.plain .nop :: (l₂ ++ [c]) =
          vals (us ++ pre) ++ e :: j := by simpa using he
      obtain ⟨-, rfl, -⟩ := vals_append_cons_inj rfl hen h1
      exact hnot.1 rfl
    · have h1 : vals (vs ++ ks ++ [v]) ++ Admin.plain .drop :: (l₂ ++ [c]) =
          vals (us ++ pre) ++ e :: j := by simpa [vals] using he
      obtain ⟨-, rfl, -⟩ := vals_append_cons_inj rfl hen h1
      exact hnot.2 rfl
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    obtain ⟨l, l', c, -, -, hcv, -, -, rfl, -⟩ := hxy
    have hmem : c ∈ vals us := by rw [← hx]; simp
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hmem
    simp at hcv

/-- **Reverse simulation**: the right side holds the units. -/
theorem vacBaseSim_flip {F : FuncInst H → FuncInst H → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel (fun a b => vacBI b a) fi gi) (hhost : HostRespects F host) :
    BaseSim P host F (fun a b => vacBI b a) (fun a b => vacB b a) where
  src := fun h => (vacBaseSim (P := P) (host := host) (F := F)).src h
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    obtain ⟨l, l', c, hs, -, hcv, hct, hcr, rfl, rfl⟩ := hxy
    obtain ⟨ks, rfl⟩ := hs.vals_right
    have heq : vals vs ++ (vals ks ++ [c]) ++ rest = vals (vs ++ ks) ++ c :: rest := by simp
    rw [heq] at hstep
    rcases Step.split_head hcv hstep with ⟨ws, us, is', hV, hs1, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · obtain ⟨t', is'', hs2, hst', hrel⟩ :=
        Step.match_storeRel (B := fun a b => vacB b a) hF hhost hs1 t hst
      have hrun := hs.run (P := P) (host := host) t f vs (c :: rest')
      have hlast : Step P host ⟨t, f, vals vs ++ vals ks ++ c :: rest'⟩
          ⟨t', f', vals ws ++ is'' ++ rest'⟩ := by
        have := Step.append_right (Step.vals_left hs2 ws) rest'
        have e : vals ws ++ (vals us ++ [c]) ++ rest' = vals vs ++ vals ks ++ c :: rest' := by
          rw [← vals_append, ← List.append_assoc, ← vals_append, ← hV]
          simp
        rw [e] at this
        exact this
      refine ⟨t', vals ws ++ is'' ++ rest', Or.inl (Relation.TransGen.tail' ?_ hlast), hst',
        AdminsRel.append (AdminsRel.append (.refl _) hrel) hrest⟩
      exact Closure.steps_congr hrun (by simp) rfl
    · exact absurd h hct
    · exact absurd h hcr
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    obtain ⟨l, l', c, hs, -, -, -, -, rfl, rfl⟩ := hxy
    obtain ⟨ks, rfl⟩ := hs.vals_right
    refine ⟨t, j, ?_, hst⟩
    have hrun := hs.run (P := P) (host := host) t f vs [c]
    exact Closure.steps_congr hrun (by simp) (by rw [← he]; simp)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    obtain ⟨l, l', c, -, -, hcv, -, -, -, rfl⟩ := hxy
    have hmem : c ∈ vals us := by rw [← hx]; simp
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hmem
    simp at hcv

/-- **Anchored vacuum on modules**: modules with `vacBI`-related bodies are export
equivalent for every code-parametric host. -/
theorem exportEquiv_vacuumLite (hhost : HostParametric host) {m m' : Module}
    (hrel : ModuleBodiesRel vacBI m m') (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) P host m' m :=
  have h₀ : HostRespects (FuncRel vacBI) host := hhost.respects (fun f => FuncRel.refl f)
  have h₁ : HostRespects (FuncRel (fun a b => vacBI b a)) host :=
    hhost.respects (fun f => FuncRel.refl f)
  ⟨exportRefines_of_bodiesRel (vacBaseSim_flip (fun _ _ h => h) h₁) h₁ hrel.flip hm' hm,
    (exportRefines_of_bodiesRel vacBaseSim h₀ hrel hm hm').mono fun _ _ h => h.symm⟩

/-! ## The pass relates every body to its result -/

/-- The anchored shape of a related pair of sequences. -/
def AnchorShape (L L' : List Instr) : Prop :=
  ∃ (l l' : List Instr) (c : Instr) (r r' : List Instr), SegI l l' ∧ anchorInstr c = true ∧
    InstrsRel vacBI r r' ∧ L = l ++ c :: r ∧ L' = l' ++ c :: r'

/-- What the induction carries: the closure relation, the anchored shape when the result
starts with an anchor, and equality when the result is constants only. -/
def Inv (L L' : List Instr) (h : Option Bool) : Prop :=
  InstrsRel vacBI L L' ∧ (h = some true → AnchorShape L L') ∧
    (h = none → L = L' ∧ ∀ k ∈ L', constInstr k = true)

theorem AnchorShape.append {L L' M M' : List Instr} (h : AnchorShape L L')
    (hM : InstrsRel vacBI M M') : AnchorShape (L ++ M) (L' ++ M') := by
  obtain ⟨l, l', c, r, r', hs, hc, hr, rfl, rfl⟩ := h
  exact ⟨l, l', c, r ++ M, r' ++ M', hs, hc, hr.append hM, by simp, by simp⟩

theorem AnchorShape.const_left {p L L' : List Instr} (hp : ∀ k ∈ p, constInstr k = true)
    (h : AnchorShape L L') : AnchorShape (p ++ L) (p ++ L') := by
  obtain ⟨l, l', c, r, r', hs, hc, hr, rfl, rfl⟩ := h
  exact ⟨p ++ l, p ++ l', c, r, r', SegI.const_append hp hs, hc, hr, by simp, by simp⟩

theorem vacL_eq_nil : ∀ {es : List BExpr}, vacL es = [] → es = []
  | [], _ => rfl
  | e :: es, h => by
    simp only [vacL] at h
    split at h
    · next hc =>
      rw [h] at hc
      simp [headL] at hc
    · cases h

theorem vacE_const_leaf {e : BExpr} {k : Instr} (h : vacE e = .op k []) : e = .op k [] := by
  cases e with
  | op i args =>
    simp only [vacE, BExpr.op.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [vacL_eq_nil h]
  | _ => simp [vacE] at h

theorem vacL_singleton_const {es : List BExpr} {k : Instr} (hk : constInstr k = true)
    (h : vacL es = [.op k []]) : es = [.op k []] := by
  match es, h with
  | e :: es, h =>
    simp only [vacL] at h
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      rw [h] at hc
      simp [headL, headE, hk] at hc
    · simp only [List.cons.injEq] at h
      rw [vacE_const_leaf h.1, vacL_eq_nil h.2]

/-- A removable result was removable already. -/
theorem removable_vacE {e : BExpr} (h : removable (vacE e) = true) : vacE e = e := by
  cases e with
  | op i args =>
    simp only [vacE] at h ⊢
    match i, hv : vacL args, h with
    | .nop, [], _ => rw [vacL_eq_nil hv]
    | .drop, [.op (.intConst t b) []], _ =>
      rw [vacL_singleton_const (by simp [constInstr]) hv]
  | _ => simp [vacE, removable] at h

theorem removable_lower {e : BExpr} (h : removable e = true) :
    e.lower = [.nop] ∨ ∃ t b, e.lower = [.intConst t b, .drop] := by
  match e, h with
  | .op .nop [], _ => exact Or.inl rfl
  | .op .drop [.op (.intConst t b) []], _ => exact Or.inr ⟨t, b, rfl⟩

theorem removable_seg {e : BExpr} (h : removable e = true) {l l' : List Instr}
    (hs : SegI l l') : SegI (e.lower ++ l) l' := by
  rcases removable_lower h with h | ⟨t, b, h⟩ <;> rw [h]
  · exact .nop hs
  · exact .drop (by simp [constInstr]) hs

theorem removable_ne {e : BExpr} (h : removable e = true) : e.lower ≠ [] := by
  rcases removable_lower h with h | ⟨t, b, h⟩ <;> rw [h] <;> simp

mutual
theorem vacE_inv : ∀ e : BExpr, Inv e.lower (vacE e).lower (headE (vacE e))
  | .op i args => by
    obtain ⟨hr, ha, hn⟩ := vacL_inv args
    simp only [vacE, BExpr.lower_op, headE]
    refine ⟨hr.append (.refl _), fun h => ?_, fun h => ?_⟩
    · split at h
      · next b hb =>
        rw [hb] at ha
        exact (ha (by rw [h])).append (.refl _)
      · next hb =>
        obtain ⟨he, hc⟩ := hn hb
        split at h
        · cases h
        · next hi =>
          simp only [Option.some.injEq] at h
          rw [he]
          exact ⟨_, _, i, [], [], SegI.of_const hc, h, .nil, by simp, by simp⟩
    · split at h
      · cases h
      · next hb =>
        obtain ⟨he, hc⟩ := hn hb
        split at h
        · next hi =>
          refine ⟨by rw [he], fun k hk => ?_⟩
          simp only [List.mem_append, List.mem_singleton] at hk
          rcases hk with hk | rfl
          exacts [hc k hk, hi]
        · cases h
  | .block bt b => by
    obtain ⟨hr, -, -⟩ := vacL_inv b
    simp only [vacE, BExpr.lower, headE]
    exact ⟨.cons (.block bt hr) .nil, by simp, by simp⟩
  | .loop bt b => by
    obtain ⟨hr, -, -⟩ := vacL_inv b
    simp only [vacE, BExpr.lower, headE]
    exact ⟨.cons (.loop bt hr) .nil, by simp, by simp⟩
  | .tryTable bt cs b => by
    obtain ⟨hr, -, -⟩ := vacL_inv b
    simp only [vacE, BExpr.lower, headE]
    exact ⟨.cons (.tryTable bt cs hr) .nil, by simp, by simp⟩
  | .if_ bt c t e => by
    obtain ⟨hc, ha, -⟩ := vacL_inv c
    obtain ⟨ht, -, -⟩ := vacL_inv t
    obtain ⟨he, -, -⟩ := vacL_inv e
    have hif : InstrsRel vacBI [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)]
        [.if_ bt (BExpr.lowerList (vacL t)) (BExpr.lowerList (vacL e))] :=
      .cons (.if_ bt ht he) .nil
    simp only [vacE, BExpr.lower, headE]
    refine ⟨hc.append hif, fun h => ?_, fun h => ?_⟩
    · split at h
      · next b hb =>
        rw [hb] at ha
        exact (ha (by rw [h])).append hif
      · cases h
    · split at h <;> cases h
termination_by e => sizeOf e
theorem vacL_inv : ∀ es : List BExpr,
    Inv (BExpr.lowerList es) (BExpr.lowerList (vacL es)) (headL (vacL es))
  | [] => ⟨.nil, by simp [vacL, headL], fun _ => ⟨rfl, by simp [vacL]⟩⟩
  | e :: es => by
    obtain ⟨hr, ha, hn⟩ := vacL_inv es
    obtain ⟨hre, hae, hne⟩ := vacE_inv e
    simp only [vacL]
    split
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hrem, hh⟩ := hc
      have hlow : e.lower = (vacE e).lower := by rw [removable_vacE hrem]
      have hshape := ha hh
      have hshape' : AnchorShape (e.lower ++ BExpr.lowerList es) (BExpr.lowerList (vacL es)) := by
        obtain ⟨l, l', c, r, r', hs, hca, hrr, hL, hL'⟩ := hshape
        rw [hlow] at ⊢
        exact ⟨(vacE e).lower ++ l, l', c, r, r', removable_seg hrem hs, hca, hrr,
          by rw [hL]; simp, hL'⟩
      refine ⟨?_, fun _ => by simpa using hshape', fun h => by rw [hh] at h; cases h⟩
      obtain ⟨l, l', c, r, r', hs, hca, hrr, hL, hL'⟩ := hshape
      have hne : (vacE e).lower ++ l ≠ l' := fun heq => by
        have h1 := congrArg List.length heq
        have h2 := hs.length_le
        have h3 := List.length_pos_of_ne_nil (removable_ne hrem)
        simp only [List.length_append] at h1
        omega
      have := (InstrsRel.base (BI := vacBI)
        ⟨_, l', c, removable_seg hrem hs, hne, hca, rfl, rfl⟩).append hrr
      simp only [BExpr.lowerList_cons, hlow, hL, hL']
      simpa using this
    · simp only [BExpr.lowerList_cons, headL]
      refine ⟨hre.append hr, fun h => ?_, fun h => ?_⟩
      · split at h
        · next b hb =>
          rw [hb] at hae
          exact (hae (by rw [h])).append hr
        · next hb =>
          obtain ⟨he, hc⟩ := hne hb
          rw [he]
          exact (ha h).const_left hc
      · split at h
        · cases h
        · next hb =>
          obtain ⟨he, hc⟩ := hne hb
          obtain ⟨he', hc'⟩ := hn h
          refine ⟨by rw [he, he'], fun k hk => ?_⟩
          simp only [List.mem_append] at hk
          rcases hk with hk | hk
          exacts [hc k hk, hc' k hk]
termination_by es => sizeOf es
end

/-- **Every body is related to its vacuumed form.** -/
theorem vacL_rel (es : List BExpr) :
    InstrsRel vacBI (BExpr.lowerList es) (BExpr.lowerList (vacL es)) :=
  (vacL_inv es).1

/-! ## Typing -/

theorem removable_typed {e : BExpr} (h : removable e = true) : TyRepl e.lower [] := by
  rcases removable_lower h with h | ⟨t, b, h⟩ <;> rw [h]
  · exact tyRepl_nop
  · exact tyRepl_const_drop t b

mutual
theorem vacE_typed : ∀ e : BExpr, TyRepl e.lower (vacE e).lower
  | .op i args => by
    simpa [vacE] using TyRepl.append_right (vacL_typed args) [i]
  | .block bt b => by simpa [vacE, BExpr.lower] using TyRepl.block (vacL_typed b) bt
  | .loop bt b => by simpa [vacE, BExpr.lower] using TyRepl.loop (vacL_typed b) bt
  | .tryTable bt cs b => by simpa [vacE, BExpr.lower] using TyRepl.tryTable (vacL_typed b) bt cs
  | .if_ bt c t e => by
    simpa [vacE, BExpr.lower] using
      TyRepl.append (vacL_typed c) (TyRepl.if_ (vacL_typed t) (vacL_typed e) bt)
termination_by e => sizeOf e
theorem vacL_typed : ∀ es : List BExpr,
    TyRepl (BExpr.lowerList es) (BExpr.lowerList (vacL es))
  | [] => TyRepl.refl _
  | e :: es => by
    simp only [vacL]
    split
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      have h := TyRepl.append (removable_typed hc.1) (vacL_typed es)
      rw [removable_vacE hc.1] at h
      simpa using h
    · simpa using TyRepl.append (vacE_typed e) (vacL_typed es)
termination_by es => sizeOf es
end

/-! ## Modules -/

theorem vacuumLite_ok {m : BModule} (hm : m.Ok) : (vacuumLite m).Ok :=
  BodyTransform.ok_of_rel hm rfl (by simp [vacuumLite]) fun i _ _ => by
    simp only [vacuumLite, List.getElem_map]
    exact ⟨rfl, rfl, fun C ts hC hb => vacL_typed _ C _ hC hb⟩

theorem vacuumLite_bodiesRel (m : BModule) :
    ModuleBodiesRel vacBI m.lower (vacuumLite m).lower := by
  refine ⟨rfl, ?_⟩
  simp only [BModule.lower, vacuumLite, List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, vacL_rel f.body⟩ ih

/-- **Anchored vacuum is export equivalent**, for every code-parametric host. -/
theorem vacuumLite_sound {m : BModule} (hm : m.Ok) (host : HostSemantics H)
    (hhost : HostParametric host) :
    ExportEquiv (· = ·) P host (vacuumLite m).lower m.lower :=
  exportEquiv_vacuumLite hhost (vacuumLite_bodiesRel m) hm (vacuumLite_ok hm)

end Silmaril.Wasm.Binaryen.VacuumLite
