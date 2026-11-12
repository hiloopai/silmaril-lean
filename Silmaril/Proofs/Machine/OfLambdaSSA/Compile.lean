module

public import Silmaril.Proofs.Machine.OfLambdaSSA.Terms

/-!
# Inverting `regionOps`

What a successful `regionOps` call says about each region constructor, the
labels a `cfg` allocates for its blocks, and the fold that compiles those
blocks.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

variable {sigs : List Silmaril.Machine.RTL.Signature}

/-- The terminator a branch to a target compiles to. -/
def termOf : Target → List ℕ → Term ℕ
  | .block b, rs => .jump b rs
  | .ret, rs => .ret rs
  | .trap, _ => .trap

theorem regionOps_br {ρ : List (List ℕ)} {L : List (Target × ℕ)} {e e' : Emit} {ℓ : ℕ}
    {arg : Tm (Opcode sigs)} {ops : List (Op ℕ)} {t : Term ℕ}
    (h : regionOps (.br ℓ arg) .br ρ L e = some (ops, t, e')) :
    ∃ tgt w rs, L[ℓ]? = some (tgt, w) ∧ tmRegs ρ arg e = some (rs, ops, e') ∧ rs.length = w ∧
      t = termOf tgt rs := by
  rw [regionOps, Option.bind_eq_some_iff] at h
  obtain ⟨⟨tgt, w⟩, hp, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨⟨rs, ops₀, e₁⟩, ht, h⟩ := h
  by_cases hlen : rs.length = w
  · cases tgt <;>
      · simp only [hlen, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨_, w, rs, hp, ht, hlen, rfl⟩
  · simp [hlen] at h

theorem regionOps_let₁ {ρ : List (List ℕ)} {L : List (Target × ℕ)} {e e' : Emit}
    {a : Tm (Opcode sigs)} {body : Region (Opcode sigs)} {ab : Ann} {ops : List (Op ℕ)}
    {t : Term ℕ} (h : regionOps (.let₁ a body) (.let₁ ab) ρ L e = some (ops, t, e')) :
    ∃ rv ops₁ e₁ ops₂, tmRegs ρ a e = some (rv, ops₁, e₁) ∧
      regionOps body ab (rv :: ρ) L e₁ = some (ops₂, t, e') ∧ ops = ops₁ ++ ops₂ := by
  rw [regionOps, Option.bind_eq_some_iff] at h
  obtain ⟨⟨rv, ops₁, e₁⟩, ha, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨ops₂, t₂, e₂⟩, hb, same⟩ := h
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl, rfl⟩ := same
  exact ⟨rv, ops₁, e₁, ops₂, ha, hb, rfl⟩

theorem regionOps_let₂ {ρ : List (List ℕ)} {L : List (Target × ℕ)} {e e' : Emit}
    {a : Tm (Opcode sigs)} {body : Region (Opcode sigs)} {ab : Ann} {ops : List (Op ℕ)}
    {t : Term ℕ} (h : regionOps (.let₂ a body) (.let₂ ab) ρ L e = some (ops, t, e')) :
    ∃ r rest ops₁ e₁ ops₂, tmRegs ρ a e = some (r :: rest, ops₁, e₁) ∧
      regionOps body ab (rest :: [r] :: ρ) L e₁ = some (ops₂, t, e') ∧ ops = ops₁ ++ ops₂ := by
  rw [regionOps, Option.bind_eq_some_iff] at h
  obtain ⟨⟨rv, ops₁, e₁⟩, ha, h⟩ := h
  match rv, h with
  | [], h => simp at h
  | r :: rest, h =>
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨ops₂, t₂, e₂⟩, hb, same⟩ := h
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl, rfl⟩ := same
    exact ⟨r, rest, ops₁, e₁, ops₂, ha, hb, rfl⟩

/-- A conditional-branch arm is a branch whose argument needs no op. -/
theorem condArm_regionOps {r : Region (Opcode sigs)} {a : Ann} {ρ : List (List ℕ)}
    {L : List (Target × ℕ)} {e e' : Emit} {tl : ℕ} {rs : List ℕ}
    (h : condArm r a ρ L e = some (tl, rs, e')) :
    regionOps r a ([] :: ρ) L e = some ([], .jump tl rs, e') := by
  unfold condArm at h
  split at h
  · obtain ⟨⟨tgt, w⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
    match tgt, h with
    | .block b, h =>
      obtain ⟨⟨rs₀, ops₀, e₁⟩, ht, h⟩ := Option.bind_eq_some_iff.mp h
      match ops₀, h with
      | [], h =>
        by_cases hlen : rs₀.length = w
        · simp only [hlen, ite_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp [regionOps, hp, ht, hlen]
        · simp [hlen] at h
      | _ :: _, h => exact absurd h (by simp)
  · exact absurd h (by simp)

/-- How a `case` on the branch test compiles: a conditional terminator when both
arms are plain branches, a diamond of two new blocks otherwise. -/
theorem regionOps_case {ρ : List (List ℕ)} {L : List (Target × ℕ)} {e e' : Emit}
    {arg : Tm (Opcode sigs)} {l r : Region (Opcode sigs)} {al ar : Ann} {ops : List (Op ℕ)}
    {t : Term ℕ} (h : regionOps (.case (.op .test arg) l r) (.case al ar) ρ L e = some (ops, t, e')) :
    ∃ c e₁, tmRegs ρ arg e = some ([c], ops, e₁) ∧
      ((∃ t₁ rs₁ t₂ rs₂ e₂, regionOps l al ([] :: ρ) L e₁ = some ([], .jump t₁ rs₁, e₂) ∧
          regionOps r ar ([] :: ρ) L e₂ = some ([], .jump t₂ rs₂, e') ∧
          t = .cond c t₁ rs₁ t₂ rs₂) ∨
        ∃ opsL tL e₃ opsR tR e₄,
          regionOps l al ([] :: ρ) L { e₁ with nextLabel := e₁.nextLabel + 1 } =
            some (opsL, tL, e₃) ∧
          regionOps r ar ([] :: ρ) L
              { e₃ with blocks := (e₁.nextLabel, ⟨[], opsL, tL⟩) :: e₃.blocks } =
            some (opsR, tR, e₄) ∧
          t = .cond c e₁.nextLabel [] e₄.nextLabel [] ∧
          e' = { e₄ with nextLabel := e₄.nextLabel + 1,
                          blocks := (e₄.nextLabel, ⟨[], opsR, tR⟩) :: e₄.blocks }) := by
  rw [regionOps] at h
  simp only at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨⟨rs, ops₀, e₁⟩, ha, h⟩ := h
  match rs, h with
  | [c], h =>
    simp only at h
    split at h
    · rename_i res hcond
      obtain rfl := Option.some.inj h
      rw [condOf, Option.bind_eq_some_iff] at hcond
      obtain ⟨⟨t₁, rs₁, e₂⟩, hL, hcond⟩ := hcond
      rw [Option.map_eq_some_iff] at hcond
      obtain ⟨⟨t₂, rs₂, e₃⟩, hR, same⟩ := hcond
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl, rfl⟩ := same
      exact ⟨c, e₁, ha, Or.inl ⟨t₁, rs₁, t₂, rs₂, e₂, condArm_regionOps hL,
        condArm_regionOps hR, rfl⟩⟩
    · rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨opsL, tL, e₃⟩, hL, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨opsR, tR, e₄⟩, hR, same⟩ := h
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl, rfl⟩ := same
      exact ⟨c, e₁, ha, Or.inr ⟨opsL, tL, e₃, opsR, tR, e₄, hL, hR, rfl, rfl⟩⟩
  | [], h => simp at h
  | _ :: _ :: _, h => simp at h

/-! ## `cfg` -/

/-- The labels a `cfg` gives its blocks: `base + i`, carrying `ws[i]` words. -/
def inner (base : ℕ) (ws : List ℕ) (k : ℕ) : List (Target × ℕ) :=
  (List.finRange k).map fun i => (Target.block (base + i.val), ws.getD i.val 0)

@[simp] theorem inner_length (base : ℕ) (ws : List ℕ) (k : ℕ) : (inner base ws k).length = k := by
  simp [inner]

theorem inner_getElem? {base : ℕ} {ws : List ℕ} {k j : ℕ} (hj : j < k) :
    (inner base ws k)[j]? = some (.block (base + j), ws.getD j 0) := by
  simp [inner, hj]

theorem inner_widths {base : ℕ} {ws : List ℕ} {k : ℕ} (hk : ws.length = k) :
    (inner base ws k).map Prod.snd = ws := by
  subst hk
  apply List.ext_getElem (by simp)
  intro j h₁ h₂
  simp [inner, List.getD_eq_getElem?_getD]

/-- Compiling block `i` of a `cfg` from compiler state `u`, and finishing it. -/
def cfgStep {k : ℕ} (blocks : Fin k → Region (Opcode sigs)) (abs : List Ann) (ws : List ℕ)
    (ρ : List (List ℕ)) (L : List (Target × ℕ)) (base : ℕ) (i : Fin k) (u : Emit) :
    Option Emit :=
  (regionOps (blocks i) (abs.getD i.val .br) (freshRegs u.nextReg (ws.getD i.val 0) :: ρ) L
      { u with nextReg := u.nextReg + ws.getD i.val 0 }).map
    fun (opsB, tB, u') =>
      { u' with blocks := (base + i.val, ⟨freshRegs u.nextReg (ws.getD i.val 0), opsB, tB⟩) ::
                            u'.blocks }

theorem regionOps_cfg {ρ : List (List ℕ)} {L : List (Target × ℕ)} {e e' : Emit}
    {entry : Region (Opcode sigs)} {k : ℕ} {blocks : Fin k → Region (Opcode sigs)}
    {ws : List ℕ} {ae : Ann} {abs : List Ann} {ops : List (Op ℕ)} {t : Term ℕ}
    (h : regionOps (.cfg entry k blocks) (.cfg ws ae abs) ρ L e = some (ops, t, e')) :
    ∃ e₁, regionOps entry ae ρ (inner e.nextLabel ws k ++ L)
        { e with nextLabel := e.nextLabel + k } = some (ops, t, e₁) ∧
      (List.finRange k).foldl
        (fun acc i => acc.bind (cfgStep blocks abs ws ρ (inner e.nextLabel ws k ++ L)
          e.nextLabel i)) (some e₁) = some e' := by
  rw [regionOps] at h
  split at h
  · rw [Option.bind_eq_some_iff] at h
    obtain ⟨⟨ops₁, t₁, e₁⟩, hE, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨e₂, hF, same⟩ := h
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl, rfl⟩ := same
    exact ⟨e₁, hE, hF⟩
  · exact absurd h (by simp)

/-- Compiling a region adds blocks and moves the register counter up. -/
theorem regionOps_mono {r : Region (Opcode sigs)} {a : Ann} {ρ : List (List ℕ)}
    {L : List (Target × ℕ)} {e e' : Emit} {ops : List (Op ℕ)} {t : Term ℕ}
    (h : regionOps r a ρ L e = some (ops, t, e')) :
    e.nextReg ≤ e'.nextReg ∧ e.blocks ⊆ e'.blocks ∧ ∀ x ∈ ops.flatMap Op.defs, e.nextReg ≤ x := by
  obtain ⟨hr, -, pre, hb, -, -, hd, -⟩ := regionOps_grew r a ρ L e _ h
  refine ⟨hr, fun p hp => by rw [hb]; exact List.mem_append_right _ hp, fun x hx => ?_⟩
  exact (hd x (List.mem_append_left _ hx)).1

/-- **The `cfg` fold compiles every block**, each from a state at or above the
one the fold started in, and keeps every block it finishes. -/
theorem fold_cfg {k : ℕ} (F : Fin k → Emit → Option Emit)
    (hF : ∀ i u v, F i u = some v → u.nextReg ≤ v.nextReg ∧ u.blocks ⊆ v.blocks) :
    ∀ (l : List (Fin k)) (u v : Emit), l.foldl (fun acc i => acc.bind (F i)) (some u) = some v →
      u.nextReg ≤ v.nextReg ∧ u.blocks ⊆ v.blocks ∧
        ∀ i ∈ l, ∃ x y, u.nextReg ≤ x.nextReg ∧ F i x = some y ∧ y.blocks ⊆ v.blocks
  | [], u, v, h => by
    obtain rfl := Option.some.inj h
    exact ⟨le_rfl, fun _ hp => hp, by simp⟩
  | i :: rest, u, v, h => by
    rw [List.foldl_cons] at h
    cases hu : F i u with
    | none =>
      rw [Option.bind_some, hu, foldl_bind_none] at h
      exact absurd h (by simp)
    | some y =>
      rw [Option.bind_some, hu] at h
      obtain ⟨r₁, b₁, each⟩ := fold_cfg F hF rest y v h
      obtain ⟨r₀, b₀⟩ := hF i u y hu
      refine ⟨r₀.trans r₁, fun _ hp => b₁ (b₀ hp), fun j hj => ?_⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨u, y, le_rfl, hu, b₁⟩
      · obtain ⟨x, z, hx, hz, hzb⟩ := each j hj
        exact ⟨x, z, r₀.trans hx, hz, hzb⟩

/-- One fold step compiles its block above the state it starts from. -/
theorem cfgStep_some {k : ℕ} {blocks : Fin k → Region (Opcode sigs)} {abs : List Ann}
    {ws : List ℕ} {ρ : List (List ℕ)} {L : List (Target × ℕ)} {base : ℕ} {i : Fin k} {u v : Emit}
    (h : cfgStep blocks abs ws ρ L base i u = some v) :
    ∃ opsB tB u', regionOps (blocks i) (abs.getD i.val .br)
        (freshRegs u.nextReg (ws.getD i.val 0) :: ρ) L
        { u with nextReg := u.nextReg + ws.getD i.val 0 } = some (opsB, tB, u') ∧
      v = { u' with blocks := (base + i.val, ⟨freshRegs u.nextReg (ws.getD i.val 0), opsB, tB⟩) ::
                                u'.blocks } := by
  rw [cfgStep, Option.map_eq_some_iff] at h
  obtain ⟨⟨opsB, tB, u'⟩, hc, rfl⟩ := h
  exact ⟨opsB, tB, u', hc, rfl⟩

theorem cfgStep_mono {k : ℕ} {blocks : Fin k → Region (Opcode sigs)} {abs : List Ann}
    {ws : List ℕ} {ρ : List (List ℕ)} {L : List (Target × ℕ)} {base : ℕ} (i : Fin k) (u v : Emit)
    (h : cfgStep blocks abs ws ρ L base i u = some v) : u.nextReg ≤ v.nextReg ∧ u.blocks ⊆ v.blocks := by
  obtain ⟨opsB, tB, u', hc, rfl⟩ := cfgStep_some h
  obtain ⟨hr, hb, -⟩ := regionOps_mono hc
  simp only at hr ⊢
  exact ⟨by omega, fun _ hp => List.mem_cons_of_mem _ (hb hp)⟩

end Silmaril.Proofs.Machine.OfLambdaSSA
