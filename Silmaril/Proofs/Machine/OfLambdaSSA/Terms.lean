module

public import Silmaril.Proofs.Machine.OfLambdaSSA.Basic

/-!
# Terms: `tmRegs` simulates term evaluation

A term of the fragment compiles to the ops that compute it and the registers
that then hold its words. Forwards (`tm_forward`): if the term evaluates, the
ops run and the registers hold the value's words. Backwards (`tm_backward`): if
the ops run, the term evaluates to the value those words make. Neither run
changes a register below where the compilation started allocating.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

variable {sigs : List Silmaril.Machine.RTL.Signature} {oracle : CallOracle}

/-! ## Inverting the compiler -/

theorem tmRegs_var {ρ : List (List ℕ)} {i : ℕ} {e e' : Emit} {rs : List ℕ} {ops : List (Op ℕ)}
    (h : tmRegs (sigs := sigs) ρ (.var i) e = some (rs, ops, e')) :
    ρ[i]? = some rs ∧ ops = [] ∧ e' = e := by
  rw [tmRegs, Option.map_eq_some_iff] at h
  obtain ⟨g, hg, same⟩ := h
  simp only [Prod.mk.injEq] at same
  exact ⟨same.1 ▸ hg, same.2.1.symm, same.2.2.symm⟩

theorem tmRegs_unit {ρ : List (List ℕ)} {e e' : Emit} {rs : List ℕ} {ops : List (Op ℕ)}
    (h : tmRegs (sigs := sigs) ρ .unit e = some (rs, ops, e')) : rs = [] ∧ ops = [] ∧ e' = e := by
  rw [tmRegs] at h
  simpa [eq_comm] using h

theorem tmRegs_pair {ρ : List (List ℕ)} {a b : Tm (Opcode sigs)} {e e' : Emit} {rs : List ℕ}
    {ops : List (Op ℕ)} (h : tmRegs ρ (.pair a b) e = some (rs, ops, e')) :
    ∃ ra opa e₁ rb opb, tmRegs ρ a e = some (ra, opa, e₁) ∧
      tmRegs ρ b e₁ = some (rb, opb, e') ∧ rs = ra ++ rb ∧ ops = opa ++ opb := by
  rw [tmRegs, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ra, opa, e₁⟩, ha, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨rb, opb, e₂⟩, hb, same⟩ := h
  simp only [Prod.mk.injEq] at same
  exact ⟨ra, opa, e₁, rb, opb, ha, same.2.2 ▸ hb, same.1.symm, same.2.1.symm⟩

theorem tmRegs_op {ρ : List (List ℕ)} {f : Opcode sigs} (hf : f ≠ .test) {a : Tm (Opcode sigs)}
    {e e' : Emit} {rs : List ℕ} {ops : List (Op ℕ)} (h : tmRegs ρ (.op f a) e = some (rs, ops, e')) :
    ∃ ra opa e₁ o, tmRegs ρ a e = some (ra, opa, e₁) ∧
      opOf f ra (freshRegs e₁.nextReg f.results) = some o ∧
      rs = freshRegs e₁.nextReg f.results ∧ ops = opa ++ [o] ∧
      e' = { e₁ with nextReg := e₁.nextReg + f.results } := by
  rw [SSA.tmRegs_op hf, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ra, opa, e₁⟩, ha, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨o, ho, same⟩ := h
  simp only [Prod.mk.injEq] at same
  exact ⟨ra, opa, e₁, o, ha, ho, same.1.symm, same.2.1.symm, same.2.2.symm⟩

theorem tmRegs_let₁ {ρ : List (List ℕ)} {a b : Tm (Opcode sigs)} {e e' : Emit} {rs : List ℕ}
    {ops : List (Op ℕ)} (h : tmRegs ρ (.let₁ a b) e = some (rs, ops, e')) :
    ∃ ra opa e₁ opb, tmRegs ρ a e = some (ra, opa, e₁) ∧
      tmRegs (ra :: ρ) b e₁ = some (rs, opb, e') ∧ ops = opa ++ opb := by
  rw [tmRegs, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ra, opa, e₁⟩, ha, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨rb, opb, e₂⟩, hb, same⟩ := h
  simp only [Prod.mk.injEq] at same
  exact ⟨ra, opa, e₁, opb, ha, by rw [← same.1, ← same.2.2]; exact hb, same.2.1.symm⟩

theorem tmRegs_let₂ {ρ : List (List ℕ)} {a b : Tm (Opcode sigs)} {e e' : Emit} {rs : List ℕ}
    {ops : List (Op ℕ)} (h : tmRegs ρ (.let₂ a b) e = some (rs, ops, e')) :
    ∃ r rest opa e₁ opb, tmRegs ρ a e = some (r :: rest, opa, e₁) ∧
      tmRegs (rest :: [r] :: ρ) b e₁ = some (rs, opb, e') ∧ ops = opa ++ opb := by
  rw [tmRegs, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ra, opa, e₁⟩, ha, h⟩ := h
  match ra, h with
  | [], h => simp at h
  | r :: rest, h =>
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨rb, opb, e₂⟩, hb, same⟩ := h
    simp only [Prod.mk.injEq] at same
    exact ⟨r, rest, opa, e₁, opb, ha, by rw [← same.1, ← same.2.2]; exact hb, same.2.1.symm⟩

/-- Compiling a term moves the register counter up and defines registers above
where it started. -/
theorem tmRegs_bounds {ρ : List (List ℕ)} {t : Tm (Opcode sigs)} {e e' : Emit} {rs : List ℕ}
    {ops : List (Op ℕ)} (h : tmRegs ρ t e = some (rs, ops, e')) :
    e.nextReg ≤ e'.nextReg ∧ (∀ r ∈ ops.flatMap Op.defs, e.nextReg ≤ r) ∧
      e'.blocks = e.blocks ∧ e'.nextLabel = e.nextLabel := by
  obtain ⟨hb, hl, hr, hd, -⟩ := tmRegs_grew t ρ e _ h
  exact ⟨hr, fun r hm => (hd r hm).1, hb, hl⟩

/-! ## Shapes -/

theorem Shape.Holds.tuple {n : ℕ} {v : Value Word} {ws : List Word}
    (h : (Shape.tuple n).Holds v ws) : v = packValues ws ∧ ws.length = n := h

/-- A word and a tuple make a longer tuple. -/
theorem holds_pair {va vb : Value Word} {wa wb : List Word} {n : ℕ}
    (ha : Shape.word.Holds va wa) (hb : (Shape.tuple n).Holds vb wb) :
    (Shape.tuple (n + 1)).Holds (.pair va vb) (wa ++ wb) := by
  obtain ⟨w, rfl, rfl⟩ := ha
  obtain ⟨rfl, hlen⟩ := hb
  exact ⟨rfl, by simp [hlen]⟩

/-- A nonempty tuple is a word in front of a shorter tuple. -/
theorem holds_split {n : ℕ} {va vb : Value Word} {ws : List Word}
    (h : (Shape.tuple (n + 1)).Holds (.pair va vb) ws) :
    ∃ w ws', ws = w :: ws' ∧ Shape.word.Holds va [w] ∧ (Shape.tuple n).Holds vb ws' := by
  obtain ⟨hv, hlen⟩ := h
  obtain ⟨w, ws', rfl, rfl, rfl⟩ := packValues_eq_pair hv.symm
  exact ⟨w, ws', rfl, ⟨w, rfl, rfl⟩, rfl, by simpa using hlen⟩

/-- The words of a value fill the registers holding it, one each. -/
theorem readAll_cons_split {fr : Frame ℕ} {g : List ℕ} {w : Word} {ws : List Word}
    (h : fr.readAll g = some (w :: ws)) :
    ∃ r rest, g = r :: rest ∧ fr.readAll [r] = some [w] ∧ fr.readAll rest = some ws := by
  match g, h with
  | [], h => simp at h
  | r :: rest, h =>
    obtain ⟨x, xs, hx, hxs, same⟩ := readAll_cons_eq_some.mp h
    simp only [List.cons.injEq] at same
    refine ⟨r, rest, rfl, ?_, same.2 ▸ hxs⟩
    simp [readAll_cons, hx, same.1]

end Silmaril.Proofs.Machine.OfLambdaSSA

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

variable {sigs : List Silmaril.Machine.RTL.Signature} {oracle : CallOracle}

/-! ## Forwards -/

variable (oracle) in
/-- What compiling a term guarantees forwards: if the term evaluates, its ops run,
its registers hold the words of its value, and nothing below `e.nextReg` changes. -/
def TmFwd (Γ : List Shape) (a : Tm (Opcode sigs)) (s : Shape) : Prop :=
  ∀ {ρ : List (List ℕ)} {e e' : Emit} {rs : List ℕ} {ops : List (Op ℕ)}
    {env : Semantics.Env Word} {fr : Frame ℕ} {m m' : Memory} {v : Value Word},
    tmRegs ρ a e = some (rs, ops, e') → Agrees Γ ρ env fr → Below Γ ρ e.nextReg →
    Semantics.Tm.Eval (Opcode.step oracle) env a m v m' →
    ∃ fr' ws, Ops.Exec oracle ops fr m fr' m' ∧ fr'.readAll rs = some ws ∧ s.Holds v ws ∧
      Same e.nextReg fr fr' ∧ ∀ x ∈ rs, x < e'.nextReg

theorem fwd_var {Γ : List Shape} {i : ℕ} {s : Shape} (hΓ : Γ[i]? = some s) :
    TmFwd oracle Γ (.var i : Tm (Opcode sigs)) s := by
  intro ρ e e' rs ops env fr m m' v h hag hb hev
  obtain ⟨hρ, rfl, rfl⟩ := tmRegs_var h
  obtain ⟨rfl, rfl⟩ := eval_var_inv hev
  obtain ⟨g, ws, hg, hr, hh⟩ := hag i s hΓ
  have same : g = rs := Option.some.inj (hg.symm.trans hρ)
  exact ⟨fr, ws, .nil, same ▸ hr, hh, Same.refl _ _, hb i s rs hΓ hρ⟩

theorem fwd_unit {Γ : List Shape} : TmFwd oracle Γ (.unit : Tm (Opcode sigs)) (.tuple 0) := by
  intro ρ e e' rs ops env fr m m' v h hag hb hev
  obtain ⟨rfl, rfl, rfl⟩ := tmRegs_unit h
  obtain ⟨rfl, rfl⟩ := eval_unit_inv hev
  exact ⟨fr, [], .nil, rfl, ⟨rfl, rfl⟩, Same.refl _ _, by simp⟩

theorem fwd_pair {Γ : List Shape} {a b : Tm (Opcode sigs)} {n : ℕ}
    (iha : TmFwd oracle Γ a .word) (ihb : TmFwd oracle Γ b (.tuple n)) :
    TmFwd oracle Γ (.pair a b) (.tuple (n + 1)) := by
  intro ρ e e' rs ops env fr m m' v h hag hb hev
  obtain ⟨ra, opa, e₁, rb, opb, ha, hb', rfl, rfl⟩ := tmRegs_pair h
  obtain ⟨va, vb, m₁, eva, evb, rfl⟩ := eval_pair_inv hev
  have bnd₁ := tmRegs_bounds ha
  have bnd₂ := tmRegs_bounds hb'
  obtain ⟨fr₁, wa, xa, ra₁, hha, same₁, lta⟩ := iha ha hag hb eva
  obtain ⟨fr₂, wb, xb, rb₂, hhb, same₂, ltb⟩ :=
    ihb hb' (hag.same hb same₁) (hb.mono bnd₁.1) evb
  have ra₂ : fr₂.readAll ra = some wa := (readAll_of_same same₂ lta).trans ra₁
  refine ⟨fr₂, wa ++ wb, ops_exec_append xa xb, readAll_append ra₂ rb₂, holds_pair hha hhb,
    same₁.trans (same₂.mono bnd₁.1), fun x hx => ?_⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact Nat.lt_of_lt_of_le (lta x hx) bnd₂.1
  · exact ltb x hx

theorem fwd_op (hsigs : CallOracle.MatchesSigs oracle sigs) {Γ : List Shape} {f : Opcode sigs}
    (hf : f ≠ .test) {a : Tm (Opcode sigs)} (ih : TmFwd oracle Γ a (.tuple f.arity)) :
    TmFwd oracle Γ (.op f a) (.tuple f.results) := by
  intro ρ e e' rs ops env fr m m' v h hag hb hev
  obtain ⟨ra, opa, e₁, o, ha, ho, rfl, rfl, rfl⟩ := tmRegs_op hf h
  obtain ⟨va, m₁, eva, hstep⟩ := eval_op_inv hev
  have bnd₁ := tmRegs_bounds ha
  obtain ⟨fr₁, wa, xa, ra₁, ⟨rfl, -⟩, same₁, -⟩ := ih ha hag hb eva
  obtain ⟨fr₂, res, xo, ds₂, rfl⟩ :=
    op_forward hsigs ho (freshRegs_nodup _ _) (freshRegs_length _ _) ra₁ hstep
  have fresh : ∀ r ∈ [o].flatMap Op.defs, e.nextReg ≤ r := fun r hr => by
    have := (mem_freshRegs.mp (by simpa [opOf_defs ho] using hr)).1
    omega
  have width : res.length = f.results := by simpa using (readAll_length ds₂).symm
  refine ⟨fr₂, res, ops_exec_append xa xo, ds₂, ⟨rfl, width⟩,
    same₁.trans (ops_exec_same xo fresh), fun x hx => (mem_freshRegs.mp hx).2⟩

theorem fwd_let₁ {Γ : List Shape} {a b : Tm (Opcode sigs)} {s s' : Shape}
    (iha : TmFwd oracle Γ a s) (ihb : TmFwd oracle (s :: Γ) b s') :
    TmFwd oracle Γ (.let₁ a b) s' := by
  intro ρ e e' rs ops env fr m m' v h hag hb hev
  obtain ⟨ra, opa, e₁, opb, ha, hb', rfl⟩ := tmRegs_let₁ h
  cases hev with
  | let₁ eva evb =>
    have bnd₁ := tmRegs_bounds ha
    obtain ⟨fr₁, wa, xa, ra₁, hha, same₁, lta⟩ := iha ha hag hb eva
    have hag₁ := (hag.same hb same₁).cons ra₁ hha
    obtain ⟨fr₂, wb, xb, rb₂, hhb, same₂, ltb⟩ :=
      ihb hb' hag₁ ((hb.mono bnd₁.1).cons lta) evb
    exact ⟨fr₂, wb, ops_exec_append xa xb, rb₂, hhb, same₁.trans (same₂.mono bnd₁.1), ltb⟩

theorem fwd_let₂ {Γ : List Shape} {a b : Tm (Opcode sigs)} {n : ℕ} {s' : Shape}
    (iha : TmFwd oracle Γ a (.tuple (n + 1))) (ihb : TmFwd oracle (.tuple n :: .word :: Γ) b s') :
    TmFwd oracle Γ (.let₂ a b) s' := by
  intro ρ e e' rs ops env fr m m' v h hag hb hev
  obtain ⟨r, rest, opa, e₁, opb, ha, hb', rfl⟩ := tmRegs_let₂ h
  obtain ⟨va, vb, m₁, eva, evb⟩ := eval_let₂_inv hev
  have bnd₁ := tmRegs_bounds ha
  obtain ⟨fr₁, wa, xa, ra₁, hha, same₁, lta⟩ := iha ha hag hb eva
  obtain ⟨w, ws', rfl, hw, hws'⟩ := holds_split hha
  obtain ⟨r', rest', heq, hr₁, hrest₁⟩ := readAll_cons_split ra₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj heq
  have hag₁ := ((hag.same hb same₁).cons hr₁ hw).cons hrest₁ hws'
  have below : Below (.tuple n :: .word :: Γ) (rest :: [r] :: ρ) e₁.nextReg :=
    ((hb.mono bnd₁.1).cons fun x hx => lta x (by simp_all)).cons fun x hx => lta x (by simp [hx])
  obtain ⟨fr₂, wb, xb, rb₂, hhb, same₂, ltb⟩ := ihb hb' hag₁ below evb
  exact ⟨fr₂, wb, ops_exec_append xa xb, rb₂, hhb, same₁.trans (same₂.mono bnd₁.1), ltb⟩

/-- **Terms of the fragment compile forwards.** -/
theorem tm_forward (hsigs : CallOracle.MatchesSigs oracle sigs) {Γ : List Shape}
    {a : Tm (Opcode sigs)} {s : Shape} (h : TmFits sigs Γ a s) : TmFwd oracle Γ a s := by
  induction h with
  | var hΓ => exact fwd_var hΓ
  | unit => exact fwd_unit
  | pair _ _ iha ihb => exact fwd_pair iha ihb
  | op hf _ ih => exact fwd_op hsigs hf ih
  | let₁ _ _ iha ihb => exact fwd_let₁ iha ihb
  | let₂ _ _ iha ihb => exact fwd_let₂ iha ihb

end Silmaril.Proofs.Machine.OfLambdaSSA

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

variable {sigs : List Silmaril.Machine.RTL.Signature} {oracle : CallOracle}

/-! ## Backwards -/

variable (oracle) in
/-- What compiling a term guarantees backwards: if its ops run, the term evaluates
to the value whose words its registers then hold. -/
def TmBwd (Γ : List Shape) (a : Tm (Opcode sigs)) (s : Shape) : Prop :=
  ∀ {ρ : List (List ℕ)} {e e' : Emit} {rs : List ℕ} {ops : List (Op ℕ)}
    {env : Semantics.Env Word} {fr fr' : Frame ℕ} {m m' : Memory},
    tmRegs ρ a e = some (rs, ops, e') → Agrees Γ ρ env fr → Below Γ ρ e.nextReg →
    Ops.Exec oracle ops fr m fr' m' →
    ∃ v ws, Semantics.Tm.Eval (Opcode.step oracle) env a m v m' ∧ fr'.readAll rs = some ws ∧
      s.Holds v ws ∧ ∀ x ∈ rs, x < e'.nextReg

/-- A compiled term's ops leave the registers below its start alone. -/
theorem tm_same {ρ : List (List ℕ)} {a : Tm (Opcode sigs)} {e e' : Emit} {rs : List ℕ}
    {ops : List (Op ℕ)} (h : tmRegs ρ a e = some (rs, ops, e')) {fr fr' : Frame ℕ}
    {m m' : Memory} (hx : Ops.Exec oracle ops fr m fr' m') : Same e.nextReg fr fr' :=
  ops_exec_same hx (tmRegs_bounds h).2.1

theorem bwd_var {Γ : List Shape} {i : ℕ} {s : Shape} (hΓ : Γ[i]? = some s) :
    TmBwd oracle Γ (.var i : Tm (Opcode sigs)) s := by
  intro ρ e e' rs ops env fr fr' m m' h hag hb hx
  obtain ⟨hρ, rfl, rfl⟩ := tmRegs_var h
  cases hx
  obtain ⟨g, ws, hg, hr, hh⟩ := hag i s hΓ
  have same : g = rs := Option.some.inj (hg.symm.trans hρ)
  exact ⟨env i, ws, .var, same ▸ hr, hh, hb i s rs hΓ hρ⟩

theorem bwd_unit {Γ : List Shape} : TmBwd oracle Γ (.unit : Tm (Opcode sigs)) (.tuple 0) := by
  intro ρ e e' rs ops env fr fr' m m' h hag hb hx
  obtain ⟨rfl, rfl, rfl⟩ := tmRegs_unit h
  cases hx
  exact ⟨.unit, [], .unit, rfl, ⟨rfl, rfl⟩, by simp⟩

theorem bwd_pair {Γ : List Shape} {a b : Tm (Opcode sigs)} {n : ℕ}
    (iha : TmBwd oracle Γ a .word) (ihb : TmBwd oracle Γ b (.tuple n)) :
    TmBwd oracle Γ (.pair a b) (.tuple (n + 1)) := by
  intro ρ e e' rs ops env fr fr' m m' h hag hb hx
  obtain ⟨ra, opa, e₁, rb, opb, ha, hb', rfl, rfl⟩ := tmRegs_pair h
  obtain ⟨fr₁, m₁, xa, xb⟩ := ops_exec_append_inv hx
  have bnd₁ := tmRegs_bounds ha
  have bnd₂ := tmRegs_bounds hb'
  obtain ⟨va, wa, eva, ra₁, hha, lta⟩ := iha ha hag hb xa
  obtain ⟨vb, wb, evb, rb₂, hhb, ltb⟩ := ihb hb' (hag.same hb (tm_same ha xa)) (hb.mono bnd₁.1) xb
  have ra₂ : fr'.readAll ra = some wa := (readAll_of_same (tm_same hb' xb) lta).trans ra₁
  refine ⟨_, wa ++ wb, .pair eva evb, readAll_append ra₂ rb₂, holds_pair hha hhb, fun x hx => ?_⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact Nat.lt_of_lt_of_le (lta x hx) bnd₂.1
  · exact ltb x hx

theorem bwd_op {Γ : List Shape} {f : Opcode sigs} (hf : f ≠ .test) {a : Tm (Opcode sigs)}
    (ih : TmBwd oracle Γ a (.tuple f.arity)) : TmBwd oracle Γ (.op f a) (.tuple f.results) := by
  intro ρ e e' rs ops env fr fr' m m' h hag hb hx
  obtain ⟨ra, opa, e₁, o, ha, ho, rfl, rfl, rfl⟩ := tmRegs_op hf h
  obtain ⟨fr₁, m₁, xa, xo⟩ := ops_exec_append_inv hx
  obtain ⟨va, wa, eva, ra₁, ⟨rfl, -⟩, -⟩ := ih ha hag hb xa
  obtain ⟨res, ds₂, hstep⟩ := op_backward ho (freshRegs_nodup _ _) ra₁ xo
  have width : res.length = f.results := by simpa using (readAll_length ds₂).symm
  exact ⟨_, res, .op eva hstep, ds₂, ⟨rfl, width⟩, fun x hx => (mem_freshRegs.mp hx).2⟩

theorem bwd_let₁ {Γ : List Shape} {a b : Tm (Opcode sigs)} {s s' : Shape}
    (iha : TmBwd oracle Γ a s) (ihb : TmBwd oracle (s :: Γ) b s') :
    TmBwd oracle Γ (.let₁ a b) s' := by
  intro ρ e e' rs ops env fr fr' m m' h hag hb hx
  obtain ⟨ra, opa, e₁, opb, ha, hb', rfl⟩ := tmRegs_let₁ h
  obtain ⟨fr₁, m₁, xa, xb⟩ := ops_exec_append_inv hx
  have bnd₁ := tmRegs_bounds ha
  obtain ⟨va, wa, eva, ra₁, hha, lta⟩ := iha ha hag hb xa
  have hag₁ := (hag.same hb (tm_same ha xa)).cons ra₁ hha
  obtain ⟨vb, wb, evb, rb₂, hhb, ltb⟩ := ihb hb' hag₁ ((hb.mono bnd₁.1).cons lta) xb
  exact ⟨vb, wb, .let₁ eva evb, rb₂, hhb, ltb⟩

theorem bwd_let₂ {Γ : List Shape} {a b : Tm (Opcode sigs)} {n : ℕ} {s' : Shape}
    (iha : TmBwd oracle Γ a (.tuple (n + 1))) (ihb : TmBwd oracle (.tuple n :: .word :: Γ) b s') :
    TmBwd oracle Γ (.let₂ a b) s' := by
  intro ρ e e' rs ops env fr fr' m m' h hag hb hx
  obtain ⟨r, rest, opa, e₁, opb, ha, hb', rfl⟩ := tmRegs_let₂ h
  obtain ⟨fr₁, m₁, xa, xb⟩ := ops_exec_append_inv hx
  have bnd₁ := tmRegs_bounds ha
  obtain ⟨va, wa, eva, ra₁, ⟨rfl, hlen⟩, lta⟩ := iha ha hag hb xa
  obtain ⟨w, ws', rfl⟩ : ∃ w ws', wa = w :: ws' := List.exists_cons_of_length_pos (by omega)
  obtain ⟨r', rest', heq, hr₁, hrest₁⟩ := readAll_cons_split ra₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj heq
  have hw : Shape.word.Holds (.atom w) [w] := ⟨w, rfl, rfl⟩
  have hws' : (Shape.tuple n).Holds (packValues ws') ws' := ⟨rfl, by simpa using hlen⟩
  have hag₁ := ((hag.same hb (tm_same ha xa)).cons hr₁ hw).cons hrest₁ hws'
  have below : Below (.tuple n :: .word :: Γ) (rest :: [r] :: ρ) e₁.nextReg :=
    ((hb.mono bnd₁.1).cons fun x hx => lta x (by simp_all)).cons fun x hx => lta x (by simp [hx])
  obtain ⟨vb, wb, evb, rb₂, hhb, ltb⟩ := ihb hb' hag₁ below xb
  exact ⟨vb, wb, .let₂ eva evb, rb₂, hhb, ltb⟩

/-- **Terms of the fragment compile backwards.** -/
theorem tm_backward {Γ : List Shape} {a : Tm (Opcode sigs)} {s : Shape} (h : TmFits sigs Γ a s) :
    TmBwd oracle Γ a s := by
  induction h with
  | var hΓ => exact bwd_var hΓ
  | unit => exact bwd_unit
  | pair _ _ iha ihb => exact bwd_pair iha ihb
  | op hf _ ih => exact bwd_op hf ih
  | let₁ _ _ iha ihb => exact bwd_let₁ iha ihb
  | let₂ _ _ iha ihb => exact bwd_let₂ iha ihb

end Silmaril.Proofs.Machine.OfLambdaSSA
