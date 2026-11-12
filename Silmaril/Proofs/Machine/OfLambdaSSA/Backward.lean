module

public import Silmaril.Proofs.Machine.OfLambdaSSA.Forward

/-!
# Backwards: an RTL run is a lambda-SSA evaluation

By induction on the region, with a run budget for the blocks a region jumps to.
`budget 0` allows nothing and `budget (n + 1)` is a run of at most `n` further
transfers, so a block whose run has budget `n` transfers to blocks with a
smaller budget. That bounds the chain of jumps between the blocks of a `cfg`
(`fol_backward`), which is what makes the converse provable without
determinism.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (extend)

variable {sigs : List Silmaril.Machine.RTL.Signature} {oracle : CallOracle} {fn : SSA.Func ℕ}

variable (oracle fn) in
/-- Runs that may make fewer than `n` transfers after the one that starts them. -/
def budget : ℕ → Label → Frame ℕ → Memory → Exit → Prop
  | 0 => fun _ _ _ _ => False
  | n + 1 => Func.ExecIn oracle fn n

theorem budget_mono {n n' : ℕ} (hn : n ≤ n') {l : Label} {fr : Frame ℕ} {m : Memory} {out : Exit}
    (h : budget oracle fn n l fr m out) : budget oracle fn n' l fr m out := by
  match n, n', hn, h with
  | n + 1, n' + 1, hn, h => exact execIn_mono (by omega) h

/-- A run with budget `n` of a block is its ops and terminator with a smaller budget. -/
theorem run_of_budget {n : ℕ} {l : Label} {b : SSA.Block ℕ} (hb : fn.block? l = some b) {fr : Frame ℕ}
    {m : Memory} {out : Exit} (h : budget oracle fn n l fr m out) :
    ∃ n' < n, Run oracle fn (budget oracle fn n') b.ops b.term fr m out := by
  match n, h with
  | 1, h =>
    cases h with
    | ret hb' hops hterm hargs =>
      obtain rfl := Option.some.inj (hb.symm.trans hb')
      exact ⟨0, by omega, _, _, hops, by rw [hterm]; exact ⟨_, hargs, rfl⟩⟩
    | trap hb' hops hterm =>
      obtain rfl := Option.some.inj (hb.symm.trans hb')
      exact ⟨0, by omega, _, _, hops, by rw [hterm]; rfl⟩
  | n + 2, h => exact ⟨n + 1, by omega, (execIn_succ_iff_run hb).1 h⟩

/-- A continuation allows whatever a weaker run predicate allows. -/
theorem cont_mono {E E' : Label → Frame ℕ → Memory → Exit → Prop}
    (hE : ∀ {l fr m out}, E l fr m out → E' l fr m out) {L : List (Target × ℕ)} {ℓ : ℕ}
    {ws : List Word} {frX : Frame ℕ} {m : Memory} {out : Exit}
    (h : Cont fn E L ℓ ws frX m out) : Cont fn E' L ℓ ws frX m out := by
  unfold Cont at h ⊢
  rcases hℓ : L[ℓ]? with _ | ⟨tgt, w⟩
  · rw [hℓ] at h
    exact h
  · rw [hℓ] at h
    cases tgt with
    | block b =>
      obtain ⟨bt, fr', hbt, hw, hex⟩ := h
      exact ⟨bt, fr', hbt, hw, hE hex⟩
    | ret => exact h
    | trap => exact h

variable (oracle fn) in
/-- **Backwards, for a region.** If what the region compiled to runs, the region
evaluates, and leaving through its exit does the rest of the run. -/
def RegBwd (Γ : List Shape) (r : Region (Opcode sigs)) (a : Ann) (Lw : List ℕ) : Prop :=
  ∀ (n : ℕ) {ρ : List (List ℕ)} {L : List (Target × ℕ)} {e e' : Emit} {ops : List (Op ℕ)}
    {t : Term ℕ} {env : Semantics.Env Word} {fr : Frame ℕ} {m : Memory} {out : Exit},
    L.map Prod.snd = Lw → regionOps r a ρ L e = some (ops, t, e') → Inst fn e'.blocks →
    Agrees Γ ρ env fr → Below Γ ρ e.nextReg → Run oracle fn (budget oracle fn n) ops t fr m out →
    ∃ ℓ v m' frX ws, Semantics.Region.Eval (Opcode.step oracle) env r m ℓ v m' ∧
      v = packValues ws ∧ Same e.nextReg fr frX ∧ (∀ p, L[ℓ]? = some p → ws.length = p.2) ∧
      Cont fn (budget oracle fn n) L ℓ ws frX m' out

theorem regBwd_br {Γ : List Shape} {ℓ w : ℕ} {Lw : List ℕ} {arg : Tm (Opcode sigs)}
    (hw : Lw[ℓ]? = some w) (harg : TmFits sigs Γ arg (.tuple w)) :
    RegBwd oracle fn Γ (.br ℓ arg) .br Lw := by
  intro n ρ L e e' ops t env fr m out hL hc hinst hag hb hrun
  obtain ⟨tgt, w', rs, hLℓ, htm, -, rfl⟩ := regionOps_br hc
  obtain ⟨fr₁, m₁, x₁, term⟩ := hrun
  obtain ⟨v, vals, hev, hrd, ⟨rfl, hvl⟩, -⟩ := tm_backward harg htm hag hb x₁
  refine ⟨ℓ, _, m₁, fr₁, vals, .br hev, rfl, tm_same htm x₁,
    fun p hp => by rw [hvl, width_eq hL hp hw], ?_⟩
  unfold Cont
  rw [hLℓ]
  cases tgt with
  | block b =>
    obtain ⟨vals', bt, fr', hrd', hbt, hw, hex⟩ := term
    obtain rfl := Option.some.inj (hrd.symm.trans hrd')
    exact ⟨bt, fr', hbt, hw, hex⟩
  | ret =>
    obtain ⟨vals', hrd', rfl⟩ := term
    obtain rfl := Option.some.inj (hrd.symm.trans hrd')
    rfl
  | trap => exact term

theorem regBwd_let₁ {Γ : List Shape} {Lw : List ℕ} {a : Tm (Opcode sigs)}
    {body : Region (Opcode sigs)} {ab : Ann} {s : Shape} (ha : TmFits sigs Γ a s)
    (ih : RegBwd oracle fn (s :: Γ) body ab Lw) : RegBwd oracle fn Γ (.let₁ a body) (.let₁ ab) Lw := by
  intro n ρ L e e' ops t env fr m out hL hc hinst hag hb hrun
  obtain ⟨rv, ops₁, e₁, ops₂, htm, hrc, rfl⟩ := regionOps_let₁ hc
  obtain ⟨fr₂, m₂, x, term⟩ := hrun
  obtain ⟨fr₁, m₁, x₁, x₂⟩ := ops_exec_append_inv x
  obtain ⟨va, ws, eva, hrd, hh, lt⟩ := tm_backward ha htm hag hb x₁
  have bnd := tmRegs_bounds htm
  have same₁ := tm_same htm x₁
  obtain ⟨ℓ, v, m', frX, ws', hev, hv, hs, hl, hcont⟩ := ih n hL hrc hinst
    ((hag.same hb same₁).cons hrd hh) ((hb.mono bnd.1).cons lt) ⟨fr₂, m₂, x₂, term⟩
  exact ⟨ℓ, v, m', frX, ws', .let₁ eva hev, hv, same₁.trans (hs.mono bnd.1), hl, hcont⟩

theorem regBwd_let₂ {Γ : List Shape} {Lw : List ℕ} {a : Tm (Opcode sigs)}
    {body : Region (Opcode sigs)} {ab : Ann} {k : ℕ} (ha : TmFits sigs Γ a (.tuple (k + 1)))
    (ih : RegBwd oracle fn (.tuple k :: .word :: Γ) body ab Lw) :
    RegBwd oracle fn Γ (.let₂ a body) (.let₂ ab) Lw := by
  intro n ρ L e e' ops t env fr m out hL hc hinst hag hb hrun
  obtain ⟨g, rest, ops₁, e₁, ops₂, htm, hrc, rfl⟩ := regionOps_let₂ hc
  obtain ⟨fr₂, m₂, x, term⟩ := hrun
  obtain ⟨fr₁, m₁, x₁, x₂⟩ := ops_exec_append_inv x
  obtain ⟨va, ws, eva, hrd, ⟨rfl, hlen⟩, lt⟩ := tm_backward ha htm hag hb x₁
  have bnd := tmRegs_bounds htm
  have same₁ := tm_same htm x₁
  obtain ⟨w, ws₁, rfl⟩ : ∃ w ws₁, ws = w :: ws₁ := List.exists_cons_of_length_pos (by omega)
  obtain ⟨g', rest', heq, hr₁, hrest₁⟩ := readAll_cons_split hrd
  obtain ⟨rfl, rfl⟩ := List.cons.inj heq
  have hw' : Shape.word.Holds (.atom w) [w] := ⟨w, rfl, rfl⟩
  have hws₁ : (Shape.tuple k).Holds (packValues ws₁) ws₁ := ⟨rfl, by simpa using hlen⟩
  have hag₁ := ((hag.same hb same₁).cons hr₁ hw').cons hrest₁ hws₁
  have hb₁ : Below (.tuple k :: .word :: Γ) (rest :: [g] :: ρ) e₁.nextReg :=
    ((hb.mono bnd.1).cons fun x hx => lt x (by simp_all)).cons fun x hx => lt x (by simp [hx])
  obtain ⟨ℓ, v, m', frX, ws', hev, hv, hs, hl, hcont⟩ :=
    ih n hL hrc hinst hag₁ hb₁ ⟨fr₂, m₂, x₂, term⟩
  exact ⟨ℓ, v, m', frX, ws', .let₂ eva hev, hv, same₁.trans (hs.mono bnd.1), hl, hcont⟩

/-- The branch test of a `case`, backwards: the scrutinee's ops ran and the
register holds `x`, so the test evaluates to the injection `x` selects. -/
theorem regBwd_test {Γ : List Shape} {ρ : List (List ℕ)} {e e₁ : Emit} {arg : Tm (Opcode sigs)}
    {c : ℕ} {ops : List (Op ℕ)} (harg : TmFits sigs Γ arg (.tuple 1))
    (htm : tmRegs ρ arg e = some ([c], ops, e₁)) {env : Semantics.Env Word} {fr fr₁ : Frame ℕ}
    (hag : Agrees Γ ρ env fr) (hb : Below Γ ρ e.nextReg) {m m₁ : Memory}
    (hx₁ : Ops.Exec oracle ops fr m fr₁ m₁) {x : Word} (hx : fr₁.get c = some x) :
    Semantics.Tm.Eval (Opcode.step oracle) env (.op .test arg) m
      (if x = 0 then .inr .unit else .inl .unit) m₁ := by
  obtain ⟨vx, ws, evx, hrd, ⟨rfl, -⟩, -⟩ := tm_backward harg htm hag hb hx₁
  obtain ⟨x', hx', rfl⟩ := readAll_one hrd
  have hxx : x' = x := Option.some.inj (hx'.symm.trans hx)
  subst x'
  exact .op evx (Opcode.step_test_iff.2 ⟨rfl, rfl⟩)

/-- A conditional branch whose arms are plain branches, backwards. -/
theorem regBwd_case_cond {Γ : List Shape} {Lw : List ℕ} {l r : Region (Opcode sigs)}
    {al ar : Ann} (ihl : RegBwd oracle fn (.tuple 0 :: Γ) l al Lw)
    (ihr : RegBwd oracle fn (.tuple 0 :: Γ) r ar Lw) {n : ℕ} {ρ : List (List ℕ)}
    {L : List (Target × ℕ)} {e₁ e₂ e' : Emit} {c t₁ t₂ : ℕ} {rs₁ rs₂ : List ℕ}
    (hL : L.map Prod.snd = Lw) (hL' : regionOps l al ([] :: ρ) L e₁ = some ([], .jump t₁ rs₁, e₂))
    (hR' : regionOps r ar ([] :: ρ) L e₂ = some ([], .jump t₂ rs₂, e')) (hinst : Inst fn e'.blocks)
    {env : Semantics.Env Word} {fr₁ : Frame ℕ} {m₁ : Memory} {out : Exit}
    (hag : Agrees (.tuple 0 :: Γ) ([] :: ρ) env fr₁) (hb : Below (.tuple 0 :: Γ) ([] :: ρ) e₁.nextReg)
    (term : TermRun fn (budget oracle fn n) (.cond c t₁ rs₁ t₂ rs₂) fr₁ m₁ out) :
    ∃ x, fr₁.get c = some x ∧ ∃ ℓ v m' frX ws,
      (if x = 0 then Semantics.Region.Eval (Opcode.step oracle) env r m₁ ℓ v m'
        else Semantics.Region.Eval (Opcode.step oracle) env l m₁ ℓ v m') ∧
      v = packValues ws ∧ Same e₁.nextReg fr₁ frX ∧ (∀ p, L[ℓ]? = some p → ws.length = p.2) ∧
      Cont fn (budget oracle fn n) L ℓ ws frX m' out := by
  obtain ⟨x, vals, bt, fr', hx, hrd, hbt, hw, hex⟩ := term
  refine ⟨x, hx, ?_⟩
  have up := (regionOps_mono hL').1
  by_cases hx0 : x = 0
  · rw [ite_eq_left hx0] at hrd hbt hex
    obtain ⟨ℓ, v, m', frX, ws, hev, hv, hs, hl, hcont⟩ := ihr n hL hR' hinst hag (hb.mono up)
      ⟨fr₁, m₁, .nil, vals, bt, fr', hrd, hbt, hw, hex⟩
    refine ⟨ℓ, v, m', frX, ws, ?_, hv, hs.mono up, hl, hcont⟩
    rw [ite_eq_left hx0]
    exact hev
  · rw [ite_eq_right hx0] at hrd hbt hex
    obtain ⟨ℓ, v, m', frX, ws, hev, hv, hs, hl, hcont⟩ := ihl n hL hL'
      (hinst.sub (regionOps_mono hR').2.1) hag hb ⟨fr₁, m₁, .nil, vals, bt, fr', hrd, hbt, hw, hex⟩
    refine ⟨ℓ, v, m', frX, ws, ?_, hv, hs, hl, hcont⟩
    rw [ite_eq_right hx0]
    exact hev

/-- An arm of the diamond, backwards: the jump into its block, with no arguments,
runs the arm's region with a smaller budget. -/
theorem regBwd_arm {Γ : List Shape} {Lw : List ℕ} {l : Region (Opcode sigs)} {al : Ann}
    (ih : RegBwd oracle fn (.tuple 0 :: Γ) l al Lw) {n : ℕ} {ρ : List (List ℕ)}
    {L : List (Target × ℕ)} {u u' : Emit} {opsL : List (Op ℕ)} {tL : Term ℕ} {lbl : ℕ}
    (hL : L.map Prod.snd = Lw) (hc : regionOps l al ([] :: ρ) L u = some (opsL, tL, u'))
    (hinst : Inst fn u'.blocks) (hbt : fn.block? lbl = some ⟨[], opsL, tL⟩)
    {env : Semantics.Env Word} {fr₁ : Frame ℕ} {m₁ : Memory} {out : Exit} {vals : List Word}
    {bt : SSA.Block ℕ} {fr' : Frame ℕ}
    (hag : Agrees (.tuple 0 :: Γ) ([] :: ρ) env fr₁) (hb : Below (.tuple 0 :: Γ) ([] :: ρ) u.nextReg)
    (hrd : fr₁.readAll [] = some vals) (hbt' : fn.block? lbl = some bt)
    (hw : fr₁.writeAll bt.params vals = some fr') (hex : budget oracle fn n lbl fr' m₁ out) :
    ∃ ℓ v m' frX ws, Semantics.Region.Eval (Opcode.step oracle) env l m₁ ℓ v m' ∧
      v = packValues ws ∧ Same u.nextReg fr₁ frX ∧ (∀ p, L[ℓ]? = some p → ws.length = p.2) ∧
      Cont fn (budget oracle fn n) L ℓ ws frX m' out := by
  obtain rfl : bt = ⟨[], opsL, tL⟩ := Option.some.inj (hbt'.symm.trans hbt)
  obtain rfl : vals = [] := by simpa using hrd.symm
  obtain rfl : fr' = fr₁ := (Option.some.inj hw).symm
  obtain ⟨n', hn', run⟩ := run_of_budget hbt hex
  obtain ⟨ℓ, v, m', frX, ws, hev, hv, hs, hl, hcont⟩ := ih n' hL hc hinst hag hb run
  exact ⟨ℓ, v, m', frX, ws, hev, hv, hs, hl, cont_mono (budget_mono hn'.le) hcont⟩

/-- A diamond, backwards: the conditional terminator enters the block of the arm
the word selects. -/
theorem regBwd_diamond {Γ : List Shape} {Lw : List ℕ} {l r : Region (Opcode sigs)} {al ar : Ann}
    (ihl : RegBwd oracle fn (.tuple 0 :: Γ) l al Lw) (ihr : RegBwd oracle fn (.tuple 0 :: Γ) r ar Lw)
    {n : ℕ} {ρ : List (List ℕ)} {L : List (Target × ℕ)} {e₁ e₃ e₄ : Emit} {c : ℕ}
    {opsL opsR : List (Op ℕ)} {tL tR : Term ℕ} (hL : L.map Prod.snd = Lw)
    (hL' : regionOps l al ([] :: ρ) L { e₁ with nextLabel := e₁.nextLabel + 1 } = some (opsL, tL, e₃))
    (hR' : regionOps r ar ([] :: ρ) L
      { e₃ with blocks := (e₁.nextLabel, ⟨[], opsL, tL⟩) :: e₃.blocks } = some (opsR, tR, e₄))
    (hinst : Inst fn ((e₄.nextLabel, ⟨[], opsR, tR⟩) :: e₄.blocks))
    {env : Semantics.Env Word} {fr₁ : Frame ℕ} {m₁ : Memory} {out : Exit}
    (hag : Agrees (.tuple 0 :: Γ) ([] :: ρ) env fr₁) (hb : Below (.tuple 0 :: Γ) ([] :: ρ) e₁.nextReg)
    (term : TermRun fn (budget oracle fn n) (.cond c e₁.nextLabel [] e₄.nextLabel []) fr₁ m₁ out) :
    ∃ x, fr₁.get c = some x ∧ ∃ ℓ v m' frX ws,
      (if x = 0 then Semantics.Region.Eval (Opcode.step oracle) env r m₁ ℓ v m'
        else Semantics.Region.Eval (Opcode.step oracle) env l m₁ ℓ v m') ∧
      v = packValues ws ∧ Same e₁.nextReg fr₁ frX ∧ (∀ p, L[ℓ]? = some p → ws.length = p.2) ∧
      Cont fn (budget oracle fn n) L ℓ ws frX m' out := by
  obtain ⟨x, vals, bt, fr', hx, hrd, hbt, hw, hex⟩ := term
  refine ⟨x, hx, ?_⟩
  have kept := (regionOps_mono hR').2.1
  by_cases hx0 : x = 0
  · rw [ite_eq_left hx0] at hrd hbt hex
    have up := (regionOps_mono hL').1
    obtain ⟨ℓ, v, m', frX, ws, hev, hv, hs, hl, hcont⟩ := regBwd_arm ihr hL hR'
      (hinst.sub fun _ hp => List.mem_cons_of_mem _ hp) (hinst _ List.mem_cons_self)
      hag (hb.mono up) hrd hbt hw hex
    refine ⟨ℓ, v, m', frX, ws, ?_, hv, hs.mono up, hl, hcont⟩
    rw [ite_eq_left hx0]
    exact hev
  · rw [ite_eq_right hx0] at hrd hbt hex
    obtain ⟨ℓ, v, m', frX, ws, hev, hv, hs, hl, hcont⟩ := regBwd_arm ihl hL hL'
      (hinst.sub fun _ hp => List.mem_cons_of_mem _ (kept (List.mem_cons_of_mem _ hp)))
      (hinst _ (List.mem_cons_of_mem _ (kept List.mem_cons_self))) hag hb hrd hbt hw hex
    refine ⟨ℓ, v, m', frX, ws, ?_, hv, hs, hl, hcont⟩
    rw [ite_eq_right hx0]
    exact hev

/-- A `case` on the test of `x` takes the arm `x` selects. -/
theorem case_of_ite {env : Semantics.Env Word} {d : Tm (Opcode sigs)} {l r : Region (Opcode sigs)}
    {m m₁ m' : Memory} {x : Word} {ℓ : ℕ} {v : Value Word}
    (test : Semantics.Tm.Eval (Opcode.step oracle) env d m
      (if x = 0 then .inr .unit else .inl .unit) m₁)
    (hev : if x = 0 then Semantics.Region.Eval (Opcode.step oracle) (extend env .unit) r m₁ ℓ v m'
      else Semantics.Region.Eval (Opcode.step oracle) (extend env .unit) l m₁ ℓ v m') :
    Semantics.Region.Eval (Opcode.step oracle) env (.case d l r) m ℓ v m' := by
  by_cases hx0 : x = 0
  · rw [ite_eq_left hx0] at test hev
    exact .case_inr test hev
  · rw [ite_eq_right hx0] at test hev
    exact .case_inl test hev

theorem regBwd_case {Γ : List Shape} {Lw : List ℕ} {arg : Tm (Opcode sigs)}
    {l r : Region (Opcode sigs)} {al ar : Ann} (harg : TmFits sigs Γ arg (.tuple 1))
    (ihl : RegBwd oracle fn (.tuple 0 :: Γ) l al Lw) (ihr : RegBwd oracle fn (.tuple 0 :: Γ) r ar Lw) :
    RegBwd oracle fn Γ (.case (.op .test arg) l r) (.case al ar) Lw := by
  intro n ρ L e e' ops t env fr m out hL hc hinst hag hb hrun
  obtain ⟨c, e₁, htm, hcases⟩ := regionOps_case hc
  obtain ⟨fr₁, m₁, x₁, term⟩ := hrun
  have same₁ := tm_same htm x₁
  have bnd := tmRegs_bounds htm
  have hag₁ := (hag.same hb same₁).unit
  have hb₁ := (hb.mono bnd.1).cons (s := .tuple 0) (g := []) (by simp)
  rcases hcases with ⟨t₁, rs₁, t₂, rs₂, e₂, hL', hR', rfl⟩ |
      ⟨opsL, tL, e₃, opsR, tR, e₄, hL', hR', rfl, rfl⟩
  · obtain ⟨x, hx, ℓ, v, m', frX, ws, hev, hv, hs, hl, hcont⟩ :=
      regBwd_case_cond ihl ihr hL hL' hR' hinst hag₁ hb₁ term
    exact ⟨ℓ, v, m', frX, ws, case_of_ite (regBwd_test harg htm hag hb x₁ hx) hev, hv,
      same₁.trans (hs.mono bnd.1), hl, hcont⟩
  · obtain ⟨x, hx, ℓ, v, m', frX, ws, hev, hv, hs, hl, hcont⟩ :=
      regBwd_diamond ihl ihr hL hL' hR' hinst hag₁ hb₁ term
    exact ⟨ℓ, v, m', frX, ws, case_of_ite (regBwd_test harg htm hag hb x₁ hx) hev, hv,
      same₁.trans (hs.mono bnd.1), hl, hcont⟩

/-- Entering block `first` of a `cfg` with the words `vs`: the frame the jump
writes agrees with the block's context. -/
theorem block_entry {Γ : List Shape} {ρ : List (List ℕ)} {env : Semantics.Env Word}
    {fr₀ frX fr' : Frame ℕ} {n₀ x w : ℕ} {vs : List Word} (hag : Agrees Γ ρ env fr₀)
    (hb : Below Γ ρ n₀) (hs : Same n₀ fr₀ frX) (hx : n₀ ≤ x)
    (hw : frX.writeAll (freshRegs x w) vs = some fr') :
    Same n₀ frX fr' ∧
      Agrees (.tuple w :: Γ) (freshRegs x w :: ρ) (extend env (packValues vs)) fr' ∧
      Below (.tuple w :: Γ) (freshRegs x w :: ρ) (x + w) := by
  have keep : Same n₀ frX fr' := fun y hy => get_writeAll_of_not_mem hw fun hm => by
    have := (mem_freshRegs.mp hm).1
    omega
  have hold : (Shape.tuple w).Holds (packValues vs) vs :=
    ⟨rfl, by simpa using (writeAll_length hw).symm⟩
  refine ⟨keep, (hag.same hb (hs.trans keep)).cons (readAll_writeAll hw (freshRegs_nodup _ _)) hold,
    (hb.mono (by omega)).cons fun y hy => (mem_freshRegs.mp hy).2⟩

/-- Entering block `first` of a `cfg`, backwards: the block's region evaluates,
and its exit continues the run with a smaller budget. -/
theorem enter_block_bwd {env : Semantics.Env Word} {k : ℕ} {blocks : Fin k → Region (Opcode sigs)}
    {abs : List Ann} {ws : List ℕ} {Γ : List Shape} {Lw : List ℕ} {ρ : List (List ℕ)}
    {L : List (Target × ℕ)} {base n₀ : ℕ} {fr₀ : Frame ℕ} (hws : ws.length = k)
    (hL : L.map Prod.snd = Lw) (hcfg : CfgInst fn blocks abs ws ρ (inner base ws k ++ L) base n₀)
    (hag : Agrees Γ ρ env fr₀) (hb : Below Γ ρ n₀)
    (ihB : ∀ i : Fin k, RegBwd oracle fn (.tuple (ws.getD i 0) :: Γ) (blocks i) (abs.getD i .br)
      (ws ++ Lw))
    {N first : ℕ} (inside : first < k) {vs : List Word} {frX : Frame ℕ} {m : Memory} {out : Exit}
    (hs : Same n₀ fr₀ frX) (hcont : Cont fn (budget oracle fn N) (inner base ws k ++ L) first vs frX m out) :
    ∃ N' < N, ∃ next ws₁ m₁ frY,
      Semantics.Region.Eval (Opcode.step oracle) (extend env (packValues vs)) (blocks ⟨first, inside⟩)
        m next (packValues ws₁) m₁ ∧ Same n₀ fr₀ frY ∧
      (∀ p, (inner base ws k ++ L)[next]? = some p → ws₁.length = p.2) ∧
      Cont fn (budget oracle fn N') (inner base ws k ++ L) next ws₁ frY m₁ out := by
  have hget : (inner base ws k ++ L)[first]? = some (.block (base + first), ws.getD first 0) := by
    rw [List.getElem?_append_left (by simpa using inside)]
    exact inner_getElem? inside
  unfold Cont at hcont
  rw [hget] at hcont
  obtain ⟨bt, fr', hbt, hw, hex⟩ := hcont
  obtain ⟨x, opsB, tB, u', hx, hcomp, hinst, hbt'⟩ := hcfg ⟨first, inside⟩
  obtain rfl : bt = _ := Option.some.inj (hbt.symm.trans hbt')
  obtain ⟨N', hN', run⟩ := run_of_budget hbt' hex
  obtain ⟨keep, hag', hb'⟩ := block_entry hag hb hs hx hw
  obtain ⟨next, middle, m₁, frY, ws₁, hev, rfl, hsY, hlY, hcontY⟩ :=
    ihB ⟨first, inside⟩ N' (by rw [List.map_append, inner_widths hws, hL]) hcomp hinst hag' hb' run
  exact ⟨N', hN', next, ws₁, m₁, frY, hev,
    (hs.trans keep).trans (hsY.mono (Nat.le_trans hx (Nat.le_add_right _ _))), hlY, hcontY⟩

/-- **Backwards, for the blocks of a `cfg`**: a jump into a block, within the
budget, is a run of internal transfers ending at an exit of the `cfg`. -/
theorem fol_backward {env : Semantics.Env Word} {k : ℕ} {blocks : Fin k → Region (Opcode sigs)}
    {abs : List Ann} {ws : List ℕ} {Γ : List Shape} {Lw : List ℕ} {ρ : List (List ℕ)}
    {L : List (Target × ℕ)} {base n₀ : ℕ} {fr₀ : Frame ℕ} (hws : ws.length = k)
    (hL : L.map Prod.snd = Lw) (hcfg : CfgInst fn blocks abs ws ρ (inner base ws k ++ L) base n₀)
    (hag : Agrees Γ ρ env fr₀) (hb : Below Γ ρ n₀)
    (ihB : ∀ i : Fin k, RegBwd oracle fn (.tuple (ws.getD i 0) :: Γ) (blocks i) (abs.getD i .br)
      (ws ++ Lw)) :
    ∀ (N first : ℕ) (vs : List Word) (frX : Frame ℕ) (m : Memory) (out : Exit), Same n₀ fr₀ frX →
      (∀ p, (inner base ws k ++ L)[first]? = some p → vs.length = p.2) →
      Cont fn (budget oracle fn N) (inner base ws k ++ L) first vs frX m out →
      ∃ ℓ v m' frZ ws', Semantics.Region.Follow (Opcode.step oracle) env blocks first
          (packValues vs) m ℓ v m' ∧ v = packValues ws' ∧ Same n₀ fr₀ frZ ∧
        (∀ p, L[ℓ]? = some p → ws'.length = p.2) ∧ Cont fn (budget oracle fn N) L ℓ ws' frZ m' out := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro first vs frX m out hs hlen hcont
  by_cases inside : first < k
  · obtain ⟨N', hN', next, ws₁, m₁, frY, hev, hsY, hlY, hcontY⟩ :=
      enter_block_bwd hws hL hcfg hag hb ihB inside hs hcont
    obtain ⟨ℓ, v, m', frZ, ws', hfol, hv, hsZ, hlZ, hcontZ⟩ :=
      ih N' hN' next ws₁ frY m₁ out hsY hlY hcontY
    exact ⟨ℓ, v, m', frZ, ws', .step inside hev hfol, hv, hsZ, hlZ,
      cont_mono (budget_mono hN'.le) hcontZ⟩
  · have long : (inner base ws k).length ≤ first := by simpa using inside
    rw [cont_append long, inner_length] at hcont
    refine ⟨first - k, packValues vs, m, frX, vs, .exit (by omega), rfl, hs, fun p hp => hlen p ?_,
      hcont⟩
    rw [List.getElem?_append_right long, inner_length]
    exact hp

theorem regBwd_cfg {Γ : List Shape} {Lw : List ℕ} {entry : Region (Opcode sigs)} {k : ℕ}
    {blocks : Fin k → Region (Opcode sigs)} {ws : List ℕ} {ae : Ann} {abs : List Ann}
    (hws : ws.length = k) (ihE : RegBwd oracle fn Γ entry ae (ws ++ Lw))
    (ihB : ∀ i : Fin k, RegBwd oracle fn (.tuple (ws.getD i 0) :: Γ) (blocks i) (abs.getD i .br)
      (ws ++ Lw)) :
    RegBwd oracle fn Γ (.cfg entry k blocks) (.cfg ws ae abs) Lw := by
  intro n ρ L e e' ops t env fr m out hL hc hinst hag hb hrun
  obtain ⟨e₁, hE, hfold⟩ := regionOps_cfg hc
  obtain ⟨hinst₁, hcfg⟩ := cfgInst_of_regionOps hE hfold hinst
  obtain ⟨first, initial, m₁, frX, ws₀, hevE, rfl, hs, hl, hcont⟩ :=
    ihE n (by rw [List.map_append, inner_widths hws, hL]) hE hinst₁ hag hb hrun
  obtain ⟨ℓ, v, m', frZ, ws', hfol, hv, hsZ, hlZ, hcontZ⟩ :=
    fol_backward hws hL hcfg hag hb ihB n first ws₀ frX m₁ out hs hl hcont
  exact ⟨ℓ, v, m', frZ, ws', .cfg hevE hfol, hv, hsZ, hlZ, hcontZ⟩

/-- **Backwards.** Every run of what a region of the fragment compiles to is an
evaluation of the region. -/
theorem region_backward {Γ : List Shape} {r : Region (Opcode sigs)} {a : Ann} {Lw : List ℕ}
    (h : RegionFits sigs Γ r a Lw) : RegBwd oracle fn Γ r a Lw := by
  induction h with
  | br hw harg => exact regBwd_br hw harg
  | let₁ ha _ ih => exact regBwd_let₁ ha ih
  | let₂ ha _ ih => exact regBwd_let₂ ha ih
  | case harg _ _ ihl ihr => exact regBwd_case harg ihl ihr
  | cfg hws _ _ ihE ihB => exact regBwd_cfg hws ihE ihB

end Silmaril.Proofs.Machine.OfLambdaSSA
