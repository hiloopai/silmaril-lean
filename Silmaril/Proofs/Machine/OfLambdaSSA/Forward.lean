module

public import Silmaril.Proofs.Machine.OfLambdaSSA.Compile

/-!
# Forwards: a lambda-SSA evaluation is an RTL run

By induction on the evaluation, in continuation-passing form. A region compiled
into the ops and terminator of a block (`RegFwd`) runs them, given what the
function does once the region has exited; the blocks of a `cfg` (`FolFwd`) are
entered by jumps, given what happens once the `cfg` has exited. Registers below
where a region's compilation started are never written while it runs, so the
values a continuation relies on survive.
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

variable (fn) in
/-- The blocks `bs` are blocks of `fn`. -/
def Inst (bs : List (ℕ × SSA.Block ℕ)) : Prop := ∀ p ∈ bs, fn.block? p.1 = some p.2

theorem Inst.sub {bs bs' : List (ℕ × SSA.Block ℕ)} (h : Inst fn bs) (hs : bs' ⊆ bs) : Inst fn bs' :=
  fun p hp => h p (hs hp)

/-- The width a label carries, read off the targets or off the widths. -/
theorem width_eq {L : List (Target × ℕ)} {Lw : List ℕ} (hL : L.map Prod.snd = Lw) {ℓ w : ℕ}
    {p : Target × ℕ} (hp : L[ℓ]? = some p) (hw : Lw[ℓ]? = some w) : p.2 = w := by
  have := congrArg (·[ℓ]?) hL
  simp only [List.getElem?_map, hp, hw, Option.map_some, Option.some.injEq] at this
  exact this

variable (oracle fn) in
/-- **Forwards, for a region.** If the region compiled into `ops` and `t`
evaluates to label `ℓ` and value `v`, then `ops` and `t` run to whatever the
function does after leaving through `ℓ` with the words of `v`. -/
def RegFwd (env : Semantics.Env Word) (r : Region (Opcode sigs)) (m : Memory) (ℓ : ℕ)
    (v : Value Word) (m' : Memory) : Prop :=
  ∀ {Γ : List Shape} {a : Ann} {Lw : List ℕ} {ρ : List (List ℕ)} {L : List (Target × ℕ)}
    {e e' : Emit} {ops : List (Op ℕ)} {t : Term ℕ} {fr : Frame ℕ} {out : Exit},
    RegionFits sigs Γ r a Lw → L.map Prod.snd = Lw → regionOps r a ρ L e = some (ops, t, e') →
    Inst fn e'.blocks → Agrees Γ ρ env fr → Below Γ ρ e.nextReg →
    (∀ frX ws, Same e.nextReg fr frX → v = packValues ws →
      (∀ p, L[ℓ]? = some p → ws.length = p.2) → ℓ < L.length →
      Cont fn (Func.Exec oracle fn) L ℓ ws frX m' out) →
    Run oracle fn (Func.Exec oracle fn) ops t fr m out

variable (fn) in
/-- Every block of a `cfg` was compiled, at the labels and widths `inner` gives,
from a state at or above `n₀`, and is a block of `fn`. -/
def CfgInst {k : ℕ} (blocks : Fin k → Region (Opcode sigs)) (abs : List Ann) (ws : List ℕ)
    (ρ : List (List ℕ)) (L : List (Target × ℕ)) (base n₀ : ℕ) : Prop :=
  ∀ i : Fin k, ∃ (x : Emit) (opsB : List (Op ℕ)) (tB : Term ℕ) (u' : Emit), n₀ ≤ x.nextReg ∧
    regionOps (blocks i) (abs.getD i.val .br) (freshRegs x.nextReg (ws.getD i.val 0) :: ρ) L
      { x with nextReg := x.nextReg + ws.getD i.val 0 } = some (opsB, tB, u') ∧
    Inst fn u'.blocks ∧ fn.block? (base + i.val) = some ⟨freshRegs x.nextReg (ws.getD i.val 0), opsB, tB⟩

/-- A compiled `cfg` installed its blocks. -/
theorem cfgInst_of_regionOps {ρ : List (List ℕ)} {L : List (Target × ℕ)} {e e₁ e' : Emit}
    {entry : Region (Opcode sigs)} {k : ℕ} {blocks : Fin k → Region (Opcode sigs)}
    {ws : List ℕ} {ae : Ann} {abs : List Ann} {ops : List (Op ℕ)} {t : Term ℕ}
    (hE : regionOps entry ae ρ (inner e.nextLabel ws k ++ L)
        { e with nextLabel := e.nextLabel + k } = some (ops, t, e₁))
    (hfold : (List.finRange k).foldl
        (fun acc i => acc.bind (cfgStep blocks abs ws ρ (inner e.nextLabel ws k ++ L)
          e.nextLabel i)) (some e₁) = some e')
    (hinst : Inst fn e'.blocks) :
    Inst fn e₁.blocks ∧ CfgInst fn blocks abs ws ρ (inner e.nextLabel ws k ++ L) e.nextLabel e.nextReg := by
  obtain ⟨-, b₁, each⟩ := fold_cfg _ cfgStep_mono _ e₁ e' hfold
  have bndE := regionOps_mono hE
  refine ⟨hinst.sub b₁, fun i => ?_⟩
  obtain ⟨x, y, hx, hy, hyb⟩ := each i (List.mem_finRange i)
  obtain ⟨opsB, tB, u', hcomp, rfl⟩ := cfgStep_some hy
  exact ⟨x, opsB, tB, u', bndE.1.trans hx, hcomp,
    hinst.sub fun p hp => hyb (List.mem_cons_of_mem _ hp), hinst _ (hyb List.mem_cons_self)⟩

variable (oracle fn) in
/-- **Forwards, for the blocks of a `cfg`.** Jumping to label `first` with the
words of `initial` does what the `cfg` does after it exits. -/
def FolFwd (env : Semantics.Env Word) {k : ℕ} (blocks : Fin k → Region (Opcode sigs)) (first : ℕ)
    (initial : Value Word) (m : Memory) (ℓ : ℕ) (v : Value Word) (m' : Memory) : Prop :=
  ∀ {Γ : List Shape} {ws : List ℕ} {abs : List Ann} {Lw : List ℕ} {ρ : List (List ℕ)}
    {L : List (Target × ℕ)} {base n₀ : ℕ} {fr₀ : Frame ℕ} {out : Exit},
    (∀ i : Fin k, RegionFits sigs (.tuple (ws.getD i 0) :: Γ) (blocks i) (abs.getD i .br) (ws ++ Lw)) →
    ws.length = k → L.map Prod.snd = Lw → CfgInst fn blocks abs ws ρ (inner base ws k ++ L) base n₀ →
    Agrees Γ ρ env fr₀ → Below Γ ρ n₀ →
    (∀ frX vs, Same n₀ fr₀ frX → v = packValues vs →
      (∀ p, L[ℓ]? = some p → vs.length = p.2) → ℓ < L.length →
      Cont fn (Func.Exec oracle fn) L ℓ vs frX m' out) →
    ∀ frX vs, Same n₀ fr₀ frX → initial = packValues vs →
      (∀ p, (inner base ws k ++ L)[first]? = some p → vs.length = p.2) →
      first < (inner base ws k ++ L).length →
      Cont fn (Func.Exec oracle fn) (inner base ws k ++ L) first vs frX m out

theorem regFwd_br (hsigs : CallOracle.MatchesSigs oracle sigs) {env : Semantics.Env Word}
    {ℓ : ℕ} {arg : Tm (Opcode sigs)} {m m' : Memory} {v : Value Word}
    (hev : Semantics.Tm.Eval (Opcode.step oracle) env arg m v m') :
    RegFwd oracle fn env (.br ℓ arg) m ℓ v m' := by
  intro Γ a Lw ρ L e e' ops t fr out hfit hL hc hinst hag hb K
  cases hfit with
  | br hw harg =>
    obtain ⟨tgt, w', rs, hLℓ, htm, -, rfl⟩ := regionOps_br hc
    obtain ⟨fr₁, vals, x₁, hrd, ⟨rfl, hvl⟩, same, -⟩ := tm_forward hsigs harg htm hag hb hev
    have cont := K fr₁ vals same rfl (fun p hp => by rw [hvl, width_eq hL hp hw])
      (List.getElem?_eq_some_iff.mp hLℓ).1
    refine ⟨fr₁, m', x₁, ?_⟩
    unfold Cont at cont
    rw [hLℓ] at cont
    cases tgt with
    | block b =>
      obtain ⟨bt, fr', hbt, hw', hex⟩ := cont
      exact ⟨vals, bt, fr', hrd, hbt, hw', hex⟩
    | ret => exact ⟨vals, hrd, cont⟩
    | trap => exact cont

theorem regFwd_let₁ (hsigs : CallOracle.MatchesSigs oracle sigs) {env : Semantics.Env Word}
    {a : Tm (Opcode sigs)} {r : Region (Opcode sigs)} {m m₁ m' : Memory} {va v : Value Word}
    {ℓ : ℕ} (hev : Semantics.Tm.Eval (Opcode.step oracle) env a m va m₁)
    (ih : RegFwd oracle fn (extend env va) r m₁ ℓ v m') :
    RegFwd oracle fn env (.let₁ a r) m ℓ v m' := by
  intro Γ ab Lw ρ L e e' ops t fr out hfit hL hc hinst hag hb K
  cases hfit with
  | let₁ ha hr =>
    obtain ⟨rv, ops₁, e₁, ops₂, htm, hrc, rfl⟩ := regionOps_let₁ hc
    obtain ⟨fr₁, ws, x₁, hrd, hh, same₁, lt⟩ := tm_forward hsigs ha htm hag hb hev
    have bnd := tmRegs_bounds htm
    obtain ⟨fr₂, m₂, x₂, term⟩ := ih hr hL hrc hinst ((hag.same hb same₁).cons hrd hh)
      ((hb.mono bnd.1).cons lt) fun frX ws' hs hv hl hlt =>
        K frX ws' (same₁.trans (hs.mono bnd.1)) hv hl hlt
    exact ⟨fr₂, m₂, ops_exec_append x₁ x₂, term⟩

theorem regFwd_let₂ (hsigs : CallOracle.MatchesSigs oracle sigs) {env : Semantics.Env Word}
    {a : Tm (Opcode sigs)} {r : Region (Opcode sigs)} {m m₁ m' : Memory} {va vb v : Value Word}
    {ℓ : ℕ} (hev : Semantics.Tm.Eval (Opcode.step oracle) env a m (.pair va vb) m₁)
    (ih : RegFwd oracle fn (extend (extend env va) vb) r m₁ ℓ v m') :
    RegFwd oracle fn env (.let₂ a r) m ℓ v m' := by
  intro Γ ab Lw ρ L e e' ops t fr out hfit hL hc hinst hag hb K
  cases hfit with
  | @let₂ _ _ _ _ _ k ha hr =>
    obtain ⟨g, rest, ops₁, e₁, ops₂, htm, hrc, rfl⟩ := regionOps_let₂ hc
    obtain ⟨fr₁, ws, x₁, hrd, hh, same₁, lt⟩ := tm_forward hsigs ha htm hag hb hev
    have bnd := tmRegs_bounds htm
    obtain ⟨w, ws', rfl, hw, hws'⟩ := holds_split hh
    obtain ⟨g', rest', heq, hr₁, hrest₁⟩ := readAll_cons_split hrd
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    have hag₁ := ((hag.same hb same₁).cons hr₁ hw).cons hrest₁ hws'
    have hb₁ : Below (.tuple k :: .word :: Γ) (rest :: [g] :: ρ) e₁.nextReg :=
      ((hb.mono bnd.1).cons fun x hx => lt x (by simp_all)).cons fun x hx => lt x (by simp [hx])
    obtain ⟨fr₂, m₂, x₂, term⟩ := ih hr hL hrc hinst hag₁ hb₁ fun frX ws' hs hv hl hlt =>
      K frX ws' (same₁.trans (hs.mono bnd.1)) hv hl hlt
    exact ⟨fr₂, m₂, ops_exec_append x₁ x₂, term⟩

/-- The scrutinee of a `case` of the fragment: the branch test on one word. -/
theorem regFwd_test (hsigs : CallOracle.MatchesSigs oracle sigs) {Γ : List Shape}
    {ρ : List (List ℕ)} {e e₁ : Emit} {arg : Tm (Opcode sigs)} {c : ℕ} {ops : List (Op ℕ)}
    (harg : TmFits sigs Γ arg (.tuple 1)) (htm : tmRegs ρ arg e = some ([c], ops, e₁))
    {env : Semantics.Env Word} {fr : Frame ℕ} (hag : Agrees Γ ρ env fr) (hb : Below Γ ρ e.nextReg)
    {m m₁ : Memory} {d : Value Word}
    (hev : Semantics.Tm.Eval (Opcode.step oracle) env (.op .test arg) m d m₁) :
    ∃ fr₁ x, Ops.Exec oracle ops fr m fr₁ m₁ ∧ fr₁.get c = some x ∧
      d = (if x = 0 then .inr .unit else .inl .unit) ∧ Same e.nextReg fr fr₁ := by
  obtain ⟨vx, m₀, evx, hstep⟩ := eval_op_inv hev
  obtain ⟨fr₁, vals, x₁, hrd, ⟨rfl, -⟩, same₁, -⟩ := tm_forward hsigs harg htm hag hb evx
  obtain ⟨x, hx, rfl⟩ := readAll_one hrd
  obtain ⟨rfl, hsel⟩ := Opcode.step_test_iff.mp hstep
  exact ⟨fr₁, x, x₁, hx, hsel, same₁⟩

/-- Context facts for the arms of a `case`, which bind the empty tuple. -/
theorem arm_context {Γ : List Shape} {ρ : List (List ℕ)} {env : Semantics.Env Word}
    {fr fr₁ : Frame ℕ} {n n₁ : ℕ} (hag : Agrees Γ ρ env fr) (hb : Below Γ ρ n)
    (same : Same n fr fr₁) (hn : n ≤ n₁) :
    Agrees (.tuple 0 :: Γ) ([] :: ρ) (extend env .unit) fr₁ ∧
      Below (.tuple 0 :: Γ) ([] :: ρ) n₁ :=
  ⟨(hag.same hb same).unit, (hb.mono hn).cons (by simp)⟩

/-- A continuation that tolerates changes above `n` tolerates changes above `n₁ ≥ n`
made after a run that changed nothing below `n`. -/
theorem kshift {n n₁ : ℕ} {fr fr₁ : Frame ℕ} {P : Frame ℕ → List Word → Prop}
    (K : ∀ frX ws, Same n fr frX → P frX ws) (same : Same n fr fr₁) (hn : n ≤ n₁) :
    ∀ frX ws, Same n₁ fr₁ frX → P frX ws :=
  fun frX ws hs => K frX ws (same.trans (hs.mono hn))

/-- The left injection is the test of a nonzero word. -/
theorem test_inl {x : Word} {va : Value Word}
    (h : Value.inl va = if x = 0 then .inr .unit else .inl .unit) : x ≠ 0 ∧ va = .unit := by
  have hx0 : x ≠ 0 := fun h0 => by rw [h0, ite_eq_left rfl] at h; cases h
  exact ⟨hx0, Value.inl.inj (by rw [h, ite_eq_right hx0])⟩

/-- The right injection is the test of zero. -/
theorem test_inr {x : Word} {va : Value Word}
    (h : Value.inr va = if x = 0 then .inr .unit else .inl .unit) : x = 0 ∧ va = .unit := by
  have hx0 : x = 0 := by
    by_contra h0
    rw [ite_eq_right h0] at h
    cases h
  exact ⟨hx0, Value.inr.inj (by rw [h, ite_eq_left hx0])⟩

/-- A conditional terminator transfers as the jump of the arm it selects. -/
theorem termRun_cond_jump {E : Label → Frame ℕ → Memory → Exit → Prop} {c t₁ t₂ tj : ℕ}
    {rs₁ rs₂ rsj : List ℕ} {fr₁ : Frame ℕ} {m₁ : Memory} {out : Exit} {x : Word}
    (hx : fr₁.get c = some x)
    (hsel : (if x = 0 then t₂ else t₁) = tj ∧ (if x = 0 then rs₂ else rs₁) = rsj)
    (h : TermRun fn E (.jump tj rsj) fr₁ m₁ out) : TermRun fn E (.cond c t₁ rs₁ t₂ rs₂) fr₁ m₁ out := by
  obtain ⟨vs, bt, fr', hrd, hbt, hw, hex⟩ := h
  obtain ⟨rfl, rfl⟩ := hsel
  exact ⟨x, vs, bt, fr', hx, hrd, hbt, hw, hex⟩

/-- A conditional terminator of a diamond enters the parameterless block it selects. -/
theorem termRun_cond_block {E : Label → Frame ℕ → Memory → Exit → Prop} {c lblL lblR lbl : ℕ}
    {fr₁ : Frame ℕ} {m₁ : Memory} {out : Exit} {x : Word} {opsA : List (Op ℕ)} {tA : Term ℕ}
    (hx : fr₁.get c = some x) (hsel : (if x = 0 then lblR else lblL) = lbl)
    (hbt : fn.block? lbl = some ⟨[], opsA, tA⟩) (hex : E lbl fr₁ m₁ out) :
    TermRun fn E (.cond c lblL [] lblR []) fr₁ m₁ out := by
  subst hsel
  exact ⟨x, [], _, fr₁, hx, by split <;> rfl, hbt, rfl, hex⟩

theorem regFwd_case_inl (hsigs : CallOracle.MatchesSigs oracle sigs) {env : Semantics.Env Word}
    {d : Tm (Opcode sigs)} {l r : Region (Opcode sigs)} {m m₁ m' : Memory} {va v : Value Word}
    {ℓ : ℕ} (hev : Semantics.Tm.Eval (Opcode.step oracle) env d m (.inl va) m₁)
    (ih : RegFwd oracle fn (extend env va) l m₁ ℓ v m') :
    RegFwd oracle fn env (.case d l r) m ℓ v m' := by
  intro Γ ab Lw ρ L e e' ops t fr out hfit hL hc hinst hag hb K
  cases hfit with
  | case harg hl hr =>
    obtain ⟨c, e₁, htm, hcases⟩ := regionOps_case hc
    obtain ⟨fr₁, x, x₁, hx, hsel, same₁⟩ := regFwd_test hsigs harg htm hag hb hev
    obtain ⟨hx0, rfl⟩ := test_inl hsel
    have bnd := tmRegs_bounds htm
    obtain ⟨hag₁, hb₁⟩ := arm_context hag hb same₁ bnd.1
    rcases hcases with ⟨t₁, rs₁, t₂, rs₂, e₂, hL', hR', rfl⟩ |
        ⟨opsL, tL, e₃, opsR, tR, e₄, hL', hR', rfl, rfl⟩
    · obtain ⟨fr₂, m₂, x₂, term⟩ := ih hl hL hL' (hinst.sub (regionOps_mono hR').2.1) hag₁ hb₁
        (kshift K same₁ bnd.1)
      cases x₂
      exact ⟨fr₁, m₁, x₁, termRun_cond_jump hx ⟨ite_eq_right hx0, ite_eq_right hx0⟩ term⟩
    · have kept := (regionOps_mono hR').2.1
      have hbt := hinst _ (List.mem_cons_of_mem _ (kept List.mem_cons_self))
      have run := ih hl hL hL' (hinst.sub fun p hp => List.mem_cons_of_mem _ (kept
        (List.mem_cons_of_mem _ hp))) hag₁ hb₁ (kshift K same₁ bnd.1)
      exact ⟨fr₁, m₁, x₁, termRun_cond_block hx (ite_eq_right hx0) hbt ((exec_iff_run hbt).2 run)⟩

theorem regFwd_case_inr (hsigs : CallOracle.MatchesSigs oracle sigs) {env : Semantics.Env Word}
    {d : Tm (Opcode sigs)} {l r : Region (Opcode sigs)} {m m₁ m' : Memory} {va v : Value Word}
    {ℓ : ℕ} (hev : Semantics.Tm.Eval (Opcode.step oracle) env d m (.inr va) m₁)
    (ih : RegFwd oracle fn (extend env va) r m₁ ℓ v m') :
    RegFwd oracle fn env (.case d l r) m ℓ v m' := by
  intro Γ ab Lw ρ L e e' ops t fr out hfit hL hc hinst hag hb K
  cases hfit with
  | case harg hl hr =>
    obtain ⟨c, e₁, htm, hcases⟩ := regionOps_case hc
    obtain ⟨fr₁, x, x₁, hx, hsel, same₁⟩ := regFwd_test hsigs harg htm hag hb hev
    obtain ⟨hx0, rfl⟩ := test_inr hsel
    have bnd := tmRegs_bounds htm
    rcases hcases with ⟨t₁, rs₁, t₂, rs₂, e₂, hL', hR', rfl⟩ |
        ⟨opsL, tL, e₃, opsR, tR, e₄, hL', hR', rfl, rfl⟩
    · obtain ⟨hag₁, hb₁⟩ := arm_context hag hb same₁ (bnd.1.trans (regionOps_mono hL').1)
      obtain ⟨fr₂, m₂, x₂, term⟩ :=
        ih hr hL hR' hinst hag₁ hb₁ (kshift K same₁ (bnd.1.trans (regionOps_mono hL').1))
      cases x₂
      exact ⟨fr₁, m₁, x₁, termRun_cond_jump hx ⟨ite_eq_left hx0, ite_eq_left hx0⟩ term⟩
    · obtain ⟨hag₁, hb₁⟩ := arm_context hag hb same₁ (bnd.1.trans (regionOps_mono hL').1)
      have hbt := hinst _ List.mem_cons_self
      have run := ih hr hL hR' (hinst.sub fun p hp => List.mem_cons_of_mem _ hp) hag₁ hb₁
        (kshift K same₁ (bnd.1.trans (regionOps_mono hL').1))
      exact ⟨fr₁, m₁, x₁, termRun_cond_block hx (ite_eq_left hx0) hbt ((exec_iff_run hbt).2 run)⟩

theorem regFwd_cfg {env : Semantics.Env Word} {entry : Region (Opcode sigs)} {k : ℕ}
    {blocks : Fin k → Region (Opcode sigs)} {m m₁ m' : Memory} {first ℓ : ℕ}
    {initial v : Value Word} (ihE : RegFwd oracle fn env entry m first initial m₁)
    (ihF : FolFwd oracle fn env blocks first initial m₁ ℓ v m') :
    RegFwd oracle fn env (.cfg entry k blocks) m ℓ v m' := by
  intro Γ ab Lw ρ L e e' ops t fr out hfit hL hc hinst hag hb K
  cases hfit with
  | @cfg _ _ _ _ _ ws ae abs hws hentry hblocks =>
    obtain ⟨e₁, hE, hfold⟩ := regionOps_cfg hc
    obtain ⟨hinst₁, hcfg⟩ := cfgInst_of_regionOps hE hfold hinst
    have widths : (inner e.nextLabel ws k ++ L).map Prod.snd = ws ++ Lw := by
      rw [List.map_append, inner_widths hws, hL]
    exact ihE hentry widths hE hinst₁ hag hb fun frX vs hs hv hl hlt =>
      ihF hblocks hws hL hcfg hag hb K frX vs hs hv hl hlt

theorem fwdF_exit {env : Semantics.Env Word} {k : ℕ} {blocks : Fin k → Region (Opcode sigs)}
    {first : ℕ} {v : Value Word} {m : Memory} (outside : k ≤ first) :
    FolFwd oracle fn env blocks first v m (first - k) v m := by
  intro Γ ws abs Lw ρ L base n₀ fr₀ out hfits hws hL hcfg hag hb K frX vs hs hv hl hlt
  have long : (inner base ws k).length ≤ first := by simpa using outside
  rw [cont_append long, inner_length]
  refine K frX vs hs hv (fun p hp => hl p ?_) (by simp at hlt; omega)
  rw [List.getElem?_append_right long, inner_length]
  exact hp

theorem fwdF_step {env : Semantics.Env Word} {k : ℕ} {blocks : Fin k → Region (Opcode sigs)}
    {first next ℓ : ℕ} {initial middle v : Value Word} {m m₁ m' : Memory} (inside : first < k)
    (ihH : RegFwd oracle fn (extend env initial) (blocks ⟨first, inside⟩) m next middle m₁)
    (ihT : FolFwd oracle fn env blocks next middle m₁ ℓ v m') :
    FolFwd oracle fn env blocks first initial m ℓ v m' := by
  intro Γ ws abs Lw ρ L base n₀ fr₀ out hfits hws hL hcfg hag hb K frX vs hs hv hl _
  obtain ⟨x, opsB, tB, u', hx, hcomp, hinst, hbt⟩ := hcfg ⟨first, inside⟩
  have hget : (inner base ws k ++ L)[first]? = some (.block (base + first), ws.getD first 0) := by
    rw [List.getElem?_append_left (by simpa using inside)]
    exact inner_getElem? inside
  have hlen : (freshRegs x.nextReg (ws.getD first 0)).length = vs.length := by
    simpa using (hl _ hget).symm
  obtain ⟨fr', hw⟩ := writeAll_isSome frX hlen
  have keep : Same n₀ frX fr' := fun y hy => get_writeAll_of_not_mem hw fun hm => by
    have := (mem_freshRegs.mp hm).1
    omega
  have hold : (Shape.tuple (ws.getD first 0)).Holds initial vs :=
    ⟨hv, hlen.symm.trans (by simp)⟩
  have hag' : Agrees (.tuple (ws.getD first 0) :: Γ) (freshRegs x.nextReg (ws.getD first 0) :: ρ)
      (extend env initial) fr' :=
    (hag.same hb (hs.trans keep)).cons (readAll_writeAll hw (freshRegs_nodup _ _)) hold
  have hb' : Below (.tuple (ws.getD first 0) :: Γ) (freshRegs x.nextReg (ws.getD first 0) :: ρ)
      (x.nextReg + ws.getD first 0) :=
    (hb.mono (by omega)).cons fun y hy => (mem_freshRegs.mp hy).2
  unfold Cont
  rw [hget]
  refine ⟨_, fr', hbt, hw, (exec_iff_run hbt).2 ?_⟩
  exact ihH (hfits ⟨first, inside⟩) (by rw [List.map_append, inner_widths hws, hL]) hcomp hinst
    hag' hb' fun frY vs' hs' hv' hl' hlt' =>
      ihT hfits hws hL hcfg hag hb K frY vs'
        ((hs.trans keep).trans (hs'.mono (Nat.le_trans hx (Nat.le_add_right _ _)))) hv' hl' hlt'

/-- **Forwards.** Every evaluation of a region of the fragment is a run of what
it compiles to. -/
theorem region_forward (hsigs : CallOracle.MatchesSigs oracle sigs) {env : Semantics.Env Word}
    {r : Region (Opcode sigs)} {m m' : Memory} {ℓ : ℕ} {v : Value Word}
    (h : Semantics.Region.Eval (Opcode.step oracle) env r m ℓ v m') :
    RegFwd oracle fn env r m ℓ v m' := by
  induction h using Semantics.Region.Eval.rec
      (motive_2 := fun env _ blocks first initial m ℓ v m' _ =>
        FolFwd oracle fn env blocks first initial m ℓ v m') with
  | br harg => exact regFwd_br hsigs harg
  | let₁ ha _ ih => exact regFwd_let₁ hsigs ha ih
  | let₂ ha _ ih => exact regFwd_let₂ hsigs ha ih
  | case_inl ha _ ih => exact regFwd_case_inl hsigs ha ih
  | case_inr ha _ ih => exact regFwd_case_inr hsigs ha ih
  | cfg _ _ ihE ihF => exact regFwd_cfg ihE ihF
  | exit outside => exact fwdF_exit outside
  | step inside _ _ ihH ihT => exact fwdF_step inside ihH ihT

end Silmaril.Proofs.Machine.OfLambdaSSA
