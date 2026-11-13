module

public import Silmaril.Proofs.Wasm.Models.FunCloDiv.Steps
public import Silmaril.Proofs.Wasm.Models.FunCloDiv.Source

/-!
# Compiled FunClo diverges where the source does: terms

`DivSpec P host p n d e`: if the well-typed term `e` diverges in a typed environment, its code
at depth `d` is safe for `n` steps **in any context** (any values below, any code after, any
postcondition): it neither exits nor gets stuck within `n` steps. `DivApplyAt n`: the same,
at the level of a function specification with postcondition `False`, for `apply` on a closure
whose body diverges.

For every constructor, divergence of the term comes from a part (`Source`): the parts that
return are run with FunCloCompile's total-correctness statement (`spec_all`, through
`safe_after`), and the diverging part with the induction hypothesis. An application whose
function and argument return makes a `call` of `apply` (`Safe.callIdx`), which costs a step, so
`DivApplyAt n` gives `DivSpec (n + 1)` (`div_spec_succ`, by induction on the term).

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCloDiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunCloCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunClo (Tm eval Prog Ty HasTy ValTy EnvTy eval_sound)
open Silmaril.Wasm.Models.FunLang (Arith Cmp)
open Silmaril.Wasm.Models.FunCompile (dBox lx fx boxIdx boxRef unbox getField anyref)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree len_setLocal setLocal_get lt_lim
  vals_pair expr_append depth_left depth_right depth_succ)
open Silmaril.Proofs.Wasm.Models.FunCloCompile (Rep EnvL Ext FOK EnvRep Spec spec_all sub_left
  sub_right Ext.funcs branch)
open Silmaril.Wasm.Logic.Core (Post)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-- Source divergence. -/
abbrev SDiv := Silmaril.Wasm.Models.FunCloDiv.Diverges

/-- **The code of a diverging term runs for `n` steps** in any context. -/
def DivSpec (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (n d : Nat) (e : Tm) :
    Prop :=
  ∀ Γ τ ρ, HasTy Γ e τ → EnvTy ρ Γ → SDiv ρ e → ∀ (s : Store Nat) (f : Frame), FOK f →
    s.funcs[1]? = some (applyInst p) → d + e.depth < f.locals.length →
    EnvRep p.table s f d ρ → (∀ x ∈ e.fixes d, x ∈ p.table) →
    ∀ (us : List Val) (rest : List Admin) (Q : Post Nat),
      Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d e) ++ rest)⟩

/-- The specification of `apply` on a closure whose body diverges: it never returns. -/
def divApplySpec (p : Prog) (b : Tm) (ρ' : List FunClo.Val) (u : FunClo.Val) : FSpec Nat :=
  ⟨fun s args => s.funcs[1]? = some (applyInst p) ∧
      ∃ wc wu, args = [wc, wu] ∧ Rep p.table s (.clo b ρ') wc ∧ Rep p.table s u wu,
    fun _ _ _ _ => False⟩

/-- `apply` runs for `n` steps on every well-typed closure whose body diverges. -/
def DivApplyAt (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (n : Nat) : Prop :=
  ∀ b ρ' u Γ τ, EnvTy (u :: .clo b ρ' :: ρ') Γ → HasTy Γ b τ → SDiv (u :: .clo b ρ' :: ρ') b →
    FSpecAt P host n 1 (divApplySpec p b ρ' u)

theorem divSpec_zero (d : Nat) (e : Tm) : DivSpec P host p 0 d e := by
  unfold DivSpec; intros; exact trivial

theorem divApplyAt_zero : DivApplyAt P host p 0 := by
  unfold DivApplyAt FSpecAt; intros; exact trivial

/-! ## A terminating part, then a diverging one -/

/-- The code of a term that returns, followed by a continuation safe for `n` steps. -/
theorem safe_after (hfit : p.Fits) {k d : Nat} {e : Tm} {ρ : List FunClo.Val} {v : FunClo.Val}
    (hv : eval k ρ e = some v) {s : Store Nat} {f : Frame} (hf : FOK f)
    (hfn : s.funcs[1]? = some (applyInst p)) (hd : d + e.depth < f.locals.length)
    (hr : EnvRep p.table s f d ρ) (hfx : ∀ x ∈ e.fixes d, x ∈ p.table) {n : Nat}
    {us : List Val} {rest : List Admin} {Q : Post Nat}
    (hk : ∀ s' f' w, Ext s s' → Agree d f f' → Rep p.table s' v w →
      Safe P host Q n ⟨s', f', vals (us ++ [w]) ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d e) ++ rest)⟩ := by
  have ht : TWP P host s f (vals us ++ (expression (compile p.table d e) ++ []))
      (thenSafe P host Q n rest) :=
    spec_all hfit k d e ρ v hv s f hf hfn hd hr hfx us [] _
      fun s' f' w hs ha hw => twp_thenSafe' (hk s' f' w hs ha hw)
  have h' := safe_of_twp ht
  simpa using h'

/-! ## Leaves -/

theorem div_spec_var (n d i : Nat) : DivSpec P host p n d (.var i) := by
  intro Γ τ ρ ht hρ hdv
  have hi : Γ[i]? = some τ := by cases ht; assumption
  exact absurd hdv (not_div_var hρ hi)

theorem div_spec_int (n d : Nat) (x : BitVec 31) : DivSpec P host p n d (.int x) :=
  fun _ _ _ _ _ hdv => absurd hdv (not_div_eval (k := 1) rfl)

theorem div_spec_bool (n d : Nat) (b : Bool) : DivSpec P host p n d (.bool b) :=
  fun _ _ _ _ _ hdv => absurd hdv (not_div_eval (k := 1) rfl)

theorem div_spec_fix (n d : Nat) (b : Tm) : DivSpec P host p n d (.fix b) :=
  fun _ _ _ _ _ hdv => absurd hdv (not_div_eval (k := 1) rfl)

/-! ## Arithmetic and comparisons -/

/-- After an integer operand, the second operand diverges. -/
theorem safe_secondInt (hfit : p.Fits) {n d : Nat} {a b : Tm} {k : Nat} {Γ : List Ty}
    {ρ : List FunClo.Val} {x : BitVec 31} (hxa : eval k ρ a = some (.int x))
    (ihb : DivSpec P host p n d b) (hb : HasTy Γ b .int) (hρ : EnvTy ρ Γ) (hdb : SDiv ρ b)
    {s : Store Nat} {f : Frame} (hf : FOK f) (hfn : s.funcs[1]? = some (applyInst p))
    (hd : d + max a.depth b.depth < f.locals.length) (hr : EnvRep p.table s f d ρ)
    (hfx : ∀ x ∈ a.fixes d ++ b.fixes d, x ∈ p.table) (us : List Val) (rest : List Admin)
    (Q : Post Nat) :
    Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d a) ++ (expression unbox ++
      (expression (compile p.table d b) ++ rest)))⟩ := by
  refine safe_after hfit hxa hf hfn (depth_left hd) hr (sub_left hfx)
    fun s₁ f₁ w hs₁ hf₁ hw => ?_
  have hw' : w = .ref (.i31 x) := hw
  have hdb' : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  rw [hw']
  exact safe_unbox (ihb Γ .int ρ hb hρ hdb s₁ f₁ (hf.of_agree hf₁) (hs₁.funcs hfn) hdb'
    (hr.of_agree hs₁.1 hf₁) (sub_right hfx) _ _ Q)

theorem div_spec_arith (hfit : p.Fits) {n d : Nat} {op : Arith} {a b : Tm}
    (iha : DivSpec P host p n d a) (ihb : DivSpec P host p n d b) :
    DivSpec P host p n d (.arith op a b) := by
  intro Γ τ ρ ht hρ hdv s f hf hfn hd hr hfx us rest Q
  have hab : HasTy Γ a .int ∧ HasTy Γ b .int := by cases ht; exact ⟨‹_›, ‹_›⟩
  show Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d a ++ unbox ++
    compile p.table d b ++ unbox ++ [.intBinOp .i32 (FunCompile.Arith.wasm op), .refI31]) ++
    rest)⟩
  simp only [List.append_assoc, expr_append]
  rcases div_arith hρ hab.1 hab.2 hdv with hda | ⟨k, x, hxa, hdb⟩
  · exact iha Γ .int ρ hab.1 hρ hda s f hf hfn (depth_left hd) hr (sub_left hfx) us _ Q
  · exact safe_secondInt hfit hxa ihb hab.2 hρ hdb hf hfn hd hr hfx us _ Q

theorem div_spec_cmp (hfit : p.Fits) {n d : Nat} {op : Cmp} {a b : Tm}
    (iha : DivSpec P host p n d a) (ihb : DivSpec P host p n d b) :
    DivSpec P host p n d (.cmp op a b) := by
  intro Γ τ ρ ht hρ hdv s f hf hfn hd hr hfx us rest Q
  have hab : HasTy Γ a .int ∧ HasTy Γ b .int := by cases ht; exact ⟨‹_›, ‹_›⟩
  show Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d a ++ unbox ++
    compile p.table d b ++ unbox ++ [.intRelOp .i32 (FunCompile.Cmp.wasm op), .refI31]) ++
    rest)⟩
  simp only [List.append_assoc, expr_append]
  rcases div_cmp hρ hab.1 hab.2 hdv with hda | ⟨k, x, hxa, hdb⟩
  · exact iha Γ .int ρ hab.1 hρ hda s f hf hfn (depth_left hd) hr (sub_left hfx) us _ Q
  · exact safe_secondInt hfit hxa ihb hab.2 hρ hdb hf hfn hd hr hfx us _ Q

/-! ## Conditionals -/

/-- A diverging term inside a block of result `anyref`. -/
theorem safe_inBlock {n d : Nat} {e : Tm} (ih : DivSpec P host p n d e) {Γ : List Ty} {τ : Ty}
    {ρ : List FunClo.Val} (ht : HasTy Γ e τ) (hρ : EnvTy ρ Γ) (hdv : SDiv ρ e)
    {s : Store Nat} {f : Frame} (hf : FOK f) (hfn : s.funcs[1]? = some (applyInst p))
    (hd : d + e.depth < f.locals.length) (hr : EnvRep p.table s f d ρ)
    (hfx : ∀ x ∈ e.fixes d, x ∈ p.table) (Q : Post Nat) :
    Safe P host Q n ⟨s, f, vals [] ++ expression (compile p.table d e)⟩ := by
  have h' := ih Γ τ ρ ht hρ hdv s f hf hfn hd hr hfx [] [] Q
  simpa using h'

/-- The selected branch of an `ite` diverges. -/
theorem safe_iteBranch {n d : Nat} {t e : Tm} {b : Bool} (iht : DivSpec P host p n d t)
    (ihe : DivSpec P host p n d e) {Γ : List Ty} {τ : Ty} {ρ : List FunClo.Val}
    (htt : HasTy Γ t τ) (hte : HasTy Γ e τ) (hρ : EnvTy ρ Γ) (hdb : SDiv ρ (if b then t else e))
    {s : Store Nat} {f : Frame} (hf : FOK f) (hfn : s.funcs[1]? = some (applyInst p))
    (hd : d + max t.depth e.depth < f.locals.length) (hr : EnvRep p.table s f d ρ)
    (hfx : ∀ x ∈ t.fixes d ++ e.fixes d, x ∈ p.table) (Q : Post Nat) :
    Safe P host Q n ⟨s, f, vals [] ++ expression
      (if (if b then (1 : BitVec 31) else 0).setWidth 32 ≠ 0 then compile p.table d t
        else compile p.table d e)⟩ := by
  cases b
  · exact safe_inBlock ihe hte hρ hdb hf hfn (depth_right hd) hr (sub_right hfx) Q
  · exact safe_inBlock iht htt hρ hdb hf hfn (depth_left hd) hr (sub_left hfx) Q

theorem div_spec_ite (hfit : p.Fits) {n d : Nat} {c t e : Tm} (ihc : DivSpec P host p n d c)
    (iht : DivSpec P host p n d t) (ihe : DivSpec P host p n d e) :
    DivSpec P host p n d (.ite c t e) := by
  intro Γ τ ρ ht hρ hdv s f hf hfn hd hr hfx us rest Q
  have hty : HasTy Γ c .bool ∧ HasTy Γ t τ ∧ HasTy Γ e τ := by
    cases ht; exact ⟨‹_›, ‹_›, ‹_›⟩
  have hfx' : ∀ x ∈ c.fixes d ++ (t.fixes d ++ e.fixes d), x ∈ p.table := by
    simpa only [Tm.fixes, List.append_assoc] using hfx
  show Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d c ++ unbox ++
    [.if_ (.value anyref) (compile p.table d t) (compile p.table d e)]) ++ rest)⟩
  simp only [List.append_assoc, expr_append]
  rcases div_ite hρ hty.1 hdv with hdc | ⟨k, b, hcb, hdb⟩
  · exact ihc Γ .bool ρ hty.1 hρ hdc s f hf hfn (depth_left hd) hr (sub_left hfx') us _ Q
  · refine safe_after hfit hcb hf hfn (depth_left hd) hr (sub_left hfx')
      fun s₁ f₁ w hs₁ hf₁ hw => ?_
    have hw' : w = .ref (.i31 (if b then 1 else 0)) := hw
    have hd₁ : d + max t.depth e.depth < f₁.locals.length := by
      rw [hf₁.2.1]; exact depth_right hd
    rw [hw']
    exact safe_unbox (safe_ifBlock (safe_iteBranch iht ihe hty.2.1 hty.2.2 hρ hdb
      (hf.of_agree hf₁) (hs₁.funcs hfn) hd₁ (hr.of_agree hs₁.1 hf₁) (sub_right hfx') _))

/-! ## Binders -/

theorem div_spec_let (hfit : p.Fits) {n d : Nat} {a b : Tm} (iha : DivSpec P host p n d a)
    (ihb : DivSpec P host p n (d + 1) b) : DivSpec P host p n d (.let_ a b) := by
  intro Γ τ ρ ht hρ hdv s f hf hfn hd hr hfx us rest Q
  obtain ⟨σ, ha, hb⟩ : ∃ σ, HasTy Γ a σ ∧ HasTy (σ :: Γ) b τ := by
    cases ht; exact ⟨_, ‹_›, ‹_›⟩
  have hfx' : ∀ x ∈ a.fixes d ++ b.fixes (d + 1), x ∈ p.table := hfx
  have hdb : d + 1 + b.depth < f.locals.length := depth_succ (depth_right hd)
  have hlt : d + 1 < f.locals.length := by omega
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.1 hlt
  show Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d a ++
    .localSet (lx (d + 1)) :: compile p.table (d + 1) b) ++ rest)⟩
  rw [expr_append]
  rcases div_let hdv with hda | ⟨k, u, hu, hdu⟩
  · exact iha Γ σ ρ ha hρ hda s f hf hfn (depth_left hd) hr (sub_left hfx') us _ Q
  · refine safe_after hfit hu hf hfn (depth_left hd) hr (sub_left hfx')
      fun s₁ f₁ w hs₁ hf₁ hw => ?_
    have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
    have hρ' : EnvTy (u :: ρ) (σ :: Γ) := .cons (eval_sound k ha hρ hu) hρ
    refine safe_localSet (hf.of_agree hf₁).1 hlt₁ ?_
    exact ihb (σ :: Γ) τ (u :: ρ) hb hρ' hdu s₁ _ ((hf.of_agree hf₁).setLocal _ w)
      (hs₁.funcs hfn) (by rw [len_setLocal, hf₁.2.1]; exact hdb)
      ((hr.of_agree hs₁.1 hf₁).cons hw hlt₁ hlim) (sub_right hfx') us rest Q

/-! ## Pairs, projections and injections -/

theorem div_spec_pair (hfit : p.Fits) {n d : Nat} {a b : Tm} (iha : DivSpec P host p n d a)
    (ihb : DivSpec P host p n d b) : DivSpec P host p n d (.pair a b) := by
  intro Γ τ ρ ht hρ hdv s f hf hfn hd hr hfx us rest Q
  obtain ⟨σ₁, σ₂, ha, hb⟩ : ∃ σ₁ σ₂, HasTy Γ a σ₁ ∧ HasTy Γ b σ₂ := by
    cases ht; exact ⟨_, _, ‹_›, ‹_›⟩
  show Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d a ++
    compile p.table d b ++ [.structNew boxIdx]) ++ rest)⟩
  simp only [List.append_assoc, expr_append]
  rcases div_pair hdv with hda | ⟨k, x, hxa, hdb⟩
  · exact iha Γ σ₁ ρ ha hρ hda s f hf hfn (depth_left hd) hr (sub_left hfx) us _ Q
  · refine safe_after hfit hxa hf hfn (depth_left hd) hr (sub_left hfx)
      fun s₁ f₁ w hs₁ hf₁ hw => ?_
    have hdb' : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
    exact ihb Γ σ₂ ρ hb hρ hdb s₁ f₁ (hf.of_agree hf₁) (hs₁.funcs hfn) hdb'
      (hr.of_agree hs₁.1 hf₁) (sub_right hfx) _ _ Q

/-- A diverging subterm followed by any code. -/
theorem div_spec_prefix {n d : Nat} {e e' : Tm} {c : List Instr} (ih : DivSpec P host p n d e)
    (hcode : compile p.table d e' = compile p.table d e ++ c) (hdepth : e'.depth = e.depth)
    (hfixes : e'.fixes d = e.fixes d)
    (hdiv : ∀ Γ τ ρ, HasTy Γ e' τ → EnvTy ρ Γ → SDiv ρ e' →
      ∃ σ, HasTy Γ e σ ∧ SDiv ρ e) : DivSpec P host p n d e' := by
  intro Γ τ ρ ht hρ hdv s f hf hfn hd hr hfx us rest Q
  obtain ⟨σ, he, hde⟩ := hdiv Γ τ ρ ht hρ hdv
  have h' := ih Γ σ ρ he hρ hde s f hf hfn (hdepth ▸ hd) hr (hfixes ▸ hfx) us
    (expression c ++ rest) Q
  rw [hcode, expr_append]
  exact h'

theorem div_spec_fst {n d : Nat} {e : Tm} (ih : DivSpec P host p n d e) :
    DivSpec P host p n d (.fst e) :=
  div_spec_prefix ih rfl rfl rfl fun Γ τ ρ ht hρ hdv => by
    cases ht with
    | fst he => exact ⟨_, he, div_fst hρ he hdv⟩

theorem div_spec_snd {n d : Nat} {e : Tm} (ih : DivSpec P host p n d e) :
    DivSpec P host p n d (.snd e) :=
  div_spec_prefix ih rfl rfl rfl fun Γ τ ρ ht hρ hdv => by
    cases ht with
    | snd he => exact ⟨_, he, div_snd hρ he hdv⟩

/-- An injection with tag `k` whose payload diverges. -/
theorem div_spec_injTag {n d : Nat} {e e' : Tm} {k : BitVec 32} (ih : DivSpec P host p n d e)
    (hcode : compile p.table d e' = .intConst .i32 k :: .refI31 :: compile p.table d e ++
      [.structNew boxIdx]) (hdepth : e'.depth = e.depth) (hfixes : e'.fixes d = e.fixes d)
    (hdiv : ∀ Γ τ ρ, HasTy Γ e' τ → EnvTy ρ Γ → SDiv ρ e' → ∃ σ, HasTy Γ e σ ∧ SDiv ρ e) :
    DivSpec P host p n d e' := by
  intro Γ τ ρ ht hρ hdv s f hf hfn hd hr hfx us rest Q
  obtain ⟨σ, he, hde⟩ := hdiv Γ τ ρ ht hρ hdv
  have hc : vals us ++ (expression (compile p.table d e') ++ rest) = vals us ++
      (expression [.intConst .i32 k, .refI31] ++ (expression (compile p.table d e) ++
        (expression [.structNew boxIdx] ++ rest))) := by
    rw [hcode]; simp [expression]
  rw [hc]
  exact safe_constBox (ih Γ σ ρ he hρ hde s f hf hfn (hdepth ▸ hd) hr (hfixes ▸ hfx) _ _ Q)

theorem div_spec_inl {n d : Nat} {e : Tm} (ih : DivSpec P host p n d e) :
    DivSpec P host p n d (.inl e) :=
  div_spec_injTag ih rfl rfl rfl fun Γ τ ρ ht _ hdv => by
    cases ht with
    | inl _ he => exact ⟨_, he, div_inl hdv⟩

theorem div_spec_inr {n d : Nat} {e : Tm} (ih : DivSpec P host p n d e) :
    DivSpec P host p n d (.inr e) :=
  div_spec_injTag ih rfl rfl rfl fun Γ τ ρ ht _ hdv => by
    cases ht with
    | inr _ he => exact ⟨_, he, div_inr hdv⟩

end Silmaril.Proofs.Wasm.Models.FunCloDiv
