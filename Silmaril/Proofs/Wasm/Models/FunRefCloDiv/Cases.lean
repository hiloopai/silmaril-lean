module

public import Silmaril.Proofs.Wasm.Models.FunRefCloDiv.Source
public import Silmaril.Wasm.Models.FunRefCloCompile.Thms
public import Silmaril.Wasm.Models.FunCloDiv.Thms

/-!
# Compiled FunRefClo diverges where the source does: terms

As `Silmaril.Proofs.Wasm.Models.FunCloDiv.Cases`, with the heap. `DivSpec P host p n d e`: if the
well-typed term `e` diverges from a heap `σ` in an environment `ρ`, both typed (`Typed`), its
code at depth `d` is safe for `n` steps **in any context** (any values below, any code after,
any postcondition), in every store whose cells represent `σ` (`HeapRep`) and every frame whose
locals represent `ρ`. `DivApplyAt n`: the same for `apply` on a closure whose body diverges,
as a function specification with postcondition `False`.

For every constructor, divergence of the term comes from a part (`Source`): the parts that
return are run with FunRefCloCompile's total-correctness statement (`spec_all`, through
`safe_after`, which hands the continuation the cells of the heap they return in), and the
diverging part with the induction hypothesis. The generic step-indexed lemmas
(`safe_of_twp`, `safe_unbox`, `safe_ifBlock`, …) are FunCloDiv's.

This file: the leaves, arithmetic, comparisons, conditionals, `let`, pairs, projections,
injections and the cells (`ref`, `get`, `set`).

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunRefCloDiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunRefCloCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunRefClo (Tm eval Prog Ty Heap HasTy)
open Silmaril.Wasm.Models.FunLang (Arith Cmp)
open Silmaril.Wasm.Models.FunCompile (dBox lx fx boxIdx boxRef unbox getField anyref)
open Silmaril.Wasm.Models.FunRefCompile (cellIdx cellRef dCell)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree len_setLocal setLocal_get lt_lim
  vals_pair expr_append depth_left depth_right depth_succ)
open Silmaril.Proofs.Wasm.Models.FunRefCloCompile (Rep EnvL Ext FOK EnvRep HeapRep spec_all
  sub_left sub_right twp_castCell)
open Silmaril.Proofs.Wasm.Models.FunCloDiv (thenSafe safe_of_twp twp_thenSafe' safe_bridge
  safe_localSet safe_unbox safe_constBox safe_ifBlock)
open Silmaril.Wasm.Logic.Core (Post)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-- Source divergence. -/
abbrev SDiv := Silmaril.Wasm.Models.FunRefCloDiv.Diverges

/-- **The code of a diverging term runs for `n` steps** in any context. -/
def DivSpec (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (n d : Nat) (e : Tm) :
    Prop :=
  ∀ Γ τ σ ρ, HasTy Γ e τ → Typed Γ σ ρ → SDiv σ ρ e →
    ∀ (μ : List Nat) (s : Store Nat) (f : Frame), FOK f →
    s.funcs[1]? = some (applyInst p) → d + e.depth < f.locals.length →
    EnvRep p.table μ s f d ρ → HeapRep p.table μ s σ → (∀ x ∈ e.fixes d, x ∈ p.table) →
    ∀ (us : List Val) (rest : List Admin) (Q : Post Nat),
      Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d e) ++ rest)⟩

/-- The specification of `apply` on a closure whose body diverges from the heap `σ` (cells
`μ`): it never returns. -/
def divApplySpec (p : Prog) (b : Tm) (ρ' : List FunRefClo.Val) (u : FunRefClo.Val) (σ : Heap)
    (μ : List Nat) : FSpec Nat :=
  ⟨fun s args => s.funcs[1]? = some (applyInst p) ∧ HeapRep p.table μ s σ ∧
      ∃ wc wu, args = [wc, wu] ∧ Rep p.table μ s (.clo b ρ') wc ∧ Rep p.table μ s u wu,
    fun _ _ _ _ => False⟩

/-- `apply` runs for `n` steps on every well-typed closure whose body diverges. -/
def DivApplyAt (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (n : Nat) : Prop :=
  ∀ b ρ' u σ μ Γ τ, Typed Γ σ (u :: .clo b ρ' :: ρ') → HasTy Γ b τ →
    SDiv σ (u :: .clo b ρ' :: ρ') b → FSpecAt P host n 1 (divApplySpec p b ρ' u σ μ)

theorem divSpec_zero (d : Nat) (e : Tm) : DivSpec P host p 0 d e := by
  unfold DivSpec; intros; exact trivial

theorem divApplyAt_zero : DivApplyAt P host p 0 := by
  unfold DivApplyAt FSpecAt; intros; exact trivial

/-! ## A terminating part, then a diverging one -/

/-- The code of a term that returns, followed by a continuation safe for `n` steps in the
cells of the heap it returns in. -/
theorem safe_after (hfit : p.Fits) {k d : Nat} {e : Tm} {σ σ' : Heap} {ρ : List FunRefClo.Val}
    {v : FunRefClo.Val} (hv : eval k σ ρ e = some (v, σ')) {μ : List Nat} {s : Store Nat}
    {f : Frame} (hf : FOK f) (hfn : s.funcs[1]? = some (applyInst p))
    (hd : d + e.depth < f.locals.length) (hr : EnvRep p.table μ s f d ρ)
    (hh : HeapRep p.table μ s σ) (hfx : ∀ x ∈ e.fixes d, x ∈ p.table) {n : Nat}
    {us : List Val} {rest : List Admin} {Q : Post Nat}
    (hk : ∀ μ' s' f' w, μ <+: μ' → Ext s s' → Agree d f f' → HeapRep p.table μ' s' σ' →
      Rep p.table μ' s' v w → Safe P host Q n ⟨s', f', vals (us ++ [w]) ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d e) ++ rest)⟩ := by
  have ht : TWP P host s f (vals us ++ (expression (compile p.table d e) ++ []))
      (thenSafe P host Q n rest) :=
    spec_all hfit k d e σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us [] _
      fun μ' s' f' w hμ hs ha hh' hw => twp_thenSafe' (hk μ' s' f' w hμ hs ha hh' hw)
  have h' := safe_of_twp ht
  simpa using h'

/-! ## Leaves -/

theorem div_spec_var (n d i : Nat) : DivSpec P host p n d (.var i) := by
  intro Γ τ σ ρ ht hT hdv
  have hi : Γ[i]? = some τ := by cases ht; assumption
  exact absurd hdv (not_div_var hT hi)

theorem div_spec_int (n d : Nat) (x : BitVec 31) : DivSpec P host p n d (.int x) :=
  fun _ _ _ _ _ _ hdv => absurd hdv (not_div_eval (k := 1) rfl)

theorem div_spec_bool (n d : Nat) (b : Bool) : DivSpec P host p n d (.bool b) :=
  fun _ _ _ _ _ _ hdv => absurd hdv (not_div_eval (k := 1) rfl)

theorem div_spec_fix (n d : Nat) (b : Tm) : DivSpec P host p n d (.fix b) :=
  fun _ _ _ _ _ _ hdv => absurd hdv (not_div_eval (k := 1) rfl)

/-! ## Arithmetic and comparisons -/

/-- After an integer operand, the second operand diverges. -/
theorem safe_secondInt (hfit : p.Fits) {n d : Nat} {a b : Tm} {k : Nat} {Γ : List Ty}
    {σ σ₁ : Heap} {ρ : List FunRefClo.Val} {x : BitVec 31}
    (hxa : eval k σ ρ a = some (.int x, σ₁)) (ihb : DivSpec P host p n d b)
    (hb : HasTy Γ b .int) (hT₁ : Typed Γ σ₁ ρ) (hdb : SDiv σ₁ ρ b) {μ : List Nat}
    {s : Store Nat} {f : Frame} (hf : FOK f) (hfn : s.funcs[1]? = some (applyInst p))
    (hd : d + max a.depth b.depth < f.locals.length) (hr : EnvRep p.table μ s f d ρ)
    (hh : HeapRep p.table μ s σ) (hfx : ∀ x ∈ a.fixes d ++ b.fixes d, x ∈ p.table)
    (us : List Val) (rest : List Admin) (Q : Post Nat) :
    Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d a) ++ (expression unbox ++
      (expression (compile p.table d b) ++ rest)))⟩ := by
  refine safe_after hfit hxa hf hfn (depth_left hd) hr hh (sub_left hfx)
    fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  have hw' : w = .ref (.i31 x) := hw
  have hdb' : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  rw [hw']
  exact safe_unbox (ihb Γ .int σ₁ ρ hb hT₁ hdb μ₁ s₁ f₁ (hf.of_agree hf₁) (hs₁.funcs hfn) hdb'
    (hr.of_agree hμ₁ hs₁.1 hf₁) hh₁ (sub_right hfx) _ _ Q)

theorem div_spec_arith (hfit : p.Fits) {n d : Nat} {op : Arith} {a b : Tm}
    (iha : DivSpec P host p n d a) (ihb : DivSpec P host p n d b) :
    DivSpec P host p n d (.arith op a b) := by
  intro Γ τ σ ρ ht hT hdv μ s f hf hfn hd hr hh hfx us rest Q
  have hab : HasTy Γ a .int ∧ HasTy Γ b .int := by cases ht; exact ⟨‹_›, ‹_›⟩
  show Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d a ++ unbox ++
    compile p.table d b ++ unbox ++ [.intBinOp .i32 (FunCompile.Arith.wasm op), .refI31]) ++
    rest)⟩
  simp only [List.append_assoc, expr_append]
  rcases div_arith hT hab.1 hab.2 hdv with hda | ⟨k, x, σ₁, hxa, hT₁, hdb⟩
  · exact iha Γ .int σ ρ hab.1 hT hda μ s f hf hfn (depth_left hd) hr hh (sub_left hfx) us _ Q
  · exact safe_secondInt hfit hxa ihb hab.2 hT₁ hdb hf hfn hd hr hh hfx us _ Q

theorem div_spec_cmp (hfit : p.Fits) {n d : Nat} {op : Cmp} {a b : Tm}
    (iha : DivSpec P host p n d a) (ihb : DivSpec P host p n d b) :
    DivSpec P host p n d (.cmp op a b) := by
  intro Γ τ σ ρ ht hT hdv μ s f hf hfn hd hr hh hfx us rest Q
  have hab : HasTy Γ a .int ∧ HasTy Γ b .int := by cases ht; exact ⟨‹_›, ‹_›⟩
  show Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d a ++ unbox ++
    compile p.table d b ++ unbox ++ [.intRelOp .i32 (FunCompile.Cmp.wasm op), .refI31]) ++
    rest)⟩
  simp only [List.append_assoc, expr_append]
  rcases div_cmp hT hab.1 hab.2 hdv with hda | ⟨k, x, σ₁, hxa, hT₁, hdb⟩
  · exact iha Γ .int σ ρ hab.1 hT hda μ s f hf hfn (depth_left hd) hr hh (sub_left hfx) us _ Q
  · exact safe_secondInt hfit hxa ihb hab.2 hT₁ hdb hf hfn hd hr hh hfx us _ Q

/-! ## Conditionals -/

/-- A diverging term inside a block of result `anyref`. -/
theorem safe_inBlock {n d : Nat} {e : Tm} (ih : DivSpec P host p n d e) {Γ : List Ty} {τ : Ty}
    {σ : Heap} {ρ : List FunRefClo.Val} (ht : HasTy Γ e τ) (hT : Typed Γ σ ρ)
    (hdv : SDiv σ ρ e) {μ : List Nat} {s : Store Nat} {f : Frame} (hf : FOK f)
    (hfn : s.funcs[1]? = some (applyInst p)) (hd : d + e.depth < f.locals.length)
    (hr : EnvRep p.table μ s f d ρ) (hh : HeapRep p.table μ s σ)
    (hfx : ∀ x ∈ e.fixes d, x ∈ p.table) (Q : Post Nat) :
    Safe P host Q n ⟨s, f, vals [] ++ expression (compile p.table d e)⟩ := by
  have h' := ih Γ τ σ ρ ht hT hdv μ s f hf hfn hd hr hh hfx [] [] Q
  simpa using h'

/-- The selected branch of an `ite` diverges. -/
theorem safe_iteBranch {n d : Nat} {t e : Tm} {b : Bool} (iht : DivSpec P host p n d t)
    (ihe : DivSpec P host p n d e) {Γ : List Ty} {τ : Ty} {σ : Heap} {ρ : List FunRefClo.Val}
    (htt : HasTy Γ t τ) (hte : HasTy Γ e τ) (hT : Typed Γ σ ρ)
    (hdb : SDiv σ ρ (if b then t else e)) {μ : List Nat} {s : Store Nat} {f : Frame}
    (hf : FOK f) (hfn : s.funcs[1]? = some (applyInst p))
    (hd : d + max t.depth e.depth < f.locals.length) (hr : EnvRep p.table μ s f d ρ)
    (hh : HeapRep p.table μ s σ) (hfx : ∀ x ∈ t.fixes d ++ e.fixes d, x ∈ p.table)
    (Q : Post Nat) :
    Safe P host Q n ⟨s, f, vals [] ++ expression
      (if (if b then (1 : BitVec 31) else 0).setWidth 32 ≠ 0 then compile p.table d t
        else compile p.table d e)⟩ := by
  cases b
  · exact safe_inBlock ihe hte hT hdb hf hfn (depth_right hd) hr hh (sub_right hfx) Q
  · exact safe_inBlock iht htt hT hdb hf hfn (depth_left hd) hr hh (sub_left hfx) Q

theorem div_spec_ite (hfit : p.Fits) {n d : Nat} {c t e : Tm} (ihc : DivSpec P host p n d c)
    (iht : DivSpec P host p n d t) (ihe : DivSpec P host p n d e) :
    DivSpec P host p n d (.ite c t e) := by
  intro Γ τ σ ρ ht hT hdv μ s f hf hfn hd hr hh hfx us rest Q
  have hty : HasTy Γ c .bool ∧ HasTy Γ t τ ∧ HasTy Γ e τ := by
    cases ht; exact ⟨‹_›, ‹_›, ‹_›⟩
  have hfx' : ∀ x ∈ c.fixes d ++ (t.fixes d ++ e.fixes d), x ∈ p.table := by
    simpa only [FunRefClo.Tm.fixes, List.append_assoc] using hfx
  show Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d c ++ unbox ++
    [.if_ (.value anyref) (compile p.table d t) (compile p.table d e)]) ++ rest)⟩
  simp only [List.append_assoc, expr_append]
  rcases div_ite hT hty.1 hdv with hdc | ⟨k, b, σ₁, hcb, hT₁, hdb⟩
  · exact ihc Γ .bool σ ρ hty.1 hT hdc μ s f hf hfn (depth_left hd) hr hh (sub_left hfx') us _ Q
  · refine safe_after hfit hcb hf hfn (depth_left hd) hr hh (sub_left hfx')
      fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
    have hw' : w = .ref (.i31 (if b then 1 else 0)) := hw
    have hd₁ : d + max t.depth e.depth < f₁.locals.length := by
      rw [hf₁.2.1]; exact depth_right hd
    rw [hw']
    exact safe_unbox (safe_ifBlock (safe_iteBranch iht ihe hty.2.1 hty.2.2 hT₁ hdb
      (hf.of_agree hf₁) (hs₁.funcs hfn) hd₁ (hr.of_agree hμ₁ hs₁.1 hf₁) hh₁ (sub_right hfx') _))

/-! ## Binders -/

theorem div_spec_let (hfit : p.Fits) {n d : Nat} {a b : Tm} (iha : DivSpec P host p n d a)
    (ihb : DivSpec P host p n (d + 1) b) : DivSpec P host p n d (.let_ a b) := by
  intro Γ τ σ ρ ht hT hdv μ s f hf hfn hd hr hh hfx us rest Q
  obtain ⟨σa, ha, hb⟩ : ∃ σa, HasTy Γ a σa ∧ HasTy (σa :: Γ) b τ := by
    cases ht; exact ⟨_, ‹_›, ‹_›⟩
  have hfx' : ∀ x ∈ a.fixes d ++ b.fixes (d + 1), x ∈ p.table := hfx
  have hdb : d + 1 + b.depth < f.locals.length := depth_succ (depth_right hd)
  have hlt : d + 1 < f.locals.length := by omega
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.1 hlt
  show Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d a ++
    .localSet (lx (d + 1)) :: compile p.table (d + 1) b) ++ rest)⟩
  rw [expr_append]
  rcases div_let hT ha hdv with hda | ⟨k, u, σ₁, hu, hT₁, hdu⟩
  · exact iha Γ σa σ ρ ha hT hda μ s f hf hfn (depth_left hd) hr hh (sub_left hfx') us _ Q
  · refine safe_after hfit hu hf hfn (depth_left hd) hr hh (sub_left hfx')
      fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
    have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
    refine safe_localSet (hf.of_agree hf₁).1 hlt₁ ?_
    exact ihb (σa :: Γ) τ σ₁ (u :: ρ) hb hT₁ hdu μ₁ s₁ _ ((hf.of_agree hf₁).setLocal _ w)
      (hs₁.funcs hfn) (by rw [len_setLocal, hf₁.2.1]; exact hdb)
      ((hr.of_agree hμ₁ hs₁.1 hf₁).cons hw hlt₁ hlim) hh₁ (sub_right hfx') us rest Q

/-! ## Pairs, projections and injections -/

theorem div_spec_pair (hfit : p.Fits) {n d : Nat} {a b : Tm} (iha : DivSpec P host p n d a)
    (ihb : DivSpec P host p n d b) : DivSpec P host p n d (.pair a b) := by
  intro Γ τ σ ρ ht hT hdv μ s f hf hfn hd hr hh hfx us rest Q
  obtain ⟨σ₁', σ₂', ha, hb⟩ : ∃ σ₁' σ₂', HasTy Γ a σ₁' ∧ HasTy Γ b σ₂' := by
    cases ht; exact ⟨_, _, ‹_›, ‹_›⟩
  show Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d a ++
    compile p.table d b ++ [.structNew boxIdx]) ++ rest)⟩
  simp only [List.append_assoc, expr_append]
  rcases div_pair hT ha hdv with hda | ⟨k, x, σ₁, hxa, hT₁, hdb⟩
  · exact iha Γ σ₁' σ ρ ha hT hda μ s f hf hfn (depth_left hd) hr hh (sub_left hfx) us _ Q
  · refine safe_after hfit hxa hf hfn (depth_left hd) hr hh (sub_left hfx)
      fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
    have hdb' : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
    exact ihb Γ σ₂' σ₁ ρ hb hT₁ hdb μ₁ s₁ f₁ (hf.of_agree hf₁) (hs₁.funcs hfn) hdb'
      (hr.of_agree hμ₁ hs₁.1 hf₁) hh₁ (sub_right hfx) _ _ Q

/-- A diverging subterm followed by any code. -/
theorem div_spec_prefix {n d : Nat} {e e' : Tm} {c : List Instr} (ih : DivSpec P host p n d e)
    (hcode : compile p.table d e' = compile p.table d e ++ c) (hdepth : e'.depth = e.depth)
    (hfixes : e'.fixes d = e.fixes d)
    (hdiv : ∀ Γ τ σ ρ, HasTy Γ e' τ → Typed Γ σ ρ → SDiv σ ρ e' →
      ∃ τe, HasTy Γ e τe ∧ SDiv σ ρ e) : DivSpec P host p n d e' := by
  intro Γ τ σ ρ ht hT hdv μ s f hf hfn hd hr hh hfx us rest Q
  obtain ⟨τe, he, hde⟩ := hdiv Γ τ σ ρ ht hT hdv
  have h' := ih Γ τe σ ρ he hT hde μ s f hf hfn (hdepth ▸ hd) hr hh (hfixes ▸ hfx) us
    (expression c ++ rest) Q
  rw [hcode, expr_append]
  exact h'

theorem div_spec_fst {n d : Nat} {e : Tm} (ih : DivSpec P host p n d e) :
    DivSpec P host p n d (.fst e) :=
  div_spec_prefix ih rfl rfl rfl fun Γ τ σ ρ ht hT hdv => by
    cases ht with
    | fst he => exact ⟨_, he, div_fst hT he hdv⟩

theorem div_spec_snd {n d : Nat} {e : Tm} (ih : DivSpec P host p n d e) :
    DivSpec P host p n d (.snd e) :=
  div_spec_prefix ih rfl rfl rfl fun Γ τ σ ρ ht hT hdv => by
    cases ht with
    | snd he => exact ⟨_, he, div_snd hT he hdv⟩

/-- An injection with tag `k` whose payload diverges. -/
theorem div_spec_injTag {n d : Nat} {e e' : Tm} {k : BitVec 32} (ih : DivSpec P host p n d e)
    (hcode : compile p.table d e' = .intConst .i32 k :: .refI31 :: compile p.table d e ++
      [.structNew boxIdx]) (hdepth : e'.depth = e.depth) (hfixes : e'.fixes d = e.fixes d)
    (hdiv : ∀ Γ τ σ ρ, HasTy Γ e' τ → Typed Γ σ ρ → SDiv σ ρ e' →
      ∃ τe, HasTy Γ e τe ∧ SDiv σ ρ e) :
    DivSpec P host p n d e' := by
  intro Γ τ σ ρ ht hT hdv μ s f hf hfn hd hr hh hfx us rest Q
  obtain ⟨τe, he, hde⟩ := hdiv Γ τ σ ρ ht hT hdv
  have hc : vals us ++ (expression (compile p.table d e') ++ rest) = vals us ++
      (expression [.intConst .i32 k, .refI31] ++ (expression (compile p.table d e) ++
        (expression [.structNew boxIdx] ++ rest))) := by
    rw [hcode]; simp [expression]
  rw [hc]
  exact safe_constBox (ih Γ τe σ ρ he hT hde μ s f hf hfn (hdepth ▸ hd) hr hh (hfixes ▸ hfx)
    _ _ Q)

theorem div_spec_inl {n d : Nat} {e : Tm} (ih : DivSpec P host p n d e) :
    DivSpec P host p n d (.inl e) :=
  div_spec_injTag ih rfl rfl rfl fun Γ τ σ ρ ht _ hdv => by
    cases ht with
    | inl _ he => exact ⟨_, he, div_inl hdv⟩

theorem div_spec_inr {n d : Nat} {e : Tm} (ih : DivSpec P host p n d e) :
    DivSpec P host p n d (.inr e) :=
  div_spec_injTag ih rfl rfl rfl fun Γ τ σ ρ ht _ hdv => by
    cases ht with
    | inr _ he => exact ⟨_, he, div_inr hdv⟩

/-! ## Cells -/

theorem div_spec_ref {n d : Nat} {e : Tm} (ih : DivSpec P host p n d e) :
    DivSpec P host p n d (.ref e) :=
  div_spec_prefix ih rfl rfl rfl fun Γ τ σ ρ ht _ hdv => by
    cases ht with
    | ref he => exact ⟨_, he, div_ref hdv⟩

theorem div_spec_get {n d : Nat} {e : Tm} (ih : DivSpec P host p n d e) :
    DivSpec P host p n d (.get e) :=
  div_spec_prefix ih rfl rfl rfl fun Γ τ σ ρ ht hT hdv => by
    cases ht with
    | get he => exact ⟨_, he, div_get hT he hdv⟩

/-- `ref.cast (ref $cell)` on a cell, then a partial continuation. -/
theorem safe_castCell {n : Nat} {s : Store Nat} {f : Frame} (hf : FOK f) {us : List Val}
    {rest : List Admin} {Q : Post Nat} {addr : Nat} {fv : List FieldVal}
    (hs : s.structs[addr]? = some ⟨dCell, fv⟩)
    (h : Safe P host Q n ⟨s, f, vals (us ++ [.ref (.struct addr)]) ++ rest⟩) :
    Safe P host Q n
      ⟨s, f, vals (us ++ [.ref (.struct addr)]) ++ .plain (.refCast cellRef) :: rest⟩ :=
  safe_bridge (twp_castCell hf hs (twp_thenSafe' h))

/-- After a location, the stored value diverges. -/
theorem safe_setSecond (hfit : p.Fits) {n d : Nat} {a b : Tm} {k l : Nat} {Γ : List Ty}
    {τc : Ty} {σ σ₁ : Heap} {ρ : List FunRefClo.Val}
    (hea : eval k σ ρ a = some (.loc l, σ₁)) (ihb : DivSpec P host p n d b)
    (hb : HasTy Γ b τc) (hT₁ : Typed Γ σ₁ ρ) (hdb : SDiv σ₁ ρ b) {μ : List Nat}
    {s : Store Nat} {f : Frame} (hf : FOK f) (hfn : s.funcs[1]? = some (applyInst p))
    (hd : d + max a.depth b.depth < f.locals.length) (hr : EnvRep p.table μ s f d ρ)
    (hh : HeapRep p.table μ s σ) (hfx : ∀ x ∈ a.fixes d ++ b.fixes d, x ∈ p.table)
    (us : List Val) (rest : List Admin) (Q : Post Nat) :
    Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d a) ++
      (expression (.refCast cellRef :: (compile p.table d b ++
        [.structSet cellIdx (fx 0), .intConst .i32 1, .refI31])) ++ rest))⟩ := by
  refine safe_after hfit hea hf hfn (depth_left hd) hr hh (sub_left hfx)
    fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  obtain ⟨addr, hμl, rfl⟩ := hw
  obtain ⟨_, _, -, hst₁, -⟩ := hh₁.cell hμl
  have hb' : Safe P host Q n ⟨s₁, f₁, vals (us ++ [.ref (.struct addr)]) ++
      (expression (compile p.table d b) ++
        (expression [.structSet cellIdx (fx 0), .intConst .i32 1, .refI31] ++ rest))⟩ :=
    ihb Γ τc σ₁ ρ hb hT₁ hdb μ₁ s₁ f₁ (hf.of_agree hf₁) (hs₁.funcs hfn)
      (by rw [hf₁.2.1]; exact depth_right hd) (hr.of_agree hμ₁ hs₁.1 hf₁) hh₁ (sub_right hfx)
      _ _ Q
  rw [← expr_append] at hb'
  exact safe_castCell (hf.of_agree hf₁) hst₁ hb'

theorem div_spec_set (hfit : p.Fits) {n d : Nat} {a b : Tm} (iha : DivSpec P host p n d a)
    (ihb : DivSpec P host p n d b) : DivSpec P host p n d (.set a b) := by
  intro Γ τ σ ρ ht hT hdv μ s f hf hfn hd hr hh hfx us rest Q
  obtain ⟨τc, ha, hb⟩ : ∃ τc, HasTy Γ a (.ref τc) ∧ HasTy Γ b τc := by
    cases ht; exact ⟨_, ‹_›, ‹_›⟩
  show Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d a ++ .refCast cellRef ::
    compile p.table d b ++ [.structSet cellIdx (fx 0), .intConst .i32 1, .refI31]) ++ rest)⟩
  simp only [List.append_assoc, List.cons_append]
  rw [expr_append]
  rcases div_set hT ha hb hdv with hda | ⟨k, l, σ₁, hea, hT₁, hdb⟩
  · exact iha Γ _ σ ρ ha hT hda μ s f hf hfn (depth_left hd) hr hh (sub_left hfx) us _ Q
  · exact safe_setSecond hfit hea ihb hb hT₁ hdb hf hfn hd hr hh hfx us rest Q

end Silmaril.Proofs.Wasm.Models.FunRefCloDiv
