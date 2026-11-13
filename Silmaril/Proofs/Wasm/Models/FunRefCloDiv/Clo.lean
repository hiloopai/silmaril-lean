module

public import Silmaril.Proofs.Wasm.Models.FunRefCloDiv.Cases

/-!
# Compiled FunRefClo diverges where the source does: `case` and application

As `Silmaril.Proofs.Wasm.Models.FunCloDiv.Clo`, with the heap:

* `safe_branch`, `safe_caseArm`, `div_spec_case`: a `case` whose scrutinee returns runs its
  selected branch, which diverges (the tag dispatch is FunCloDiv's `safe_caseTail`);
* `safe_call`, `div_spec_app`: an application whose function and argument return calls
  `apply` on a closure whose body diverges, from the heap they return in (`Safe.callIdx` with
  `DivApplyAt n`, one step);
* **`div_spec_succ`**: `DivApplyAt n` gives `DivSpec (n + 1)` for every term, by induction on the
  term.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunRefCloDiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunRefCloCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunRefClo (Tm eval Prog Ty Heap HasTy)
open Silmaril.Wasm.Models.FunCompile (dBox lx fx boxIdx boxRef unbox getField anyref)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree len_setLocal setLocal_get lt_lim
  vals_pair expr_append depth_left depth_right depth_succ)
open Silmaril.Proofs.Wasm.Models.FunRefCloCompile (Rep EnvL Ext FOK EnvRep HeapRep sub_left
  sub_right branch)
open Silmaril.Proofs.Wasm.Models.FunCloDiv (safe_localGet safe_localSet safe_castBox safe_getBox
  safe_caseTail)
open Silmaril.Wasm.Logic.Core (Post)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-! ## `case` -/

/-- A `case` branch whose body diverges on the payload. -/
theorem safe_branch {n d : Nat} {t : Tm} (ih : DivSpec P host p n (d + 1) t) {Γ : List Ty}
    {τa τ : Ty} {σ : Heap} {ρ : List FunRefClo.Val} {u : FunRefClo.Val}
    (ht : HasTy (τa :: Γ) t τ) (hT : Typed (τa :: Γ) σ (u :: ρ)) (hdv : SDiv σ (u :: ρ) t)
    {μ : List Nat} {s : Store Nat} {f : Frame} (hf : FOK f)
    (hfn : s.funcs[1]? = some (applyInst p)) (hd : d + 1 + t.depth < f.locals.length)
    (hr : EnvRep p.table μ s f d ρ) (hh : HeapRep p.table μ s σ)
    (hfx : ∀ x ∈ t.fixes (d + 1), x ∈ p.table) {addr : Nat} {tagw wv : Val}
    (hloc : f.locals[d + 1]? = some (some (.ref (.struct addr))))
    (hst : s.structs[addr]? = some ⟨dBox, [.val tagw, .val wv]⟩) (hu : Rep p.table μ s u wv)
    (Q : Post Nat) :
    Safe P host Q n ⟨s, f, vals [] ++ expression (branch p.table d t)⟩ := by
  have hlt : d + 1 < f.locals.length := by omega
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.1 hlt
  have hbody : Safe P host Q n ⟨s, f.setLocal (lx (d + 1)) wv,
      vals [] ++ expression (compile p.table (d + 1) t)⟩ := by
    have h' := ih (τa :: Γ) τ σ (u :: ρ) ht hT hdv μ s _ (hf.setLocal _ wv) hfn
      (by rw [len_setLocal]; exact hd) (hr.cons hu hlt hlim) hh hfx [] [] Q
    simpa using h'
  show Safe P host Q n ⟨s, f, vals [] ++ .plain (.localGet (lx (d + 1))) ::
    .plain (.refCast boxRef) :: .plain (.structGet none boxIdx (fx 1)) ::
    .plain (.localSet (lx (d + 1))) :: expression (compile p.table (d + 1) t)⟩
  exact safe_localGet hf.1 hloc (safe_castBox hf.1 hst (safe_getBox hf.1 (by omega) hst
    (safe_localSet (w := wv) hf.1 hlt hbody)))

/-- A `case` whose scrutinee returns a `$box` with tag `tag`, selecting the branch `t`, which
diverges on the payload. -/
theorem safe_caseArm (hfit : p.Fits) {n d k : Nat} {e l r t : Tm} {tag : BitVec 31}
    {Γ : List Ty} {τa τ : Ty} {σ σ₁ : Heap} {ρ : List FunRefClo.Val} {u v : FunRefClo.Val}
    (hev : eval k σ ρ e = some (v, σ₁))
    (hrep : ∀ μ s w, Rep p.table μ s v w → ∃ addr wv, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 tag)), .val wv]⟩ ∧ Rep p.table μ s u wv)
    (hsel : (if tag.setWidth 32 ≠ 0 then branch p.table d r else branch p.table d l) =
      branch p.table d t)
    (iht : DivSpec P host p n (d + 1) t) (htt : HasTy (τa :: Γ) t τ)
    (hT : Typed (τa :: Γ) σ₁ (u :: ρ)) (hdt : SDiv σ₁ (u :: ρ) t) {μ : List Nat}
    {s : Store Nat} {f : Frame} (hf : FOK f) (hfn : s.funcs[1]? = some (applyInst p))
    (hde : d + e.depth < f.locals.length) (hdt' : d + 1 + t.depth < f.locals.length)
    (hr : EnvRep p.table μ s f d ρ) (hh : HeapRep p.table μ s σ)
    (hfxe : ∀ x ∈ e.fixes d, x ∈ p.table) (hfxt : ∀ x ∈ t.fixes (d + 1), x ∈ p.table)
    (us : List Val) (rest : List Admin) (Q : Post Nat) :
    Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d e) ++
      (expression (.localSet (lx (d + 1)) :: getField (d + 1) 0 ++ unbox ++
        [.if_ (.value anyref) (branch p.table d r) (branch p.table d l)]) ++ rest))⟩ := by
  refine safe_after hfit hev hf hfn hde hr hh hfxe fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  obtain ⟨addr, wv, hw', hst, hu⟩ := hrep μ₁ s₁ w hw
  have hf₁' : FOK f₁ := hf.of_agree hf₁
  have hlt : d + 1 < f.locals.length := by omega
  have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.1 hlt
  have hbr : Safe P host (labelPostK P host 1 [] us (seqPostK P host rest Q n) n) n
      ⟨s₁, f₁.setLocal (lx (d + 1)) (.ref (.struct addr)),
        vals [] ++ expression (branch p.table d t)⟩ :=
    safe_branch iht htt hT hdt (hf₁'.setLocal _ _) (hs₁.funcs hfn)
      (by rw [len_setLocal, hf₁.2.1]; exact hdt')
      ((hr.of_agree hμ₁ hs₁.1 hf₁).of_agree (List.prefix_refl _)
        (Silmaril.Proofs.Wasm.Models.FunRefCompile.BoxExt.refl _) (Agree.setLocal _ hlim))
      hh₁ hfxt (setLocal_get _ hlt₁ hlim) hst hu _
  rw [hw']
  refine safe_caseTail hf₁'.1 hlt₁ hst ?_
  rw [hsel]
  exact hbr

theorem div_spec_case (hfit : p.Fits) {n d : Nat} {e l r : Tm} (ihe : DivSpec P host p n d e)
    (ihl : DivSpec P host p n (d + 1) l) (ihr : DivSpec P host p n (d + 1) r) :
    DivSpec P host p n d (.case e l r) := by
  intro Γ τ σ ρ ht hT hdv μ s f hf hfn hd hr hh hfx us rest Q
  obtain ⟨σ₁', σ₂', he, hl, hr'⟩ : ∃ σ₁' σ₂', HasTy Γ e (.sum σ₁' σ₂') ∧
      HasTy (σ₁' :: Γ) l τ ∧ HasTy (σ₂' :: Γ) r τ := by
    cases ht; exact ⟨_, _, ‹_›, ‹_›, ‹_›⟩
  have hfx' : ∀ x ∈ e.fixes d ++ l.fixes (d + 1) ++ r.fixes (d + 1), x ∈ p.table := hfx
  have hdlr : d + 1 + max l.depth r.depth < f.locals.length := depth_succ (depth_right hd)
  show Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d e ++
    .localSet (lx (d + 1)) :: getField (d + 1) 0 ++ unbox ++
      [.if_ (.value anyref) (branch p.table d r) (branch p.table d l)]) ++ rest)⟩
  simp only [List.append_assoc]
  rw [expr_append]
  rcases div_case hT he hdv with hde | ⟨k, u, σ₁, hev, hT₁, hdl⟩ | ⟨k, u, σ₁, hev, hT₁, hdr⟩
  · exact ihe Γ _ σ ρ he hT hde μ s f hf hfn (depth_left hd) hr hh (sub_left (sub_left hfx'))
      us _ Q
  · exact safe_caseArm (tag := 0) hfit hev (fun _ _ _ hw => hw) rfl ihl hl hT₁ hdl hf
      hfn (depth_left hd) (depth_left hdlr) hr hh (sub_left (sub_left hfx'))
      (sub_right (sub_left hfx')) us rest Q
  · exact safe_caseArm (tag := 1) hfit hev (fun _ _ _ hw => hw) rfl ihr hr' hT₁ hdr hf
      hfn (depth_left hd) (depth_right hdlr) hr hh (sub_left (sub_left hfx')) (sub_right hfx')
      us rest Q

/-! ## Application -/

/-- **A call of `apply` on a closure whose body diverges.** -/
theorem safe_call (hfit : p.Fits) {n d k : Nat} {f a b : Tm} {σ σ₁ σ₂ : Heap}
    {ρ ρ' : List FunRefClo.Val} {u : FunRefClo.Val} {Γb : List Ty} {τ : Ty}
    (happ : DivApplyAt P host p n) (hfk : eval k σ ρ f = some (.clo b ρ', σ₁))
    (hak : eval k σ₁ ρ a = some (u, σ₂)) (hΓ : Typed Γb σ₂ (u :: .clo b ρ' :: ρ'))
    (hbt : HasTy Γb b τ) (hdb : SDiv σ₂ (u :: .clo b ρ' :: ρ') b) {μ : List Nat}
    {s : Store Nat} {fr : Frame} (hfr : FOK fr) (hfn : s.funcs[1]? = some (applyInst p))
    (hd : d + max f.depth a.depth < fr.locals.length) (hr : EnvRep p.table μ s fr d ρ)
    (hh : HeapRep p.table μ s σ) (hfx : ∀ x ∈ f.fixes d ++ a.fixes d, x ∈ p.table)
    (us : List Val) (rest : List Admin) (Q : Post Nat) :
    Safe P host Q (n + 1) ⟨s, fr, vals us ++ (expression (compile p.table d f) ++
      (expression (compile p.table d a) ++ (expression [.call ⟨1⟩] ++ rest)))⟩ := by
  refine safe_after hfit hfk hfr hfn (depth_left hd) hr hh (sub_left hfx)
    fun μ₁ s₁ f₁ wc hμ₁ hs₁ hf₁ hh₁ hwc => ?_
  refine safe_after hfit hak (hfr.of_agree hf₁) (hs₁.funcs hfn)
    (by rw [hf₁.2.1]; exact depth_right hd) (hr.of_agree hμ₁ hs₁.1 hf₁) hh₁ (sub_right hfx)
    fun μ₂ s₂ f₂ wu hμ₂ hs₂ hf₂ hh₂ hwu => ?_
  have hfn₂ : s₂.funcs[1]? = some (applyInst p) := (hs₁.trans hs₂).funcs hfn
  have hx : f₂.module.funcs[(⟨1⟩ : FuncIdx).toNat]? = some 1 :=
    (hfr.of_agree (hf₁.trans hf₂)).2.1
  have hpre : (divApplySpec p b ρ' u σ₂ μ₂).pre s₂ [wc, wu] :=
    ⟨hfn₂, hh₂, wc, wu, rfl, hwc.mono hμ₂ hs₂.1, hwu⟩
  have hcall : Safe P host Q (n + 1)
      ⟨s₂, f₂, vals (us ++ [wc, wu]) ++ .plain (.call ⟨1⟩) :: rest⟩ :=
    Safe.callIdx hx hfn₂ (happ b ρ' u σ₂ μ₂ Γb τ hΓ hbt hdb) hpre fun s' o hpost => by
      rcases hpost with ⟨-, ⟨_, -, h⟩ | ⟨-, h⟩ | ⟨_, -, h⟩⟩ <;> exact h.elim
  rw [vals_pair]
  exact hcall

theorem div_spec_app (hfit : p.Fits) {n d : Nat} {f a : Tm} (happ : DivApplyAt P host p n)
    (ihf : DivSpec P host p (n + 1) d f) (iha : DivSpec P host p (n + 1) d a) :
    DivSpec P host p (n + 1) d (.app f a) := by
  intro Γ τ σ ρ ht hT hdv μ s fr hfr hfn hd hr hh hfx us rest Q
  obtain ⟨τa, hf, ha⟩ : ∃ τa, HasTy Γ f (.arr τa τ) ∧ HasTy Γ a τa := by
    cases ht; exact ⟨_, ‹_›, ‹_›⟩
  show Safe P host Q (n + 1) ⟨s, fr, vals us ++ (expression (compile p.table d f ++
    compile p.table d a ++ [.call ⟨1⟩]) ++ rest)⟩
  simp only [List.append_assoc, expr_append]
  rcases div_app hT hf ha hdv with hdf | ⟨k, b, ρ', σ₁, hfk, hT₁, hda⟩ |
      ⟨k, b, ρ', σ₁, u, σ₂, Γb, hfk, hak, hΓ, hbt, hdb⟩
  · exact ihf Γ _ σ ρ hf hT hdf μ s fr hfr hfn (depth_left hd) hr hh (sub_left hfx) us _ Q
  · refine safe_after hfit hfk hfr hfn (depth_left hd) hr hh (sub_left hfx)
      fun μ₁ s₁ f₁ wc hμ₁ hs₁ hf₁ hh₁ hwc => ?_
    exact iha Γ τa σ₁ ρ ha hT₁ hda μ₁ s₁ f₁ (hfr.of_agree hf₁) (hs₁.funcs hfn)
      (by rw [hf₁.2.1]; exact depth_right hd) (hr.of_agree hμ₁ hs₁.1 hf₁) hh₁ (sub_right hfx)
      _ _ Q
  · exact safe_call hfit happ hfk hak hΓ hbt hdb hfr hfn hd hr hh hfx us rest Q

/-! ## Every term -/

/-- **`DivApplyAt n` gives `DivSpec (n + 1)` for every term**, by induction on the term. -/
theorem div_spec_succ (hfit : p.Fits) {n : Nat} (happ : DivApplyAt P host p n) :
    ∀ (e : Tm) (d : Nat), DivSpec P host p (n + 1) d e
  | .var i, d => div_spec_var _ d i
  | .int x, d => div_spec_int _ d x
  | .bool b, d => div_spec_bool _ d b
  | .arith _ a b, d =>
    div_spec_arith hfit (div_spec_succ hfit happ a d) (div_spec_succ hfit happ b d)
  | .cmp _ a b, d => div_spec_cmp hfit (div_spec_succ hfit happ a d) (div_spec_succ hfit happ b d)
  | .ite c t e, d => div_spec_ite hfit (div_spec_succ hfit happ c d)
      (div_spec_succ hfit happ t d) (div_spec_succ hfit happ e d)
  | .let_ a b, d =>
    div_spec_let hfit (div_spec_succ hfit happ a d) (div_spec_succ hfit happ b (d + 1))
  | .pair a b, d => div_spec_pair hfit (div_spec_succ hfit happ a d) (div_spec_succ hfit happ b d)
  | .fst e, d => div_spec_fst (div_spec_succ hfit happ e d)
  | .snd e, d => div_spec_snd (div_spec_succ hfit happ e d)
  | .inl e, d => div_spec_inl (div_spec_succ hfit happ e d)
  | .inr e, d => div_spec_inr (div_spec_succ hfit happ e d)
  | .case e l r, d => div_spec_case hfit (div_spec_succ hfit happ e d)
      (div_spec_succ hfit happ l (d + 1)) (div_spec_succ hfit happ r (d + 1))
  | .fix b, d => div_spec_fix _ d b
  | .app f a, d => div_spec_app hfit happ (div_spec_succ hfit happ f d)
      (div_spec_succ hfit happ a d)
  | .ref e, d => div_spec_ref (div_spec_succ hfit happ e d)
  | .get e, d => div_spec_get (div_spec_succ hfit happ e d)
  | .set a b, d => div_spec_set hfit (div_spec_succ hfit happ a d) (div_spec_succ hfit happ b d)

end Silmaril.Proofs.Wasm.Models.FunRefCloDiv
