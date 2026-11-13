module

public import Silmaril.Proofs.Wasm.Models.FunCloDiv.Cases

/-!
# Compiled FunClo diverges where the source does: `case` and application

* `safe_caseTail`, `safe_branch`, `div_spec_case`: a `case` whose scrutinee returns runs its
  selected branch, which diverges;
* `safe_call`, `div_spec_app`: an application whose function and argument return calls
  `apply` on a closure whose body diverges (`Safe.callIdx` with `DivApplyAt n`, one step);
* **`div_spec_succ`**: `DivApplyAt n` gives `DivSpec (n + 1)` for every term, by induction on the
  term.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCloDiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunCloCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunClo (Tm eval Prog Ty HasTy ValTy EnvTy eval_sound)
open Silmaril.Wasm.Models.FunCompile (dBox lx fx boxIdx boxRef unbox getField anyref)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree len_setLocal setLocal_get lt_lim
  vals_pair expr_append depth_left depth_right depth_succ)
open Silmaril.Proofs.Wasm.Models.FunCloCompile (Rep EnvL Ext FOK EnvRep sub_left sub_right
  Ext.funcs branch)
open Silmaril.Wasm.Logic.Core (Post)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-! ## `case` -/

/-- The dispatch of a `case` on the tag of a `$box`, with a selected branch safe for `n`
steps. -/
theorem safe_caseTail {n d : Nat} {s : Store Nat} {f : Frame} (hf : FrameOK f)
    (hlt : d + 1 < f.locals.length) {addr : Nat} {tag : BitVec 31} {wv : Val}
    (hst : s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 tag)), .val wv]⟩)
    {br bl : List Instr} {us : List Val} {rest : List Admin} {Q : Post Nat}
    (hb : Safe P host (labelPostK P host 1 [] us (seqPostK P host rest Q n) n) n
      ⟨s, f.setLocal (lx (d + 1)) (.ref (.struct addr)),
        vals [] ++ expression (if tag.setWidth 32 ≠ 0 then br else bl)⟩) :
    Safe P host Q n ⟨s, f, vals (us ++ [.ref (.struct addr)]) ++
      (expression (.localSet (lx (d + 1)) :: getField (d + 1) 0 ++ unbox ++
        [.if_ (.value anyref) br bl]) ++ rest)⟩ := by
  have hf₂ : FrameOK (f.setLocal (lx (d + 1)) (.ref (.struct addr))) := hf.setLocal _ _
  have hloc := setLocal_get (f := f) (.ref (.struct addr)) hlt (lt_lim hf hlt)
  show Safe P host Q n ⟨s, f, vals (us ++ [.ref (.struct addr)]) ++
    .plain (.localSet (lx (d + 1))) :: .plain (.localGet (lx (d + 1))) ::
    .plain (.refCast boxRef) :: .plain (.structGet none boxIdx (fx 0)) ::
    (expression unbox ++ (.plain (.if_ (.value anyref) br bl) :: rest))⟩
  exact safe_localSet hf hlt (safe_localGet hf₂ hloc (safe_castBox hf₂ hst
    (safe_getBox hf₂ (by omega) hst (safe_unbox (safe_ifBlock hb)))))

/-- A `case` branch whose body diverges on the payload. -/
theorem safe_branch {n d : Nat} {t : Tm} (ih : DivSpec P host p n (d + 1) t) {Γ : List Ty}
    {σ τ : Ty} {ρ : List FunClo.Val} {u : FunClo.Val} (ht : HasTy (σ :: Γ) t τ)
    (hρ : EnvTy (u :: ρ) (σ :: Γ)) (hdv : SDiv (u :: ρ) t) {s : Store Nat} {f : Frame}
    (hf : FOK f) (hfn : s.funcs[1]? = some (applyInst p))
    (hd : d + 1 + t.depth < f.locals.length) (hr : EnvRep p.table s f d ρ)
    (hfx : ∀ x ∈ t.fixes (d + 1), x ∈ p.table) {addr : Nat} {tagw wv : Val}
    (hloc : f.locals[d + 1]? = some (some (.ref (.struct addr))))
    (hst : s.structs[addr]? = some ⟨dBox, [.val tagw, .val wv]⟩) (hu : Rep p.table s u wv)
    (Q : Post Nat) :
    Safe P host Q n ⟨s, f, vals [] ++ expression (branch p.table d t)⟩ := by
  have hlt : d + 1 < f.locals.length := by omega
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.1 hlt
  have hbody : Safe P host Q n ⟨s, f.setLocal (lx (d + 1)) wv,
      vals [] ++ expression (compile p.table (d + 1) t)⟩ := by
    have h' := ih (σ :: Γ) τ (u :: ρ) ht hρ hdv s _ (hf.setLocal _ wv) hfn
      (by rw [len_setLocal]; exact hd) (hr.cons hu hlt hlim) hfx [] [] Q
    simpa using h'
  show Safe P host Q n ⟨s, f, vals [] ++ .plain (.localGet (lx (d + 1))) ::
    .plain (.refCast boxRef) :: .plain (.structGet none boxIdx (fx 1)) ::
    .plain (.localSet (lx (d + 1))) :: expression (compile p.table (d + 1) t)⟩
  exact safe_localGet hf.1 hloc (safe_castBox hf.1 hst (safe_getBox hf.1 (by omega) hst
    (safe_localSet (w := wv) hf.1 hlt hbody)))

/-- A `case` whose scrutinee returns a `$box` with tag `tag`, selecting the branch `t`, which
diverges on the payload. -/
theorem safe_caseArm (hfit : p.Fits) {n d k : Nat} {e l r t : Tm} {tag : BitVec 31}
    {Γ : List Ty} {σ τ : Ty} {ρ : List FunClo.Val} {u v : FunClo.Val}
    (hev : eval k ρ e = some v)
    (hrep : ∀ s w, Rep p.table s v w → ∃ addr wv, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 tag)), .val wv]⟩ ∧ Rep p.table s u wv)
    (hsel : (if tag.setWidth 32 ≠ 0 then branch p.table d r else branch p.table d l) =
      branch p.table d t)
    (iht : DivSpec P host p n (d + 1) t) (htt : HasTy (σ :: Γ) t τ)
    (hρ : EnvTy (u :: ρ) (σ :: Γ)) (hdt : SDiv (u :: ρ) t) {s : Store Nat} {f : Frame}
    (hf : FOK f) (hfn : s.funcs[1]? = some (applyInst p)) (hde : d + e.depth < f.locals.length)
    (hdt' : d + 1 + t.depth < f.locals.length) (hr : EnvRep p.table s f d ρ)
    (hfxe : ∀ x ∈ e.fixes d, x ∈ p.table) (hfxt : ∀ x ∈ t.fixes (d + 1), x ∈ p.table)
    (us : List Val) (rest : List Admin) (Q : Post Nat) :
    Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d e) ++
      (expression (.localSet (lx (d + 1)) :: getField (d + 1) 0 ++ unbox ++
        [.if_ (.value anyref) (branch p.table d r) (branch p.table d l)]) ++ rest))⟩ := by
  refine safe_after hfit hev hf hfn hde hr hfxe fun s₁ f₁ w hs₁ hf₁ hw => ?_
  obtain ⟨addr, wv, hw', hst, hu⟩ := hrep s₁ w hw
  have hf₁' : FOK f₁ := hf.of_agree hf₁
  have hlt : d + 1 < f.locals.length := by omega
  have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.1 hlt
  have hbr : Safe P host (labelPostK P host 1 [] us (seqPostK P host rest Q n) n) n
      ⟨s₁, f₁.setLocal (lx (d + 1)) (.ref (.struct addr)),
        vals [] ++ expression (branch p.table d t)⟩ :=
    safe_branch iht htt hρ hdt (hf₁'.setLocal _ _) (hs₁.funcs hfn)
      (by rw [len_setLocal, hf₁.2.1]; exact hdt')
      ((hr.of_agree hs₁.1 hf₁).of_agree (List.prefix_refl _) (Agree.setLocal _ hlim)) hfxt
      (setLocal_get _ hlt₁ hlim) hst hu _
  rw [hw']
  refine safe_caseTail hf₁'.1 hlt₁ hst ?_
  rw [hsel]
  exact hbr

theorem div_spec_case (hfit : p.Fits) {n d : Nat} {e l r : Tm} (ihe : DivSpec P host p n d e)
    (ihl : DivSpec P host p n (d + 1) l) (ihr : DivSpec P host p n (d + 1) r) :
    DivSpec P host p n d (.case e l r) := by
  intro Γ τ ρ ht hρ hdv s f hf hfn hd hr hfx us rest Q
  obtain ⟨σ₁, σ₂, he, hl, hr'⟩ : ∃ σ₁ σ₂, HasTy Γ e (.sum σ₁ σ₂) ∧ HasTy (σ₁ :: Γ) l τ ∧
      HasTy (σ₂ :: Γ) r τ := by
    cases ht; exact ⟨_, _, ‹_›, ‹_›, ‹_›⟩
  have hfx' : ∀ x ∈ e.fixes d ++ l.fixes (d + 1) ++ r.fixes (d + 1), x ∈ p.table := hfx
  have hdlr : d + 1 + max l.depth r.depth < f.locals.length := depth_succ (depth_right hd)
  show Safe P host Q n ⟨s, f, vals us ++ (expression (compile p.table d e ++
    .localSet (lx (d + 1)) :: getField (d + 1) 0 ++ unbox ++
      [.if_ (.value anyref) (branch p.table d r) (branch p.table d l)]) ++ rest)⟩
  simp only [List.append_assoc]
  rw [expr_append]
  rcases div_case hρ he hdv with hde | ⟨k, u, hev, hu, hdl⟩ | ⟨k, u, hev, hu, hdr⟩
  · exact ihe Γ _ ρ he hρ hde s f hf hfn (depth_left hd) hr (sub_left (sub_left hfx')) us _ Q
  · exact safe_caseArm (tag := 0) hfit hev (fun _ _ hw => hw) rfl ihl hl (.cons hu hρ) hdl hf
      hfn (depth_left hd) (depth_left hdlr) hr (sub_left (sub_left hfx'))
      (sub_right (sub_left hfx')) us rest Q
  · exact safe_caseArm (tag := 1) hfit hev (fun _ _ hw => hw) rfl ihr hr' (.cons hu hρ) hdr hf
      hfn (depth_left hd) (depth_right hdlr) hr (sub_left (sub_left hfx')) (sub_right hfx')
      us rest Q

/-! ## Application -/

/-- **A call of `apply` on a closure whose body diverges.** -/
theorem safe_call (hfit : p.Fits) {n d k : Nat} {f a b : Tm} {ρ ρ' : List FunClo.Val}
    {u : FunClo.Val} {Γb : List Ty} {τ : Ty} (happ : DivApplyAt P host p n)
    (hfk : eval k ρ f = some (.clo b ρ')) (hak : eval k ρ a = some u)
    (hΓ : EnvTy (u :: .clo b ρ' :: ρ') Γb) (hbt : HasTy Γb b τ)
    (hdb : SDiv (u :: .clo b ρ' :: ρ') b) {s : Store Nat} {fr : Frame} (hfr : FOK fr)
    (hfn : s.funcs[1]? = some (applyInst p)) (hd : d + max f.depth a.depth < fr.locals.length)
    (hr : EnvRep p.table s fr d ρ) (hfx : ∀ x ∈ f.fixes d ++ a.fixes d, x ∈ p.table)
    (us : List Val) (rest : List Admin) (Q : Post Nat) :
    Safe P host Q (n + 1) ⟨s, fr, vals us ++ (expression (compile p.table d f) ++
      (expression (compile p.table d a) ++ (expression [.call ⟨1⟩] ++ rest)))⟩ := by
  refine safe_after hfit hfk hfr hfn (depth_left hd) hr (sub_left hfx)
    fun s₁ f₁ wc hs₁ hf₁ hwc => ?_
  refine safe_after hfit hak (hfr.of_agree hf₁) (hs₁.funcs hfn)
    (by rw [hf₁.2.1]; exact depth_right hd) (hr.of_agree hs₁.1 hf₁) (sub_right hfx)
    fun s₂ f₂ wu hs₂ hf₂ hwu => ?_
  have hfn₂ : s₂.funcs[1]? = some (applyInst p) := (hs₁.trans hs₂).funcs hfn
  have hx : f₂.module.funcs[(⟨1⟩ : FuncIdx).toNat]? = some 1 :=
    (hfr.of_agree (hf₁.trans hf₂)).2
  have hpre : (divApplySpec p b ρ' u).pre s₂ [wc, wu] :=
    ⟨hfn₂, wc, wu, rfl, hwc.mono hs₂.1, hwu⟩
  have hcall : Safe P host Q (n + 1)
      ⟨s₂, f₂, vals (us ++ [wc, wu]) ++ .plain (.call ⟨1⟩) :: rest⟩ :=
    Safe.callIdx hx hfn₂ (happ b ρ' u Γb τ hΓ hbt hdb) hpre fun s' o hpost => by
      rcases hpost with ⟨-, ⟨_, -, h⟩ | ⟨-, h⟩ | ⟨_, -, h⟩⟩ <;> exact h.elim
  rw [vals_pair]
  exact hcall

theorem div_spec_app (hfit : p.Fits) {n d : Nat} {f a : Tm} (happ : DivApplyAt P host p n)
    (ihf : DivSpec P host p (n + 1) d f) (iha : DivSpec P host p (n + 1) d a) :
    DivSpec P host p (n + 1) d (.app f a) := by
  intro Γ τ ρ ht hρ hdv s fr hfr hfn hd hr hfx us rest Q
  obtain ⟨σ, hf, ha⟩ : ∃ σ, HasTy Γ f (.arr σ τ) ∧ HasTy Γ a σ := by
    cases ht; exact ⟨_, ‹_›, ‹_›⟩
  show Safe P host Q (n + 1) ⟨s, fr, vals us ++ (expression (compile p.table d f ++
    compile p.table d a ++ [.call ⟨1⟩]) ++ rest)⟩
  simp only [List.append_assoc, expr_append]
  rcases div_app hρ hf ha hdv with hdf | ⟨k, b, ρ', hfk, hda⟩ |
      ⟨k, b, ρ', u, Γb, hfk, hak, hΓ, hbt, hdb⟩
  · exact ihf Γ _ ρ hf hρ hdf s fr hfr hfn (depth_left hd) hr (sub_left hfx) us _ Q
  · refine safe_after hfit hfk hfr hfn (depth_left hd) hr (sub_left hfx)
      fun s₁ f₁ wc hs₁ hf₁ hwc => ?_
    exact iha Γ σ ρ ha hρ hda s₁ f₁ (hfr.of_agree hf₁) (hs₁.funcs hfn)
      (by rw [hf₁.2.1]; exact depth_right hd) (hr.of_agree hs₁.1 hf₁) (sub_right hfx) _ _ Q
  · exact safe_call hfit happ hfk hak hΓ hbt hdb hfr hfn hd hr hfx us rest Q

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

end Silmaril.Proofs.Wasm.Models.FunCloDiv
