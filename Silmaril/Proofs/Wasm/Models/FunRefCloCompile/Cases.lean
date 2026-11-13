module

public import Silmaril.Proofs.Wasm.Models.FunRefCloCompile.Rep

/-!
# Compiling FunRefClo: the FunLang constructs and the cells

`Spec P host p (k + 1) d e` for every constructor of `Tm` other than `fix` and `app`, from
`Spec … k` of its subterms (`spec_var` … `spec_case`, `spec_ref`, `spec_get`, `spec_set`). The
proofs follow `Silmaril.Proofs.Wasm.Models.FunCloCompile.Cases` and
`Silmaril.Proofs.Wasm.Models.FunRefCompile.Cases`, with fuel, the closure table and the heap.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunRefCloCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunRefCloCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunRefClo (Tm eval Prog Heap)
open Silmaril.Wasm.Models.FunLang (Arith Cmp)
open Silmaril.Wasm.Models.FunCompile (dBox lx fx boxIdx boxRef unbox getField anyref)
open Silmaril.Wasm.Models.FunRefCompile (cellIdx cellRef dCell)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree twp_unbox twp_box twp_castBox twp_getBox
  twp_newBox addStruct_get addStruct_prefix twp_localGet twp_localSet twp_constBox len_setLocal
  setLocal_get lt_lim vals_pair arith_wasm cmp_wasm bool32_31 setWidth_31_32 twp_ifBlock
  expr_append depth_left depth_right depth_succ twp_caseTail getElem?_of_prefix)
open Silmaril.Proofs.Wasm.Models.FunRefCompile (BoxExt)
open Silmaril.Wasm.Logic.Core (Post)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-! ## Inversion of evaluation -/

section Inv

variable {k : Nat} {σ σ' : Heap} {ρ : List FunRefClo.Val} {v : FunRefClo.Val}

theorem eval_var_inv {i : Nat} (h : eval (k + 1) σ ρ (.var i) = some (v, σ')) :
    ρ[i]? = some v ∧ σ' = σ := by
  simp only [eval, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨u, hu, rfl, rfl⟩ := h
  exact ⟨hu, rfl⟩

theorem eval_arith_inv {op : Arith} {a b : Tm}
    (h : eval (k + 1) σ ρ (.arith op a b) = some (v, σ')) :
    ∃ x σ₁ y, eval k σ ρ a = some (.int x, σ₁) ∧ eval k σ₁ ρ b = some (.int y, σ') ∧
      v = .int (op.eval x y) := by
  simp only [eval] at h
  split at h
  · next x σ₁ ha =>
    split at h
    · next y σ₂ hb => cases h; exact ⟨x, σ₁, y, ha, hb, rfl⟩
    · cases h
  · cases h

theorem eval_cmp_inv {op : Cmp} {a b : Tm}
    (h : eval (k + 1) σ ρ (.cmp op a b) = some (v, σ')) :
    ∃ x σ₁ y, eval k σ ρ a = some (.int x, σ₁) ∧ eval k σ₁ ρ b = some (.int y, σ') ∧
      v = .bool (op.eval x y) := by
  simp only [eval] at h
  split at h
  · next x σ₁ ha =>
    split at h
    · next y σ₂ hb => cases h; exact ⟨x, σ₁, y, ha, hb, rfl⟩
    · cases h
  · cases h

theorem eval_ite_inv {c t e : Tm} (h : eval (k + 1) σ ρ (.ite c t e) = some (v, σ')) :
    ∃ b σ₁, eval k σ ρ c = some (.bool b, σ₁) ∧
      eval k σ₁ ρ (if b then t else e) = some (v, σ') := by
  simp only [eval] at h
  split at h
  · next σ₁ hc => exact ⟨true, σ₁, hc, h⟩
  · next σ₁ hc => exact ⟨false, σ₁, hc, h⟩
  · cases h

theorem eval_let_inv {a b : Tm} (h : eval (k + 1) σ ρ (.let_ a b) = some (v, σ')) :
    ∃ u σ₁, eval k σ ρ a = some (u, σ₁) ∧ eval k σ₁ (u :: ρ) b = some (v, σ') := by
  simp only [eval] at h
  split at h
  · next u σ₁ hu => exact ⟨u, σ₁, hu, h⟩
  · cases h

theorem eval_pair_inv {a b : Tm} (h : eval (k + 1) σ ρ (.pair a b) = some (v, σ')) :
    ∃ x σ₁ y, eval k σ ρ a = some (x, σ₁) ∧ eval k σ₁ ρ b = some (y, σ') ∧ v = .pair x y := by
  simp only [eval] at h
  split at h
  · next x σ₁ ha =>
    split at h
    · next y σ₂ hb => cases h; exact ⟨x, σ₁, y, ha, hb, rfl⟩
    · cases h
  · cases h

theorem eval_fst_inv {e : Tm} (h : eval (k + 1) σ ρ (.fst e) = some (v, σ')) :
    ∃ y, eval k σ ρ e = some (.pair v y, σ') := by
  simp only [eval] at h
  split at h
  · next x y σ₁ he => cases h; exact ⟨y, he⟩
  · cases h

theorem eval_snd_inv {e : Tm} (h : eval (k + 1) σ ρ (.snd e) = some (v, σ')) :
    ∃ x, eval k σ ρ e = some (.pair x v, σ') := by
  simp only [eval] at h
  split at h
  · next x y σ₁ he => cases h; exact ⟨x, he⟩
  · cases h

theorem eval_inl_inv {e : Tm} (h : eval (k + 1) σ ρ (.inl e) = some (v, σ')) :
    ∃ u, eval k σ ρ e = some (u, σ') ∧ v = .inl u := by
  simp only [eval, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨u, σ₁⟩, hu, rfl, rfl⟩ := h
  exact ⟨u, hu, rfl⟩

theorem eval_inr_inv {e : Tm} (h : eval (k + 1) σ ρ (.inr e) = some (v, σ')) :
    ∃ u, eval k σ ρ e = some (u, σ') ∧ v = .inr u := by
  simp only [eval, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨u, σ₁⟩, hu, rfl, rfl⟩ := h
  exact ⟨u, hu, rfl⟩

theorem eval_case_inv {e l r : Tm} (h : eval (k + 1) σ ρ (.case e l r) = some (v, σ')) :
    (∃ u σ₁, eval k σ ρ e = some (.inl u, σ₁) ∧ eval k σ₁ (u :: ρ) l = some (v, σ')) ∨
      (∃ u σ₁, eval k σ ρ e = some (.inr u, σ₁) ∧ eval k σ₁ (u :: ρ) r = some (v, σ')) := by
  simp only [eval] at h
  split at h
  · next u σ₁ hu => exact .inl ⟨u, σ₁, hu, h⟩
  · next u σ₁ hu => exact .inr ⟨u, σ₁, hu, h⟩
  · cases h

theorem eval_ref_inv {e : Tm} (h : eval (k + 1) σ ρ (.ref e) = some (v, σ')) :
    ∃ u σ₁, eval k σ ρ e = some (u, σ₁) ∧ v = .loc σ₁.length ∧ σ' = σ₁ ++ [u] := by
  simp only [eval] at h
  split at h
  · next u σ₁ hu => cases h; exact ⟨u, σ₁, hu, rfl, rfl⟩
  · cases h

theorem eval_get_inv {e : Tm} (h : eval (k + 1) σ ρ (.get e) = some (v, σ')) :
    ∃ l, eval k σ ρ e = some (.loc l, σ') ∧ σ'[l]? = some v := by
  simp only [eval] at h
  split at h
  · next l σ₁ he =>
    obtain ⟨u, hu, heq⟩ : ∃ u, σ₁[l]? = some u ∧ (u, σ₁) = (v, σ') := by
      simpa only [Option.map_eq_some_iff] using h
    cases heq
    exact ⟨l, he, hu⟩
  · cases h

theorem eval_set_inv {a b : Tm} (h : eval (k + 1) σ ρ (.set a b) = some (v, σ')) :
    ∃ l σ₁ u σ₂, eval k σ ρ a = some (.loc l, σ₁) ∧ eval k σ₁ ρ b = some (u, σ₂) ∧
      l < σ₂.length ∧ v = .bool true ∧ σ' = σ₂.set l u := by
  simp only [eval] at h
  split at h
  · next l σ₁ ha =>
    split at h
    · next u σ₂ hb =>
      split at h
      · next hl => cases h; exact ⟨l, σ₁, u, σ₂, ha, hb, hl, rfl, rfl⟩
      · cases h
    · cases h
  · cases h

end Inv

/-! ## Bookkeeping -/

theorem sub_left {L l₁ l₂ : List (Nat × Tm)} (h : ∀ x ∈ l₁ ++ l₂, x ∈ L) : ∀ x ∈ l₁, x ∈ L :=
  fun x hx => h x (List.mem_append_left _ hx)

theorem sub_right {L l₁ l₂ : List (Nat × Tm)} (h : ∀ x ∈ l₁ ++ l₂, x ∈ L) : ∀ x ∈ l₂, x ∈ L :=
  fun x hx => h x (List.mem_append_right _ hx)

theorem Cont.unboxInt {d : Nat} {μ : List Nat} {s : Store Nat} {f : Frame} {x : BitVec 31}
    {σ' : Heap} {us : List Val} {rest : List Admin} {Q : Post Nat}
    (h : ∀ μ' s' f', μ <+: μ' → Ext s s' → Agree d f f' → HeapRep p.table μ' s' σ' →
      TWP P host s' f' (vals (us ++ [.i32 (x.setWidth 32)]) ++ rest) Q) :
    Cont P host p.table d μ s f (.int x) σ' us (expression unbox ++ rest) Q := by
  intro μ' s' f' w hμ hs hf hh hw
  have hw' : w = .ref (.i31 x) := hw
  rw [hw']
  exact twp_unbox (h μ' s' f' hμ hs hf hh)

theorem Cont.unboxBool {d : Nat} {μ : List Nat} {s : Store Nat} {f : Frame} {b : Bool}
    {σ' : Heap} {us : List Val} {rest : List Admin} {Q : Post Nat}
    (h : ∀ μ' s' f', μ <+: μ' → Ext s s' → Agree d f f' → HeapRep p.table μ' s' σ' →
      TWP P host s' f'
        (vals (us ++ [.i32 ((if b then (1 : BitVec 31) else 0).setWidth 32)]) ++ rest) Q) :
    Cont P host p.table d μ s f (.bool b) σ' us (expression unbox ++ rest) Q := by
  intro μ' s' f' w hμ hs hf hh hw
  have hw' : w = .ref (.i31 (if b then 1 else 0)) := hw
  rw [hw']
  exact twp_unbox (h μ' s' f' hμ hs hf hh)

/-! ## Leaves -/

theorem spec_var (k d i : Nat) : Spec P host p (k + 1) d (.var i) := by
  intro σ ρ v σ' hv μ s f hf _ _ hr hh _ us rest Q hk
  obtain ⟨hi, rfl⟩ := eval_var_inv hv
  obtain ⟨w, hw, hrep⟩ := hr.2 i v hi
  exact twp_localGet hf.1 hw (hk μ s f w (List.prefix_refl _) (Ext.refl s) (Agree.refl d f) hh hrep)

theorem spec_int (k d : Nat) (n : BitVec 31) : Spec P host p (k + 1) d (.int n) := by
  intro σ ρ v σ' hv μ s f _ _ _ _ hh _ us rest Q hk
  have hv' : (v, σ') = (.int n, σ) := (Option.some.inj hv).symm
  cases hv'
  have hw : Rep p.table μ s (.int n) (.ref (.i31 ((n.setWidth 32).setWidth 31))) := by
    rw [setWidth_31_32]; rfl
  exact twp_constBox (hk μ s f _ (List.prefix_refl _) (Ext.refl s) (Agree.refl d f) hh hw)

theorem spec_bool (k d : Nat) (b : Bool) : Spec P host p (k + 1) d (.bool b) := by
  intro σ ρ v σ' hv μ s f _ _ _ _ hh _ us rest Q hk
  have hv' : (v, σ') = (.bool b, σ) := (Option.some.inj hv).symm
  cases hv'
  have hw : Rep p.table μ s (.bool b)
      (.ref (.i31 ((if b then (1 : BitVec 32) else 0).setWidth 31))) := by
    cases b <;> rfl
  exact twp_constBox (hk μ s f _ (List.prefix_refl _) (Ext.refl s) (Agree.refl d f) hh hw)

/-! ## Arithmetic and comparisons -/

theorem twp_arithTail {d : Nat} {μ μ₂ : List Nat} {s s₂ : Store Nat} {f f₂ : Frame}
    {op : Arith} {x y : BitVec 31} {σ' : Heap} {us : List Val} {rest : List Admin}
    {Q : Post Nat} (hk : Cont P host p.table d μ s f (.int (op.eval x y)) σ' us rest Q)
    (hμ : μ <+: μ₂) (hs : Ext s s₂) (hf : Agree d f f₂) (hh : HeapRep p.table μ₂ s₂ σ') :
    TWP P host s₂ f₂ (vals ((us ++ [.i32 (x.setWidth 32)]) ++ [.i32 (y.setWidth 32)]) ++
      (expression [.intBinOp .i32 (FunCompile.Arith.wasm op), .refI31] ++ rest)) Q := by
  obtain ⟨z, hz, hzw⟩ := arith_wasm op x y
  have hrep : Rep p.table μ₂ s₂ (.int (op.eval x y)) (.ref (.i31 (z.setWidth 31))) := by
    show Val.ref (.i31 (z.setWidth 31)) = .ref (.i31 (op.eval x y))
    rw [hzw]
  rw [vals_pair]
  exact Wp.intBinOp (m := .total) hz (twp_box (hk μ₂ s₂ f₂ _ hμ hs hf hh hrep))

theorem twp_cmpTail {d : Nat} {μ μ₂ : List Nat} {s s₂ : Store Nat} {f f₂ : Frame} {op : Cmp}
    {x y : BitVec 31} {σ' : Heap} {us : List Val} {rest : List Admin} {Q : Post Nat}
    (hk : Cont P host p.table d μ s f (.bool (op.eval x y)) σ' us rest Q)
    (hμ : μ <+: μ₂) (hs : Ext s s₂) (hf : Agree d f f₂) (hh : HeapRep p.table μ₂ s₂ σ') :
    TWP P host s₂ f₂ (vals ((us ++ [.i32 (x.setWidth 32)]) ++ [.i32 (y.setWidth 32)]) ++
      (expression [.intRelOp .i32 (FunCompile.Cmp.wasm op), .refI31] ++ rest)) Q := by
  have hrep : Rep p.table μ₂ s₂ (.bool (op.eval x y))
      (.ref (.i31 ((Numerics.intRelOp .i32 (FunCompile.Cmp.wasm op) (x.setWidth 32)
        (y.setWidth 32)).setWidth 31))) := by
    show Val.ref (.i31 _) = .ref (.i31 (if op.eval x y then 1 else 0))
    rw [cmp_wasm, bool32_31]
  rw [vals_pair]
  exact Wp.intRelOp (m := .total) (twp_box (hk μ₂ s₂ f₂ _ hμ hs hf hh hrep))

theorem spec_arith {k d : Nat} {op : Arith} {a b : Tm} (ha : Spec P host p k d a)
    (hb : Spec P host p k d b) : Spec P host p (k + 1) d (.arith op a b) := by
  intro σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us rest Q hk
  obtain ⟨x, σ₁, y, hxa, hyb, rfl⟩ := eval_arith_inv hv
  show TWP P host s f (vals us ++ (expression (compile p.table d a ++ unbox ++
    compile p.table d b ++ unbox ++ [.intBinOp .i32 (FunCompile.Arith.wasm op), .refI31]) ++
    rest)) Q
  simp only [List.append_assoc, expr_append]
  refine ha σ ρ _ σ₁ hxa μ s f hf hfn (depth_left hd) hr hh (sub_left hfx) us _ Q
    (Cont.unboxInt fun μ₁ s₁ f₁ hμ₁ hs₁ hf₁ hh₁ => ?_)
  have hdb : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  refine hb σ₁ ρ _ σ' hyb μ₁ s₁ f₁ (hf.of_agree hf₁) (hs₁.funcs hfn) hdb
    (hr.of_agree hμ₁ hs₁.1 hf₁) hh₁ (sub_right hfx) _ _ Q
    (Cont.unboxInt fun μ₂ s₂ f₂ hμ₂ hs₂ hf₂ hh₂ => ?_)
  exact twp_arithTail hk (hμ₁.trans hμ₂) (hs₁.trans hs₂) (hf₁.trans hf₂) hh₂

theorem spec_cmp {k d : Nat} {op : Cmp} {a b : Tm} (ha : Spec P host p k d a)
    (hb : Spec P host p k d b) : Spec P host p (k + 1) d (.cmp op a b) := by
  intro σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us rest Q hk
  obtain ⟨x, σ₁, y, hxa, hyb, rfl⟩ := eval_cmp_inv hv
  show TWP P host s f (vals us ++ (expression (compile p.table d a ++ unbox ++
    compile p.table d b ++ unbox ++ [.intRelOp .i32 (FunCompile.Cmp.wasm op), .refI31]) ++
    rest)) Q
  simp only [List.append_assoc, expr_append]
  refine ha σ ρ _ σ₁ hxa μ s f hf hfn (depth_left hd) hr hh (sub_left hfx) us _ Q
    (Cont.unboxInt fun μ₁ s₁ f₁ hμ₁ hs₁ hf₁ hh₁ => ?_)
  have hdb : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  refine hb σ₁ ρ _ σ' hyb μ₁ s₁ f₁ (hf.of_agree hf₁) (hs₁.funcs hfn) hdb
    (hr.of_agree hμ₁ hs₁.1 hf₁) hh₁ (sub_right hfx) _ _ Q
    (Cont.unboxInt fun μ₂ s₂ f₂ hμ₂ hs₂ hf₂ hh₂ => ?_)
  exact twp_cmpTail hk (hμ₁.trans hμ₂) (hs₁.trans hs₂) (hf₁.trans hf₂) hh₂

/-! ## Blocks -/

/-- The code of a term inside a block of result `anyref`. -/
theorem twp_inBlock {k d : Nat} {e : Tm} (hsp : Spec P host p k d e) {σ σ' : Heap}
    {ρ : List FunRefClo.Val} {v : FunRefClo.Val} (hv : eval k σ ρ e = some (v, σ'))
    {μ : List Nat} {s : Store Nat} {f : Frame} (hf : FOK f)
    (hfn : s.funcs[1]? = some (applyInst p)) (hd : d + e.depth < f.locals.length)
    (hr : EnvRep p.table μ s f d ρ) (hh : HeapRep p.table μ s σ)
    (hfx : ∀ x ∈ e.fixes d, x ∈ p.table) {us : List Val} {rest : List Admin} {Q : Post Nat}
    (hk : Cont P host p.table d μ s f v σ' us rest Q) :
    TWP P host s f (vals [] ++ expression (compile p.table d e))
      (labelPostT P host 1 [] us (seqPostT P host rest Q)) := by
  have h' := hsp σ ρ v σ' hv μ s f hf hfn hd hr hh hfx [] []
    (labelPostT P host 1 [] us (seqPostT P host rest Q))
    fun μ' s' f' w hμ hs hag hh' hw =>
      Wp.of_vals (m := .total) (vs := [w]) (hk μ' s' f' w hμ hs hag hh' hw)
  simpa using h'

theorem spec_ite {k d : Nat} {c t e : Tm} (hc : Spec P host p k d c) (ht : Spec P host p k d t)
    (he : Spec P host p k d e) : Spec P host p (k + 1) d (.ite c t e) := by
  intro σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us rest Q hk
  obtain ⟨b, σ₁, hcb, hbr⟩ := eval_ite_inv hv
  have hfx' : ∀ x ∈ c.fixes d ++ t.fixes d ++ e.fixes d, x ∈ p.table := hfx
  have hsp : Spec P host p k d (if b then t else e) := by cases b; exacts [he, ht]
  have hdb : d + (if b then t else e).depth < f.locals.length := by
    cases b
    · exact depth_right (depth_right hd)
    · exact depth_left (depth_right hd)
  have hfb : ∀ x ∈ (if b then t else e).fixes d, x ∈ p.table := by
    cases b
    · exact sub_right hfx'
    · exact sub_right (sub_left hfx')
  have hsel : (if (if b then (1 : BitVec 31) else 0).setWidth 32 ≠ 0 then compile p.table d t
      else compile p.table d e) = compile p.table d (if b then t else e) := by cases b <;> rfl
  show TWP P host s f (vals us ++ (expression (compile p.table d c ++ unbox ++
    [.if_ (.value anyref) (compile p.table d t) (compile p.table d e)]) ++ rest)) Q
  simp only [List.append_assoc, expr_append]
  refine hc σ ρ _ σ₁ hcb μ s f hf hfn (depth_left hd) hr hh (sub_left (sub_left hfx')) us _ Q
    (Cont.unboxBool fun μ₁ s₁ f₁ hμ₁ hs₁ hf₁ hh₁ => ?_)
  refine twp_ifBlock ?_
  rw [hsel]
  exact twp_inBlock hsp hbr (hf.of_agree hf₁) (hs₁.funcs hfn) (hf₁.2.1 ▸ hdb)
    (hr.of_agree hμ₁ hs₁.1 hf₁) hh₁ hfb (hk.later hμ₁ hs₁ hf₁)

/-! ## Binders -/

theorem spec_let {k d : Nat} {a b : Tm} (ha : Spec P host p k d a)
    (hb : Spec P host p k (d + 1) b) : Spec P host p (k + 1) d (.let_ a b) := by
  intro σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us rest Q hk
  obtain ⟨u, σ₁, hu, hbv⟩ := eval_let_inv hv
  have hfx' : ∀ x ∈ a.fixes d ++ b.fixes (d + 1), x ∈ p.table := hfx
  have hdb : d + 1 + b.depth < f.locals.length := depth_succ (depth_right hd)
  have hlt : d + 1 < f.locals.length := by omega
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.1 hlt
  show TWP P host s f (vals us ++ (expression (compile p.table d a ++
    .localSet (lx (d + 1)) :: compile p.table (d + 1) b) ++ rest)) Q
  rw [expr_append]
  refine ha σ ρ u σ₁ hu μ s f hf hfn (depth_left hd) hr hh (sub_left hfx') us _ Q
    fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
  refine twp_localSet (hf.of_agree hf₁).1 hlt₁ ?_
  refine hb σ₁ (u :: ρ) v σ' hbv μ₁ s₁ _ ((hf.of_agree hf₁).setLocal _ w) (hs₁.funcs hfn)
    (by rw [len_setLocal, hf₁.2.1]; exact hdb) ((hr.of_agree hμ₁ hs₁.1 hf₁).cons hw hlt₁ hlim)
    hh₁ (sub_right hfx') us rest Q fun μ₂ s₂ f₂ w₂ hμ₂ hs₂ hf₂ hh₂ hw₂ => ?_
  exact hk μ₂ s₂ f₂ w₂ (hμ₁.trans hμ₂) (hs₁.trans hs₂)
    (hf₁.trans ((Agree.setLocal w hlim).trans hf₂.of_succ)) hh₂ hw₂

/-! ## Pairs and injections -/

theorem spec_pair {k d : Nat} {a b : Tm} (ha : Spec P host p k d a)
    (hb : Spec P host p k d b) : Spec P host p (k + 1) d (.pair a b) := by
  intro σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us rest Q hk
  obtain ⟨x, σ₁, y, hxa, hyb, rfl⟩ := eval_pair_inv hv
  show TWP P host s f (vals us ++ (expression (compile p.table d a ++ compile p.table d b ++
    [.structNew boxIdx]) ++ rest)) Q
  simp only [List.append_assoc, expr_append]
  refine ha σ ρ _ σ₁ hxa μ s f hf hfn (depth_left hd) hr hh (sub_left hfx) us _ Q
    fun μ₁ s₁ f₁ wa hμ₁ hs₁ hf₁ hh₁ hwa => ?_
  have hdb : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  refine hb σ₁ ρ _ σ' hyb μ₁ s₁ f₁ (hf.of_agree hf₁) (hs₁.funcs hfn) hdb
    (hr.of_agree hμ₁ hs₁.1 hf₁) hh₁ (sub_right hfx) _ _ Q
    fun μ₂ s₂ f₂ wb hμ₂ hs₂ hf₂ hh₂ hwb => ?_
  rw [vals_pair]
  refine twp_newBox (hf.of_agree (hf₁.trans hf₂)).1 ?_
  have hp := addStruct_prefix s₂ ⟨dBox, [.val wa, .val wb]⟩
  have hbx : BoxExt s₂ (s₂.addStruct ⟨dBox, [.val wa, .val wb]⟩) :=
    Silmaril.Proofs.Wasm.Models.FunRefCompile.BoxExt.of_prefix hp
  exact hk μ₂ _ f₂ _ (hμ₁.trans hμ₂) ((hs₁.trans hs₂).trans (Ext.addStruct _ _))
    (hf₁.trans hf₂) (hh₂.prefix hp)
    ⟨s₂.structs.length, wa, wb, rfl, addStruct_get _ _,
      (hwa.mono hμ₂ hs₂.1).mono (List.prefix_refl _) hbx, hwb.mono (List.prefix_refl _) hbx⟩

theorem spec_fst {k d : Nat} {e : Tm} (he : Spec P host p k d e) :
    Spec P host p (k + 1) d (.fst e) := by
  intro σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us rest Q hk
  obtain ⟨y, hev⟩ := eval_fst_inv hv
  show TWP P host s f (vals us ++ (expression (compile p.table d e ++
    [.refCast boxRef, .structGet none boxIdx (fx 0)]) ++ rest)) Q
  rw [expr_append]
  refine he σ ρ _ σ' hev μ s f hf hfn hd hr hh hfx us _ Q
    fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  obtain ⟨addr, wa, wb, hw', hst, hwa, -⟩ := hw
  rw [hw']
  have hf₁' : FrameOK f₁ := (hf.of_agree hf₁).1
  exact twp_castBox hf₁' hst (twp_getBox hf₁' (by omega) hst
    (hk μ₁ s₁ f₁ wa hμ₁ hs₁ hf₁ hh₁ hwa))

theorem spec_snd {k d : Nat} {e : Tm} (he : Spec P host p k d e) :
    Spec P host p (k + 1) d (.snd e) := by
  intro σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us rest Q hk
  obtain ⟨x, hev⟩ := eval_snd_inv hv
  show TWP P host s f (vals us ++ (expression (compile p.table d e ++
    [.refCast boxRef, .structGet none boxIdx (fx 1)]) ++ rest)) Q
  rw [expr_append]
  refine he σ ρ _ σ' hev μ s f hf hfn hd hr hh hfx us _ Q
    fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  obtain ⟨addr, wa, wb, hw', hst, -, hwb⟩ := hw
  rw [hw']
  have hf₁' : FrameOK f₁ := (hf.of_agree hf₁).1
  exact twp_castBox hf₁' hst (twp_getBox hf₁' (by omega) hst
    (hk μ₁ s₁ f₁ wb hμ₁ hs₁ hf₁ hh₁ hwb))

/-- The value of an injection with tag `0` (`inl`) or `1` (`inr`). -/
def inj (tag : BitVec 31) (u : FunRefClo.Val) : FunRefClo.Val :=
  if tag = 0 then .inl u else .inr u

theorem rep_inj {μ : List Nat} {s : Store Nat} {tag : BitVec 31} (ht : tag = 0 ∨ tag = 1)
    {u : FunRefClo.Val} {wv : Val} {addr : Nat}
    (hst : s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 tag)), .val wv]⟩)
    (hu : Rep p.table μ s u wv) : Rep p.table μ s (inj tag u) (.ref (.struct addr)) := by
  rcases ht with rfl | rfl
  · exact ⟨addr, wv, rfl, hst, hu⟩
  · exact ⟨addr, wv, rfl, hst, hu⟩

theorem spec_injTag {k d : Nat} {e : Tm} {tag : BitVec 31} (ht : tag = 0 ∨ tag = 1)
    (he : Spec P host p k d e) {σ σ' : Heap} {ρ : List FunRefClo.Val} {u : FunRefClo.Val}
    (hev : eval k σ ρ e = some (u, σ')) {μ : List Nat} {s : Store Nat} {f : Frame} (hf : FOK f)
    (hfn : s.funcs[1]? = some (applyInst p)) (hd : d + e.depth < f.locals.length)
    (hr : EnvRep p.table μ s f d ρ) (hh : HeapRep p.table μ s σ)
    (hfx : ∀ x ∈ e.fixes d, x ∈ p.table) {us : List Val} {rest : List Admin} {Q : Post Nat}
    (hk : Cont P host p.table d μ s f (inj tag u) σ' us rest Q) :
    TWP P host s f (vals us ++ (expression (.intConst .i32 (tag.setWidth 32) :: .refI31 ::
      compile p.table d e ++ [.structNew boxIdx]) ++ rest)) Q := by
  show TWP P host s f (vals us ++ (expression [.intConst .i32 (tag.setWidth 32), .refI31] ++
    (expression (compile p.table d e ++ [.structNew boxIdx]) ++ rest))) Q
  refine twp_constBox ?_
  rw [expr_append, setWidth_31_32]
  refine he σ ρ u σ' hev μ s f hf hfn hd hr hh hfx _ _ Q
    fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  rw [vals_pair]
  refine twp_newBox (hf.of_agree hf₁).1 ?_
  have hp := addStruct_prefix s₁ ⟨dBox, [.val (.ref (.i31 tag)), .val w]⟩
  have hbx := Silmaril.Proofs.Wasm.Models.FunRefCompile.BoxExt.of_prefix hp
  exact hk μ₁ _ f₁ _ hμ₁ (hs₁.trans (Ext.addStruct _ _)) hf₁ (hh₁.prefix hp)
    (rep_inj ht (addStruct_get _ _) (hw.mono (List.prefix_refl _) hbx))

theorem spec_inl {k d : Nat} {e : Tm} (he : Spec P host p k d e) :
    Spec P host p (k + 1) d (.inl e) := by
  intro σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us rest Q hk
  obtain ⟨u, hev, rfl⟩ := eval_inl_inv hv
  exact spec_injTag (tag := 0) (.inl rfl) he hev hf hfn hd hr hh hfx hk

theorem spec_inr {k d : Nat} {e : Tm} (he : Spec P host p k d e) :
    Spec P host p (k + 1) d (.inr e) := by
  intro σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us rest Q hk
  obtain ⟨u, hev, rfl⟩ := eval_inr_inv hv
  exact spec_injTag (tag := 1) (.inr rfl) he hev hf hfn hd hr hh hfx hk

/-! ## `case` -/

/-- The code of a `case` branch. -/
def branch (L : List (Nat × Tm)) (d : Nat) (t : Tm) : List Instr :=
  getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile L (d + 1) t

theorem twp_branch {k d : Nat} {t : Tm} (hsp : Spec P host p k (d + 1) t) {σ σ' : Heap}
    {ρ : List FunRefClo.Val} {u v : FunRefClo.Val} (hev : eval k σ (u :: ρ) t = some (v, σ'))
    {μ : List Nat} {s : Store Nat} {f : Frame} (hf : FOK f)
    (hfn : s.funcs[1]? = some (applyInst p)) (hd : d + 1 + t.depth < f.locals.length)
    (hr : EnvRep p.table μ s f d ρ) (hh : HeapRep p.table μ s σ)
    (hfx : ∀ x ∈ t.fixes (d + 1), x ∈ p.table) {addr : Nat} {tagw wv : Val}
    (hloc : f.locals[d + 1]? = some (some (.ref (.struct addr))))
    (hst : s.structs[addr]? = some ⟨dBox, [.val tagw, .val wv]⟩) (hu : Rep p.table μ s u wv)
    {us : List Val} {rest : List Admin} {Q : Post Nat}
    (hk : Cont P host p.table d μ s f v σ' us rest Q) :
    TWP P host s f (vals [] ++ expression (branch p.table d t))
      (labelPostT P host 1 [] us (seqPostT P host rest Q)) := by
  have hlt : d + 1 < f.locals.length := by omega
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.1 hlt
  show TWP P host s f (vals [] ++ .plain (.localGet (lx (d + 1))) :: .plain (.refCast boxRef) ::
    .plain (.structGet none boxIdx (fx 1)) :: .plain (.localSet (lx (d + 1))) ::
    expression (compile p.table (d + 1) t)) _
  refine twp_localGet hf.1 hloc (twp_castBox hf.1 hst (twp_getBox hf.1 (by omega) hst
    (twp_localSet (w := wv) hf.1 hlt ?_)))
  have hk' : Cont P host p.table (d + 1) μ s (f.setLocal (lx (d + 1)) wv) v σ' [] []
      (labelPostT P host 1 [] us (seqPostT P host rest Q)) :=
    fun μ' s' f' w hμ hs hag hh' hw => Wp.of_vals (m := .total) (vs := [w])
      (hk μ' s' f' w hμ hs ((Agree.setLocal wv hlim).trans hag.of_succ) hh' hw)
  have h' := hsp σ (u :: ρ) v σ' hev μ s _ (hf.setLocal _ wv) hfn
    (by rw [len_setLocal]; exact hd) (hr.cons hu hlt hlim) hh hfx [] [] _ hk'
  simpa using h'

/-- A `case` whose scrutinee returns a `$box` with tag `tag`, which selects the branch `t`. -/
theorem spec_caseArm {k d : Nat} {e l r t : Tm} {tag : BitVec 31}
    (he : Spec P host p k d e) (ht : Spec P host p k (d + 1) t)
    (hsel : (if tag.setWidth 32 ≠ 0 then branch p.table d r else branch p.table d l) =
      branch p.table d t)
    {σ σ₁ σ' : Heap} {ρ : List FunRefClo.Val} {u v w₀ : FunRefClo.Val}
    (hev : eval k σ ρ e = some (w₀, σ₁))
    (hrep : ∀ μ s w, Rep p.table μ s w₀ w → ∃ addr wv, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 tag)), .val wv]⟩ ∧ Rep p.table μ s u wv)
    (hbv : eval k σ₁ (u :: ρ) t = some (v, σ')) {μ : List Nat} {s : Store Nat} {f : Frame}
    (hf : FOK f) (hfn : s.funcs[1]? = some (applyInst p)) (hde : d + e.depth < f.locals.length)
    (hdt : d + 1 + t.depth < f.locals.length) (hr : EnvRep p.table μ s f d ρ)
    (hh : HeapRep p.table μ s σ) (hfxe : ∀ x ∈ e.fixes d, x ∈ p.table)
    (hfxt : ∀ x ∈ t.fixes (d + 1), x ∈ p.table) {us : List Val} {rest : List Admin}
    {Q : Post Nat} (hk : Cont P host p.table d μ s f v σ' us rest Q) :
    TWP P host s f (vals us ++ (expression (compile p.table d e) ++
      (expression (.localSet (lx (d + 1)) :: getField (d + 1) 0 ++ unbox ++
        [.if_ (.value anyref) (branch p.table d r) (branch p.table d l)]) ++ rest))) Q := by
  refine he σ ρ _ σ₁ hev μ s f hf hfn hde hr hh hfxe us _ Q
    fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  obtain ⟨addr, wv, hw', hst, hu⟩ := hrep μ₁ s₁ w hw
  have hf₁' : FOK f₁ := hf.of_agree hf₁
  have hlt : d + 1 < f.locals.length := by omega
  have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.1 hlt
  rw [hw']
  refine twp_caseTail hf₁'.1 hlt₁ hst ?_
  rw [hsel]
  exact twp_branch ht hbv (hf₁'.setLocal _ _) (hs₁.funcs hfn)
    (by rw [len_setLocal, hf₁.2.1]; exact hdt)
    ((hr.of_agree hμ₁ hs₁.1 hf₁).of_agree (List.prefix_refl _)
      (Silmaril.Proofs.Wasm.Models.FunRefCompile.BoxExt.refl _) (Agree.setLocal _ hlim))
    hh₁ hfxt (setLocal_get _ hlt₁ hlim) hst hu
    ((hk.later hμ₁ hs₁ hf₁).later (List.prefix_refl _) (Ext.refl _) (Agree.setLocal _ hlim))

theorem spec_case {k d : Nat} {e l r : Tm} (he : Spec P host p k d e)
    (hl : Spec P host p k (d + 1) l) (hr' : Spec P host p k (d + 1) r) :
    Spec P host p (k + 1) d (.case e l r) := by
  intro σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us rest Q hk
  have hfx' : ∀ x ∈ e.fixes d ++ l.fixes (d + 1) ++ r.fixes (d + 1), x ∈ p.table := hfx
  have hdlr : d + 1 + max l.depth r.depth < f.locals.length := depth_succ (depth_right hd)
  show TWP P host s f (vals us ++ (expression (compile p.table d e ++ .localSet (lx (d + 1)) ::
    getField (d + 1) 0 ++ unbox ++ [.if_ (.value anyref) (branch p.table d r)
      (branch p.table d l)]) ++ rest)) Q
  simp only [List.append_assoc]
  rw [expr_append]
  rcases eval_case_inv hv with ⟨u, σ₁, hev, hbv⟩ | ⟨u, σ₁, hev, hbv⟩
  · exact spec_caseArm (tag := 0) he hl rfl hev (fun _ _ _ hw => hw) hbv hf hfn (depth_left hd)
      (depth_left hdlr) hr hh (sub_left (sub_left hfx')) (sub_right (sub_left hfx')) hk
  · exact spec_caseArm (tag := 1) he hr' rfl hev (fun _ _ _ hw => hw) hbv hf hfn (depth_left hd)
      (depth_right hdlr) hr hh (sub_left (sub_left hfx')) (sub_right hfx') hk

/-! ## Cells -/

theorem spec_ref {k d : Nat} {e : Tm} (he : Spec P host p k d e) :
    Spec P host p (k + 1) d (.ref e) := by
  intro σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us rest Q hk
  obtain ⟨u, σ₁, hev, rfl, rfl⟩ := eval_ref_inv hv
  show TWP P host s f (vals us ++ (expression (compile p.table d e ++ [.structNew cellIdx]) ++
    rest)) Q
  rw [expr_append]
  refine he σ ρ u σ₁ hev μ s f hf hfn hd hr hh hfx us _ Q
    fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  refine twp_newCell (hf.of_agree hf₁) ?_
  have hloc : (μ₁ ++ [s₁.structs.length])[σ₁.length]? = some s₁.structs.length := by
    rw [← hh₁.1]; simp
  exact hk _ _ f₁ _ (hμ₁.trans (List.prefix_append _ _)) (hs₁.trans (Ext.addStruct _ _)) hf₁
    (hh₁.alloc hw) ⟨s₁.structs.length, hloc, rfl⟩

theorem spec_get {k d : Nat} {e : Tm} (he : Spec P host p k d e) :
    Spec P host p (k + 1) d (.get e) := by
  intro σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us rest Q hk
  obtain ⟨l, hev, hl⟩ := eval_get_inv hv
  show TWP P host s f (vals us ++ (expression (compile p.table d e ++
    [.refCast cellRef, .structGet none cellIdx (fx 0)]) ++ rest)) Q
  rw [expr_append]
  refine he σ ρ _ σ' hev μ s f hf hfn hd hr hh hfx us _ Q
    fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  obtain ⟨addr, hμl, rfl⟩ := hw
  obtain ⟨u, w', hu, hst, hrep⟩ := hh₁.cell hμl
  have huv : u = v := Option.some.inj (hu.symm.trans hl)
  have hf₁' : FOK f₁ := hf.of_agree hf₁
  exact twp_castCell hf₁' hst (twp_getCell hf₁' hst
    (hk μ₁ s₁ f₁ w' hμ₁ hs₁ hf₁ hh₁ (huv ▸ hrep)))

theorem twp_setTail {d : Nat} {μ μ₂ : List Nat} {s s₂ : Store Nat} {f f₂ : Frame}
    (hf₂ : FOK f₂) {l addr : Nat} {u : FunRefClo.Val} {σ₂ : Heap} {wb : Val} {us : List Val}
    {rest : List Admin} {Q : Post Nat}
    (hk : Cont P host p.table d μ s f (.bool true) (σ₂.set l u) us rest Q) (hμ : μ <+: μ₂)
    (hs : Ext s s₂) (hag : Agree d f f₂) (hh₂ : HeapRep p.table μ₂ s₂ σ₂)
    (hμl : μ₂[l]? = some addr) (hwb : Rep p.table μ₂ s₂ u wb) :
    TWP P host s₂ f₂ (vals ((us ++ [.ref (.struct addr)]) ++ [wb]) ++
      (expression [.structSet cellIdx (fx 0), .intConst .i32 1, .refI31] ++ rest)) Q := by
  obtain ⟨_, w₀, -, hst, -⟩ := hh₂.cell hμl
  rw [vals_pair]
  refine twp_setCell hf₂ hst ?_
  have hrep : Rep p.table μ₂ (s₂.setStructField addr 0 (.val wb)) (.bool true)
      (.ref (.i31 ((1 : BitVec 32).setWidth 31))) := rfl
  exact twp_constBox (hk μ₂ _ f₂ _ hμ (hs.trans (Ext.setCell hst 0 _)) hag (hh₂.set hμl hwb) hrep)

theorem spec_set {k d : Nat} {a b : Tm} (ha : Spec P host p k d a) (hb : Spec P host p k d b) :
    Spec P host p (k + 1) d (.set a b) := by
  intro σ ρ v σ' hv μ s f hf hfn hd hr hh hfx us rest Q hk
  obtain ⟨l, σ₁, u, σ₂, hea, heb, -, rfl, rfl⟩ := eval_set_inv hv
  show TWP P host s f (vals us ++ (expression (compile p.table d a ++ .refCast cellRef ::
    compile p.table d b ++ [.structSet cellIdx (fx 0), .intConst .i32 1, .refI31]) ++ rest)) Q
  simp only [List.append_assoc, List.cons_append]
  rw [expr_append]
  refine ha σ ρ _ σ₁ hea μ s f hf hfn (depth_left hd) hr hh (sub_left hfx) us _ Q
    fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  obtain ⟨addr, hμl, rfl⟩ := hw
  obtain ⟨_, _, -, hst₁, -⟩ := hh₁.cell hμl
  refine twp_castCell (hf.of_agree hf₁) hst₁ ?_
  show TWP P host s₁ f₁ (vals (us ++ [.ref (.struct addr)]) ++ (expression (compile p.table d b ++
    [.structSet cellIdx (fx 0), .intConst .i32 1, .refI31]) ++ rest)) Q
  rw [expr_append]
  refine hb σ₁ ρ u σ₂ heb μ₁ s₁ f₁ (hf.of_agree hf₁) (hs₁.funcs hfn)
    (by rw [hf₁.2.1]; exact depth_right hd) (hr.of_agree hμ₁ hs₁.1 hf₁) hh₁ (sub_right hfx) _ _ Q
    fun μ₂ s₂ f₂ wb hμ₂ hs₂ hf₂ hh₂ hwb => ?_
  exact twp_setTail (hf.of_agree (hf₁.trans hf₂)) hk (hμ₁.trans hμ₂) (hs₁.trans hs₂)
    (hf₁.trans hf₂) hh₂ (getElem?_of_prefix hμ₂ hμl) hwb

end Silmaril.Proofs.Wasm.Models.FunRefCloCompile
