module

public import Silmaril.Proofs.Wasm.Models.FunRefCompile.Rep

/-!
# Compiling FunRef: correctness of the code of each construct

`Spec P host d e` for every constructor, threading the heap and its cells, and
**`spec_compile`** by induction on terms. The FunLang constructs follow
`Silmaril.Proofs.Wasm.Models.FunCompile.Cases`; the new ones are `spec_ref`, `spec_get`, `spec_set`.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunRefCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunRefCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunRef (Tm eval Heap)
open Silmaril.Wasm.Models.FunLang (Arith Cmp)
open Silmaril.Wasm.Models.FunCompile (dBox dMain boxIdx boxRef lx fx unbox getField anyref)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree getElem?_of_prefix expr_append twp_unbox
  twp_box twp_castBox twp_getBox twp_newBox twp_localGet twp_localSet addStruct_get
  addStruct_prefix setWidth_31_32 arith_wasm cmp_wasm bool32_31 depth_left depth_right depth_succ
  twp_constBox len_setLocal setLocal_get lt_lim vals_pair twp_ifBlock twp_caseTail)
open Silmaril.Wasm.Logic.Core (Post)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Inversion of evaluation -/

theorem eval_var_inv {σ : Heap} {ρ : List FunRef.Val} {i : Nat} {v : FunRef.Val} {σ' : Heap}
    (h : eval σ ρ (.var i) = some (v, σ')) : ρ[i]? = some v ∧ σ' = σ := by
  simp only [eval, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨u, hu, rfl, rfl⟩ := h
  exact ⟨hu, rfl⟩

theorem eval_arith_inv {σ σ' : Heap} {ρ : List FunRef.Val} {op : Arith} {a b : Tm}
    {v : FunRef.Val} (h : eval σ ρ (.arith op a b) = some (v, σ')) :
    ∃ x σ₁ y, eval σ ρ a = some (.int x, σ₁) ∧ eval σ₁ ρ b = some (.int y, σ') ∧
      v = .int (op.eval x y) := by
  simp only [eval] at h
  split at h
  · next x σ₁ ha =>
    split at h
    · next y σ₂ hb =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨x, σ₁, y, ha, hb, rfl⟩
    · cases h
  · cases h

theorem eval_cmp_inv {σ σ' : Heap} {ρ : List FunRef.Val} {op : Cmp} {a b : Tm}
    {v : FunRef.Val} (h : eval σ ρ (.cmp op a b) = some (v, σ')) :
    ∃ x σ₁ y, eval σ ρ a = some (.int x, σ₁) ∧ eval σ₁ ρ b = some (.int y, σ') ∧
      v = .bool (op.eval x y) := by
  simp only [eval] at h
  split at h
  · next x σ₁ ha =>
    split at h
    · next y σ₂ hb =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨x, σ₁, y, ha, hb, rfl⟩
    · cases h
  · cases h

theorem eval_ite_inv {σ σ' : Heap} {ρ : List FunRef.Val} {c t e : Tm} {v : FunRef.Val}
    (h : eval σ ρ (.ite c t e) = some (v, σ')) :
    ∃ b σ₁, eval σ ρ c = some (.bool b, σ₁) ∧ eval σ₁ ρ (if b then t else e) = some (v, σ') := by
  simp only [eval] at h
  split at h
  · next σ₁ hc => exact ⟨true, σ₁, hc, h⟩
  · next σ₁ hc => exact ⟨false, σ₁, hc, h⟩
  · cases h

theorem eval_let_inv {σ σ' : Heap} {ρ : List FunRef.Val} {a b : Tm} {v : FunRef.Val}
    (h : eval σ ρ (.let_ a b) = some (v, σ')) :
    ∃ u σ₁, eval σ ρ a = some (u, σ₁) ∧ eval σ₁ (u :: ρ) b = some (v, σ') := by
  simp only [eval] at h
  split at h
  · next u σ₁ hu => exact ⟨u, σ₁, hu, h⟩
  · cases h

theorem eval_pair_inv {σ σ' : Heap} {ρ : List FunRef.Val} {a b : Tm} {v : FunRef.Val}
    (h : eval σ ρ (.pair a b) = some (v, σ')) :
    ∃ x σ₁ y, eval σ ρ a = some (x, σ₁) ∧ eval σ₁ ρ b = some (y, σ') ∧ v = .pair x y := by
  simp only [eval] at h
  split at h
  · next x σ₁ ha =>
    split at h
    · next y σ₂ hb =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨x, σ₁, y, ha, hb, rfl⟩
    · cases h
  · cases h

theorem eval_fst_inv {σ σ' : Heap} {ρ : List FunRef.Val} {e : Tm} {v : FunRef.Val}
    (h : eval σ ρ (.fst e) = some (v, σ')) : ∃ y, eval σ ρ e = some (.pair v y, σ') := by
  simp only [eval] at h
  split at h
  · next x y σ₁ he =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨y, he⟩
  · cases h

theorem eval_snd_inv {σ σ' : Heap} {ρ : List FunRef.Val} {e : Tm} {v : FunRef.Val}
    (h : eval σ ρ (.snd e) = some (v, σ')) : ∃ x, eval σ ρ e = some (.pair x v, σ') := by
  simp only [eval] at h
  split at h
  · next x y σ₁ he =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨x, he⟩
  · cases h

theorem eval_inl_inv {σ σ' : Heap} {ρ : List FunRef.Val} {e : Tm} {v : FunRef.Val}
    (h : eval σ ρ (.inl e) = some (v, σ')) : ∃ u, eval σ ρ e = some (u, σ') ∧ v = .inl u := by
  simp only [eval, Option.map_eq_some_iff] at h
  obtain ⟨⟨u, σ₁⟩, hu, he⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact ⟨u, hu, rfl⟩

theorem eval_inr_inv {σ σ' : Heap} {ρ : List FunRef.Val} {e : Tm} {v : FunRef.Val}
    (h : eval σ ρ (.inr e) = some (v, σ')) : ∃ u, eval σ ρ e = some (u, σ') ∧ v = .inr u := by
  simp only [eval, Option.map_eq_some_iff] at h
  obtain ⟨⟨u, σ₁⟩, hu, he⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact ⟨u, hu, rfl⟩

theorem eval_case_inv {σ σ' : Heap} {ρ : List FunRef.Val} {e l r : Tm} {v : FunRef.Val}
    (h : eval σ ρ (.case e l r) = some (v, σ')) :
    (∃ u σ₁, eval σ ρ e = some (.inl u, σ₁) ∧ eval σ₁ (u :: ρ) l = some (v, σ')) ∨
      (∃ u σ₁, eval σ ρ e = some (.inr u, σ₁) ∧ eval σ₁ (u :: ρ) r = some (v, σ')) := by
  simp only [eval] at h
  split at h
  · next u σ₁ hu => exact .inl ⟨u, σ₁, hu, h⟩
  · next u σ₁ hu => exact .inr ⟨u, σ₁, hu, h⟩
  · cases h

theorem eval_ref_inv {σ σ' : Heap} {ρ : List FunRef.Val} {e : Tm} {v : FunRef.Val}
    (h : eval σ ρ (.ref e) = some (v, σ')) :
    ∃ u σ₁, eval σ ρ e = some (u, σ₁) ∧ v = .loc σ₁.length ∧ σ' = σ₁ ++ [u] := by
  simp only [eval] at h
  split at h
  · next u σ₁ hu =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨u, σ₁, hu, rfl, rfl⟩
  · cases h

theorem eval_get_inv {σ σ' : Heap} {ρ : List FunRef.Val} {e : Tm} {v : FunRef.Val}
    (h : eval σ ρ (.get e) = some (v, σ')) :
    ∃ l, eval σ ρ e = some (.loc l, σ') ∧ σ'[l]? = some v := by
  simp only [eval] at h
  split at h
  · next l σ₁ he =>
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨u, hu, rfl, rfl⟩ := h
    exact ⟨l, he, hu⟩
  · cases h

theorem eval_set_inv {σ σ' : Heap} {ρ : List FunRef.Val} {a b : Tm} {v : FunRef.Val}
    (h : eval σ ρ (.set a b) = some (v, σ')) :
    ∃ l σ₁ u σ₂, eval σ ρ a = some (.loc l, σ₁) ∧ eval σ₁ ρ b = some (u, σ₂) ∧
      v = .bool true ∧ σ' = σ₂.set l u := by
  simp only [eval] at h
  split at h
  · next l σ₁ ha =>
    split at h
    · next u σ₂ hb =>
      split at h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨l, σ₁, u, σ₂, ha, hb, rfl, rfl⟩
      · cases h
    · cases h
  · cases h

/-! ## Continuations through unboxing -/

theorem Cont.unboxInt {d : Nat} {μ : List Nat} {s : Store H} {f : Frame} {x : BitVec 31}
    {σ' : Heap} {us : List Val} {rest : List Admin} {Q : Post H}
    (h : ∀ μ' s' f', μ <+: μ' → BoxExt s s' → Agree d f f' → HeapRep μ' s' σ' →
      TWP P host s' f' (vals (us ++ [.i32 (x.setWidth 32)]) ++ rest) Q) :
    Cont P host d μ s f (.int x) σ' us (expression unbox ++ rest) Q := by
  intro μ' s' f' w hμ hs hf hh hw
  have hw' : w = .ref (.i31 x) := hw
  rw [hw']
  exact twp_unbox (h μ' s' f' hμ hs hf hh)

theorem Cont.unboxBool {d : Nat} {μ : List Nat} {s : Store H} {f : Frame} {b : Bool}
    {σ' : Heap} {us : List Val} {rest : List Admin} {Q : Post H}
    (h : ∀ μ' s' f', μ <+: μ' → BoxExt s s' → Agree d f f' → HeapRep μ' s' σ' →
      TWP P host s' f' (vals (us ++ [.i32 ((if b then (1 : BitVec 31) else 0).setWidth 32)]) ++
        rest) Q) :
    Cont P host d μ s f (.bool b) σ' us (expression unbox ++ rest) Q := by
  intro μ' s' f' w hμ hs hf hh hw
  have hw' : w = .ref (.i31 (if b then 1 else 0)) := hw
  rw [hw']
  exact twp_unbox (h μ' s' f' hμ hs hf hh)

/-! ## Leaves -/

theorem spec_var (d i : Nat) : Spec (H := H) P host d (.var i) := by
  intro σ ρ v σ' hv μ s f hf _ hr hh us rest Q hk
  obtain ⟨hi, rfl⟩ := eval_var_inv hv
  obtain ⟨w, hw, hrep⟩ := hr.2 i v hi
  exact twp_localGet hf.ok hw
    (hk μ s f w (List.prefix_refl _) (BoxExt.refl s) (Agree.refl d f) hh hrep)

theorem spec_int (d : Nat) (n : BitVec 31) : Spec (H := H) P host d (.int n) := by
  intro σ ρ v σ' hv μ s f _ _ _ hh us rest Q hk
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
  have hw : Rep μ s (.int n) (.ref (.i31 ((n.setWidth 32).setWidth 31))) := by
    rw [setWidth_31_32]; rfl
  exact twp_constBox (hk μ s f _ (List.prefix_refl _) (BoxExt.refl s) (Agree.refl d f) hh hw)

theorem spec_bool (d : Nat) (b : Bool) : Spec (H := H) P host d (.bool b) := by
  intro σ ρ v σ' hv μ s f _ _ _ hh us rest Q hk
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
  have hw : Rep μ s (.bool b) (.ref (.i31 ((if b then (1 : BitVec 32) else 0).setWidth 31))) := by
    cases b <;> rfl
  exact twp_constBox (hk μ s f _ (List.prefix_refl _) (BoxExt.refl s) (Agree.refl d f) hh hw)

/-! ## Arithmetic and comparisons -/

theorem twp_arithTail {d : Nat} {μ μ₂ : List Nat} {s s₂ : Store H} {f f₂ : Frame} {op : Arith}
    {x y : BitVec 31} {σ' : Heap} {us : List Val} {rest : List Admin} {Q : Post H}
    (hk : Cont P host d μ s f (.int (op.eval x y)) σ' us rest Q) (hμ : μ <+: μ₂)
    (hs : BoxExt s s₂) (hf : Agree d f f₂) (hh : HeapRep μ₂ s₂ σ') :
    TWP P host s₂ f₂ (vals ((us ++ [.i32 (x.setWidth 32)]) ++ [.i32 (y.setWidth 32)]) ++
      (expression [.intBinOp .i32 (FunCompile.Arith.wasm op), .refI31] ++ rest)) Q := by
  obtain ⟨z, hz, hzw⟩ := arith_wasm op x y
  have hrep : Rep μ₂ s₂ (.int (op.eval x y)) (.ref (.i31 (z.setWidth 31))) := by
    show Val.ref (.i31 (z.setWidth 31)) = .ref (.i31 (op.eval x y))
    rw [hzw]
  rw [vals_pair]
  exact Wp.intBinOp (m := .total) hz (twp_box (hk μ₂ s₂ f₂ _ hμ hs hf hh hrep))

theorem twp_cmpTail {d : Nat} {μ μ₂ : List Nat} {s s₂ : Store H} {f f₂ : Frame} {op : Cmp}
    {x y : BitVec 31} {σ' : Heap} {us : List Val} {rest : List Admin} {Q : Post H}
    (hk : Cont P host d μ s f (.bool (op.eval x y)) σ' us rest Q) (hμ : μ <+: μ₂)
    (hs : BoxExt s s₂) (hf : Agree d f f₂) (hh : HeapRep μ₂ s₂ σ') :
    TWP P host s₂ f₂ (vals ((us ++ [.i32 (x.setWidth 32)]) ++ [.i32 (y.setWidth 32)]) ++
      (expression [.intRelOp .i32 (FunCompile.Cmp.wasm op), .refI31] ++ rest)) Q := by
  have hrep : Rep μ₂ s₂ (.bool (op.eval x y)) (.ref (.i31
      ((Numerics.intRelOp .i32 (FunCompile.Cmp.wasm op) (x.setWidth 32)
        (y.setWidth 32)).setWidth 31))) := by
    show Val.ref (.i31 _) = .ref (.i31 (if op.eval x y then 1 else 0))
    rw [cmp_wasm, bool32_31]
  rw [vals_pair]
  exact Wp.intRelOp (m := .total) (twp_box (hk μ₂ s₂ f₂ _ hμ hs hf hh hrep))

theorem spec_arith {d : Nat} {op : Arith} {a b : Tm} (ha : Spec P host d a)
    (hb : Spec P host d b) : Spec (H := H) P host d (.arith op a b) := by
  intro σ ρ v σ' hv μ s f hf hd hr hh us rest Q hk
  obtain ⟨x, σ₁, y, hxa, hyb, rfl⟩ := eval_arith_inv hv
  show TWP P host s f (vals us ++ (expression (compile d a ++ unbox ++ compile d b ++ unbox ++
    [.intBinOp .i32 (FunCompile.Arith.wasm op), .refI31]) ++ rest)) Q
  simp only [List.append_assoc, expr_append]
  refine ha σ ρ _ σ₁ hxa μ s f hf (depth_left hd) hr hh us _ Q
    (Cont.unboxInt fun μ₁ s₁ f₁ hμ₁ hs₁ hf₁ hh₁ => ?_)
  have hdb : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  refine hb σ₁ ρ _ σ' hyb μ₁ s₁ f₁ (hf.of_agree hf₁) hdb (hr.of_agree hμ₁ hs₁ hf₁) hh₁ _ _ Q
    (Cont.unboxInt fun μ₂ s₂ f₂ hμ₂ hs₂ hf₂ hh₂ => ?_)
  exact twp_arithTail hk (hμ₁.trans hμ₂) (hs₁.trans hs₂) (hf₁.trans hf₂) hh₂

theorem spec_cmp {d : Nat} {op : Cmp} {a b : Tm} (ha : Spec P host d a)
    (hb : Spec P host d b) : Spec (H := H) P host d (.cmp op a b) := by
  intro σ ρ v σ' hv μ s f hf hd hr hh us rest Q hk
  obtain ⟨x, σ₁, y, hxa, hyb, rfl⟩ := eval_cmp_inv hv
  show TWP P host s f (vals us ++ (expression (compile d a ++ unbox ++ compile d b ++ unbox ++
    [.intRelOp .i32 (FunCompile.Cmp.wasm op), .refI31]) ++ rest)) Q
  simp only [List.append_assoc, expr_append]
  refine ha σ ρ _ σ₁ hxa μ s f hf (depth_left hd) hr hh us _ Q
    (Cont.unboxInt fun μ₁ s₁ f₁ hμ₁ hs₁ hf₁ hh₁ => ?_)
  have hdb : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  refine hb σ₁ ρ _ σ' hyb μ₁ s₁ f₁ (hf.of_agree hf₁) hdb (hr.of_agree hμ₁ hs₁ hf₁) hh₁ _ _ Q
    (Cont.unboxInt fun μ₂ s₂ f₂ hμ₂ hs₂ hf₂ hh₂ => ?_)
  exact twp_cmpTail hk (hμ₁.trans hμ₂) (hs₁.trans hs₂) (hf₁.trans hf₂) hh₂

/-! ## Blocks -/

/-- The code of a term inside a block of result `anyref`. -/
theorem twp_inBlock {d : Nat} {e : Tm} (hsp : Spec P host d e) {σ σ' : Heap}
    {ρ : List FunRef.Val} {v : FunRef.Val} (hv : eval σ ρ e = some (v, σ')) {μ : List Nat}
    {s : Store H} {f : Frame} (hf : FrameR f) (hd : d + e.depth < f.locals.length)
    (hr : EnvRep μ s f d ρ) (hh : HeapRep μ s σ) {us : List Val} {rest : List Admin}
    {Q : Post H} (hk : Cont P host d μ s f v σ' us rest Q) :
    TWP P host s f (vals [] ++ expression (compile d e))
      (labelPostT P host 1 [] us (seqPostT P host rest Q)) := by
  have h' := hsp σ ρ v σ' hv μ s f hf hd hr hh [] []
    (labelPostT P host 1 [] us (seqPostT P host rest Q))
    fun μ' s' f' w hμ hs hag hh' hw =>
      Wp.of_vals (m := .total) (vs := [w]) (hk μ' s' f' w hμ hs hag hh' hw)
  simpa using h'

theorem spec_ite {d : Nat} {c t e : Tm} (hc : Spec P host d c) (ht : Spec P host d t)
    (he : Spec P host d e) : Spec (H := H) P host d (.ite c t e) := by
  intro σ ρ v σ' hv μ s f hf hd hr hh us rest Q hk
  obtain ⟨b, σ₁, hcb, hbr⟩ := eval_ite_inv hv
  have hsp : Spec P host d (if b then t else e) := by cases b; exacts [he, ht]
  have hdb : d + (if b then t else e).depth < f.locals.length := by
    cases b
    · exact depth_right (depth_right hd)
    · exact depth_left (depth_right hd)
  have hsel : (if (if b then (1 : BitVec 31) else 0).setWidth 32 ≠ 0 then compile d t else
      compile d e) = compile d (if b then t else e) := by cases b <;> rfl
  show TWP P host s f (vals us ++ (expression (compile d c ++ unbox ++
    [.if_ (.value anyref) (compile d t) (compile d e)]) ++ rest)) Q
  simp only [List.append_assoc, expr_append]
  refine hc σ ρ _ σ₁ hcb μ s f hf (depth_left hd) hr hh us _ Q
    (Cont.unboxBool fun μ₁ s₁ f₁ hμ₁ hs₁ hf₁ hh₁ => ?_)
  refine twp_ifBlock ?_
  rw [hsel]
  exact twp_inBlock hsp hbr (hf.of_agree hf₁) (hf₁.2.1 ▸ hdb) (hr.of_agree hμ₁ hs₁ hf₁) hh₁
    (hk.later hμ₁ hs₁ hf₁)

/-! ## Binders -/

theorem spec_let {d : Nat} {a b : Tm} (ha : Spec P host d a) (hb : Spec P host (d + 1) b) :
    Spec (H := H) P host d (.let_ a b) := by
  intro σ ρ v σ' hv μ s f hf hd hr hh us rest Q hk
  obtain ⟨u, σ₁, hu, hbv⟩ := eval_let_inv hv
  have hdb : d + 1 + b.depth < f.locals.length := depth_succ (depth_right hd)
  have hlt : d + 1 < f.locals.length := by omega
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.ok hlt
  show TWP P host s f (vals us ++ (expression (compile d a ++
    .localSet (lx (d + 1)) :: compile (d + 1) b) ++ rest)) Q
  rw [expr_append]
  refine ha σ ρ u σ₁ hu μ s f hf (depth_left hd) hr hh us _ Q
    fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
  refine twp_localSet (hf.of_agree hf₁).ok hlt₁ ?_
  refine hb σ₁ (u :: ρ) v σ' hbv μ₁ s₁ _ ((hf.of_agree hf₁).setLocal _ w)
    (by rw [len_setLocal, hf₁.2.1]; exact hdb) ((hr.of_agree hμ₁ hs₁ hf₁).cons hw hlt₁ hlim) hh₁
    us rest Q fun μ₂ s₂ f₂ w₂ hμ₂ hs₂ hf₂ hh₂ hw₂ => ?_
  exact hk μ₂ s₂ f₂ w₂ (hμ₁.trans hμ₂) (hs₁.trans hs₂)
    (hf₁.trans ((Agree.setLocal w hlim).trans hf₂.of_succ)) hh₂ hw₂

/-! ## Pairs -/

theorem twp_pairTail {d : Nat} {μ μ₁ μ₂ : List Nat} {s s₁ s₂ : Store H} {f f₂ : Frame}
    (hf₂ : FrameR f₂) {x y : FunRef.Val} {σ' : Heap} {wa wb : Val} {us : List Val}
    {rest : List Admin} {Q : Post H} (hk : Cont P host d μ s f (.pair x y) σ' us rest Q)
    (hμ₁ : μ <+: μ₁) (hμ₂ : μ₁ <+: μ₂) (hs₁ : BoxExt s s₁) (hs₂ : BoxExt s₁ s₂)
    (hag : Agree d f f₂) (hh₂ : HeapRep μ₂ s₂ σ') (hwa : Rep μ₁ s₁ x wa) (hwb : Rep μ₂ s₂ y wb) :
    TWP P host s₂ f₂ (vals ((us ++ [wa]) ++ [wb]) ++
      (expression [.structNew boxIdx] ++ rest)) Q := by
  rw [vals_pair]
  refine twp_newBox hf₂.ok ?_
  have hp := addStruct_prefix s₂ ⟨dBox, [.val wa, .val wb]⟩
  have he : BoxExt s₂ (s₂.addStruct ⟨dBox, [.val wa, .val wb]⟩) := BoxExt.of_prefix hp
  exact hk μ₂ _ f₂ _ (hμ₁.trans hμ₂) ((hs₁.trans hs₂).trans he) hag (hh₂.prefix hp)
    ⟨s₂.structs.length, wa, wb, rfl, addStruct_get _ _,
      (hwa.mono hμ₂ hs₂).mono (List.prefix_refl _) he, hwb.mono (List.prefix_refl _) he⟩

theorem spec_pair {d : Nat} {a b : Tm} (ha : Spec P host d a) (hb : Spec P host d b) :
    Spec (H := H) P host d (.pair a b) := by
  intro σ ρ v σ' hv μ s f hf hd hr hh us rest Q hk
  obtain ⟨x, σ₁, y, hxa, hyb, rfl⟩ := eval_pair_inv hv
  show TWP P host s f (vals us ++ (expression (compile d a ++ compile d b ++
    [.structNew boxIdx]) ++ rest)) Q
  simp only [List.append_assoc, expr_append]
  refine ha σ ρ _ σ₁ hxa μ s f hf (depth_left hd) hr hh us _ Q
    fun μ₁ s₁ f₁ wa hμ₁ hs₁ hf₁ hh₁ hwa => ?_
  have hdb : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  refine hb σ₁ ρ _ σ' hyb μ₁ s₁ f₁ (hf.of_agree hf₁) hdb (hr.of_agree hμ₁ hs₁ hf₁) hh₁ _ _ Q
    fun μ₂ s₂ f₂ wb hμ₂ hs₂ hf₂ hh₂ hwb => ?_
  exact twp_pairTail (hf.of_agree (hf₁.trans hf₂)) hk hμ₁ hμ₂ hs₁ hs₂ (hf₁.trans hf₂) hh₂ hwa hwb

theorem spec_fst {d : Nat} {e : Tm} (he : Spec P host d e) : Spec (H := H) P host d (.fst e) := by
  intro σ ρ v σ' hv μ s f hf hd hr hh us rest Q hk
  obtain ⟨y, hev⟩ := eval_fst_inv hv
  show TWP P host s f (vals us ++ (expression (compile d e ++
    [.refCast boxRef, .structGet none boxIdx (fx 0)]) ++ rest)) Q
  rw [expr_append]
  refine he σ ρ _ σ' hev μ s f hf hd hr hh us _ Q fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  obtain ⟨addr, wa, wb, hw', hst, hwa, -⟩ := hw
  rw [hw']
  have hf₁' : FrameOK f₁ := (hf.of_agree hf₁).ok
  exact twp_castBox hf₁' hst (twp_getBox hf₁' (by omega) hst (hk μ₁ s₁ f₁ wa hμ₁ hs₁ hf₁ hh₁ hwa))

theorem spec_snd {d : Nat} {e : Tm} (he : Spec P host d e) : Spec (H := H) P host d (.snd e) := by
  intro σ ρ v σ' hv μ s f hf hd hr hh us rest Q hk
  obtain ⟨x, hev⟩ := eval_snd_inv hv
  show TWP P host s f (vals us ++ (expression (compile d e ++
    [.refCast boxRef, .structGet none boxIdx (fx 1)]) ++ rest)) Q
  rw [expr_append]
  refine he σ ρ _ σ' hev μ s f hf hd hr hh us _ Q fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  obtain ⟨addr, wa, wb, hw', hst, -, hwb⟩ := hw
  rw [hw']
  have hf₁' : FrameOK f₁ := (hf.of_agree hf₁).ok
  exact twp_castBox hf₁' hst (twp_getBox hf₁' (by omega) hst (hk μ₁ s₁ f₁ wb hμ₁ hs₁ hf₁ hh₁ hwb))

/-! ## Injections -/

/-- The value of an injection with tag `0` (`inl`) or `1` (`inr`). -/
def inj (tag : BitVec 31) (u : FunRef.Val) : FunRef.Val := if tag = 0 then .inl u else .inr u

theorem rep_inj {μ : List Nat} {s : Store H} {tag : BitVec 31} (ht : tag = 0 ∨ tag = 1)
    {u : FunRef.Val} {wv : Val} {addr : Nat}
    (hst : s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 tag)), .val wv]⟩)
    (hu : Rep μ s u wv) : Rep μ s (inj tag u) (.ref (.struct addr)) := by
  rcases ht with rfl | rfl
  · exact ⟨addr, wv, rfl, hst, hu⟩
  · exact ⟨addr, wv, rfl, hst, hu⟩

theorem spec_injTag {d : Nat} {e : Tm} {tag : BitVec 31} (ht : tag = 0 ∨ tag = 1)
    (he : Spec P host d e) {σ σ' : Heap} {ρ : List FunRef.Val} {u : FunRef.Val}
    (hev : eval σ ρ e = some (u, σ')) {μ : List Nat} {s : Store H} {f : Frame} (hf : FrameR f)
    (hd : d + e.depth < f.locals.length) (hr : EnvRep μ s f d ρ) (hh : HeapRep μ s σ)
    {us : List Val} {rest : List Admin} {Q : Post H}
    (hk : Cont P host d μ s f (inj tag u) σ' us rest Q) :
    TWP P host s f (vals us ++ (expression (.intConst .i32 (tag.setWidth 32) :: .refI31 ::
      compile d e ++ [.structNew boxIdx]) ++ rest)) Q := by
  show TWP P host s f (vals us ++ (expression [.intConst .i32 (tag.setWidth 32), .refI31] ++
    (expression (compile d e ++ [.structNew boxIdx]) ++ rest))) Q
  refine twp_constBox ?_
  rw [expr_append, setWidth_31_32]
  refine he σ ρ u σ' hev μ s f hf hd hr hh _ _ Q fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  rw [vals_pair]
  refine twp_newBox (hf.of_agree hf₁).ok ?_
  have hp := addStruct_prefix s₁ ⟨dBox, [.val (.ref (.i31 tag)), .val w]⟩
  have hx : BoxExt s₁ (s₁.addStruct ⟨dBox, [.val (.ref (.i31 tag)), .val w]⟩) := BoxExt.of_prefix hp
  exact hk μ₁ _ f₁ _ hμ₁ (hs₁.trans hx) hf₁ (hh₁.prefix hp)
    (rep_inj ht (addStruct_get _ _) (hw.mono (List.prefix_refl _) hx))

theorem spec_inl {d : Nat} {e : Tm} (he : Spec P host d e) : Spec (H := H) P host d (.inl e) := by
  intro σ ρ v σ' hv μ s f hf hd hr hh us rest Q hk
  obtain ⟨u, hev, rfl⟩ := eval_inl_inv hv
  exact spec_injTag (tag := 0) (.inl rfl) he hev hf hd hr hh hk

theorem spec_inr {d : Nat} {e : Tm} (he : Spec P host d e) : Spec (H := H) P host d (.inr e) := by
  intro σ ρ v σ' hv μ s f hf hd hr hh us rest Q hk
  obtain ⟨u, hev, rfl⟩ := eval_inr_inv hv
  exact spec_injTag (tag := 1) (.inr rfl) he hev hf hd hr hh hk

/-! ## `case` -/

/-- The code of a `case` branch. -/
def branch (d : Nat) (t : Tm) : List Instr :=
  getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile (d + 1) t

theorem twp_branch {d : Nat} {t : Tm} (hsp : Spec P host (d + 1) t) {σ σ' : Heap}
    {ρ : List FunRef.Val} {u v : FunRef.Val} (hev : eval σ (u :: ρ) t = some (v, σ'))
    {μ : List Nat} {s : Store H} {f : Frame} (hf : FrameR f)
    (hd : d + 1 + t.depth < f.locals.length) (hr : EnvRep μ s f d ρ) (hh : HeapRep μ s σ)
    {addr : Nat} {tagw wv : Val} (hloc : f.locals[d + 1]? = some (some (.ref (.struct addr))))
    (hst : s.structs[addr]? = some ⟨dBox, [.val tagw, .val wv]⟩) (hu : Rep μ s u wv)
    {us : List Val} {rest : List Admin} {Q : Post H} (hk : Cont P host d μ s f v σ' us rest Q) :
    TWP P host s f (vals [] ++ expression (branch d t))
      (labelPostT P host 1 [] us (seqPostT P host rest Q)) := by
  have hlt : d + 1 < f.locals.length := by omega
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.ok hlt
  show TWP P host s f (vals [] ++ .plain (.localGet (lx (d + 1))) :: .plain (.refCast boxRef) ::
    .plain (.structGet none boxIdx (fx 1)) :: .plain (.localSet (lx (d + 1))) ::
    expression (compile (d + 1) t)) _
  refine twp_localGet hf.ok hloc (twp_castBox hf.ok hst (twp_getBox hf.ok (by omega) hst
    (twp_localSet (w := wv) hf.ok hlt ?_)))
  have hk' : Cont P host (d + 1) μ s (f.setLocal (lx (d + 1)) wv) v σ' [] []
      (labelPostT P host 1 [] us (seqPostT P host rest Q)) :=
    fun μ' s' f' w hμ hs hag hh' hw => Wp.of_vals (m := .total) (vs := [w])
      (hk μ' s' f' w hμ hs ((Agree.setLocal wv hlim).trans hag.of_succ) hh' hw)
  have h' := hsp σ (u :: ρ) v σ' hev μ s _ (hf.setLocal _ wv) (by rw [len_setLocal]; exact hd)
    (hr.cons hu hlt hlim) hh [] [] _ hk'
  simpa using h'

theorem spec_caseArm {d : Nat} {e t : Tm} {tag : BitVec 31} (ht : tag = 0 ∨ tag = 1)
    (he : Spec P host d e) (hsp : Spec P host (d + 1) t) {σ σ₁ σ' : Heap}
    {ρ : List FunRef.Val} {u v : FunRef.Val} (hev : eval σ ρ e = some (inj tag u, σ₁))
    (hbv : eval σ₁ (u :: ρ) t = some (v, σ')) {μ : List Nat} {s : Store H} {f : Frame}
    (hf : FrameR f) (hde : d + e.depth < f.locals.length) (hdt : d + 1 + t.depth < f.locals.length)
    (hr : EnvRep μ s f d ρ) (hh : HeapRep μ s σ) {br bl : List Instr}
    (hsel : (if tag.setWidth 32 ≠ 0 then br else bl) = branch d t)
    {us : List Val} {rest : List Admin} {Q : Post H} (hk : Cont P host d μ s f v σ' us rest Q) :
    TWP P host s f (vals us ++ (expression (compile d e) ++ (expression (.localSet (lx (d + 1)) ::
      getField (d + 1) 0 ++ unbox ++ [.if_ (.value anyref) br bl]) ++ rest))) Q := by
  have hlt : d + 1 < f.locals.length := by omega
  refine he σ ρ _ σ₁ hev μ s f hf hde hr hh us _ Q fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  have hw' : ∃ addr wv, w = .ref (.struct addr) ∧
      s₁.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 tag)), .val wv]⟩ ∧ Rep μ₁ s₁ u wv := by
    rcases ht with rfl | rfl
    · exact hw
    · exact hw
  obtain ⟨addr, wv, rfl, hst, hu⟩ := hw'
  have hf₁' : FrameR f₁ := hf.of_agree hf₁
  have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.ok hlt
  refine twp_caseTail hf₁'.ok hlt₁ hst ?_
  rw [hsel]
  exact twp_branch hsp hbv (hf₁'.setLocal _ _) (by rw [len_setLocal, hf₁.2.1]; exact hdt)
    ((hr.of_agree hμ₁ hs₁ hf₁).of_agree (List.prefix_refl _) (BoxExt.refl _)
      (Agree.setLocal _ hlim))
    hh₁ (setLocal_get _ hlt₁ hlim) hst hu
    ((hk.later hμ₁ hs₁ hf₁).later (List.prefix_refl _) (BoxExt.refl _) (Agree.setLocal _ hlim))

theorem spec_case {d : Nat} {e l r : Tm} (he : Spec P host d e) (hl : Spec P host (d + 1) l)
    (hr' : Spec P host (d + 1) r) : Spec (H := H) P host d (.case e l r) := by
  intro σ ρ v σ' hv μ s f hf hd hr hh us rest Q hk
  have hdlr : d + 1 + max l.depth r.depth < f.locals.length := depth_succ (depth_right hd)
  show TWP P host s f (vals us ++ (expression (compile d e ++ .localSet (lx (d + 1)) ::
    getField (d + 1) 0 ++ unbox ++ [.if_ (.value anyref) (branch d r) (branch d l)]) ++ rest)) Q
  simp only [List.append_assoc]
  rw [expr_append]
  rcases eval_case_inv hv with ⟨u, σ₁, hev, hbv⟩ | ⟨u, σ₁, hev, hbv⟩
  · exact spec_caseArm (tag := 0) (.inl rfl) he hl hev hbv hf (depth_left hd) (depth_left hdlr)
      hr hh rfl hk
  · exact spec_caseArm (tag := 1) (.inr rfl) he hr' hev hbv hf (depth_left hd) (depth_right hdlr)
      hr hh rfl hk

/-! ## References -/

theorem spec_ref {d : Nat} {e : Tm} (he : Spec P host d e) : Spec (H := H) P host d (.ref e) := by
  intro σ ρ v σ' hv μ s f hf hd hr hh us rest Q hk
  obtain ⟨u, σ₁, hev, rfl, rfl⟩ := eval_ref_inv hv
  show TWP P host s f (vals us ++ (expression (compile d e ++ [.structNew cellIdx]) ++ rest)) Q
  rw [expr_append]
  refine he σ ρ u σ₁ hev μ s f hf hd hr hh us _ Q fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  refine twp_newCell (hf.of_agree hf₁) ?_
  have hp : s₁.structs <+: (s₁.addStruct ⟨dCell, [.val w]⟩).structs := List.prefix_append _ _
  have hloc : (μ₁ ++ [s₁.structs.length])[σ₁.length]? = some s₁.structs.length := by
    rw [← hh₁.1]; simp
  exact hk _ _ f₁ _ (hμ₁.trans (List.prefix_append _ _)) (hs₁.trans (BoxExt.of_prefix hp)) hf₁
    (hh₁.alloc hw) ⟨s₁.structs.length, hloc, rfl⟩

theorem spec_get {d : Nat} {e : Tm} (he : Spec P host d e) : Spec (H := H) P host d (.get e) := by
  intro σ ρ v σ' hv μ s f hf hd hr hh us rest Q hk
  obtain ⟨l, hev, hl⟩ := eval_get_inv hv
  show TWP P host s f (vals us ++ (expression (compile d e ++
    [.refCast cellRef, .structGet none cellIdx (fx 0)]) ++ rest)) Q
  rw [expr_append]
  refine he σ ρ _ σ' hev μ s f hf hd hr hh us _ Q fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  obtain ⟨addr, hμl, rfl⟩ := hw
  obtain ⟨u, w', hu, hst, hrep⟩ := hh₁.cell hμl
  have huv : u = v := Option.some.inj (hu.symm.trans hl)
  have hf₁' : FrameR f₁ := hf.of_agree hf₁
  exact twp_castCell hf₁' hst (twp_getCell hf₁' hst
    (hk μ₁ s₁ f₁ w' hμ₁ hs₁ hf₁ hh₁ (huv ▸ hrep)))

theorem twp_setTail {d : Nat} {μ μ₂ : List Nat} {s s₂ : Store H} {f f₂ : Frame}
    (hf₂ : FrameR f₂) {l addr : Nat} {u : FunRef.Val} {σ₂ : Heap} {wb : Val} {us : List Val}
    {rest : List Admin} {Q : Post H}
    (hk : Cont P host d μ s f (.bool true) (σ₂.set l u) us rest Q) (hμ : μ <+: μ₂)
    (hs : BoxExt s s₂) (hag : Agree d f f₂) (hh₂ : HeapRep μ₂ s₂ σ₂)
    (hμl : μ₂[l]? = some addr) (hwb : Rep μ₂ s₂ u wb) :
    TWP P host s₂ f₂ (vals ((us ++ [.ref (.struct addr)]) ++ [wb]) ++
      (expression [.structSet cellIdx (fx 0), .intConst .i32 1, .refI31] ++ rest)) Q := by
  obtain ⟨_, w₀, -, hst, -⟩ := hh₂.cell hμl
  rw [vals_pair]
  refine twp_setCell hf₂ hst ?_
  have hx : BoxExt s₂ (s₂.setStructField addr 0 (.val wb)) := BoxExt.setCell hst 0 _
  have hrep : Rep μ₂ (s₂.setStructField addr 0 (.val wb)) (.bool true)
      (.ref (.i31 ((1 : BitVec 32).setWidth 31))) := rfl
  exact twp_constBox (hk μ₂ _ f₂ _ hμ (hs.trans hx) hag (hh₂.set hμl hwb) hrep)

theorem spec_set {d : Nat} {a b : Tm} (ha : Spec P host d a) (hb : Spec P host d b) :
    Spec (H := H) P host d (.set a b) := by
  intro σ ρ v σ' hv μ s f hf hd hr hh us rest Q hk
  obtain ⟨l, σ₁, u, σ₂, hea, heb, rfl, rfl⟩ := eval_set_inv hv
  show TWP P host s f (vals us ++ (expression (compile d a ++ .refCast cellRef :: compile d b ++
    [.structSet cellIdx (fx 0), .intConst .i32 1, .refI31]) ++ rest)) Q
  simp only [List.append_assoc, List.cons_append]
  rw [expr_append]
  refine ha σ ρ _ σ₁ hea μ s f hf (depth_left hd) hr hh us _ Q
    fun μ₁ s₁ f₁ w hμ₁ hs₁ hf₁ hh₁ hw => ?_
  obtain ⟨addr, hμl, rfl⟩ := hw
  obtain ⟨_, _, -, hst₁, -⟩ := hh₁.cell hμl
  refine twp_castCell (hf.of_agree hf₁) hst₁ ?_
  show TWP P host s₁ f₁ (vals (us ++ [.ref (.struct addr)]) ++ (expression (compile d b ++
    [.structSet cellIdx (fx 0), .intConst .i32 1, .refI31]) ++ rest)) Q
  rw [expr_append]
  have hdb : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  refine hb σ₁ ρ u σ₂ heb μ₁ s₁ f₁ (hf.of_agree hf₁) hdb (hr.of_agree hμ₁ hs₁ hf₁) hh₁ _ _ Q
    fun μ₂ s₂ f₂ wb hμ₂ hs₂ hf₂ hh₂ hwb => ?_
  exact twp_setTail (hf.of_agree (hf₁.trans hf₂)) hk (hμ₁.trans hμ₂) (hs₁.trans hs₂)
    (hf₁.trans hf₂) hh₂ (getElem?_of_prefix hμ₂ hμl) hwb

/-! ## Every term -/

/-- **The code of every term is correct**, at every depth, profile and host. -/
theorem spec_compile (e : Tm) : ∀ d, Spec (H := H) P host d e := by
  induction e with
  | var i => exact fun d => spec_var d i
  | int n => exact fun d => spec_int d n
  | bool b => exact fun d => spec_bool d b
  | arith op a b iha ihb => exact fun d => spec_arith (iha d) (ihb d)
  | cmp op a b iha ihb => exact fun d => spec_cmp (iha d) (ihb d)
  | ite c t e ihc iht ihe => exact fun d => spec_ite (ihc d) (iht d) (ihe d)
  | let_ a b iha ihb => exact fun d => spec_let (iha d) (ihb (d + 1))
  | pair a b iha ihb => exact fun d => spec_pair (iha d) (ihb d)
  | fst e ih => exact fun d => spec_fst (ih d)
  | snd e ih => exact fun d => spec_snd (ih d)
  | inl e ih => exact fun d => spec_inl (ih d)
  | inr e ih => exact fun d => spec_inr (ih d)
  | case e l r ihe ihl ihr => exact fun d => spec_case (ihe d) (ihl (d + 1)) (ihr (d + 1))
  | ref e ih => exact fun d => spec_ref (ih d)
  | get e ih => exact fun d => spec_get (ih d)
  | set a b iha ihb => exact fun d => spec_set (iha d) (ihb d)

end Silmaril.Proofs.Wasm.Models.FunRefCompile
