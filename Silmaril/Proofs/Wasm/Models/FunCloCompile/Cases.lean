module

public import Silmaril.Proofs.Wasm.Models.FunCloCompile.Rep

/-!
# Compiling FunClo: the FunLang constructs

`Spec P host p (k + 1) d e` for every FunLang constructor of `Tm` from `Spec … k` of its
subterms (`spec_var` … `spec_case`), reusing FunCompile's instruction lemmas. The proofs follow
`Silmaril.Proofs.Wasm.Models.FunCompile.Cases`, with fuel, the closure table and the invariant
that `apply` stays at address `1`.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCloCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunCloCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunClo (Tm eval Prog)
open Silmaril.Wasm.Models.FunLang (Arith Cmp)
open Silmaril.Wasm.Models.FunCompile (dBox lx fx boxIdx boxRef unbox getField anyref)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree twp_unbox twp_box twp_castBox twp_getBox
  twp_newBox addStruct_get addStruct_prefix twp_localGet twp_localSet twp_constBox len_setLocal
  setLocal_get lt_lim vals_pair arith_wasm cmp_wasm bool32_31 setWidth_31_32 twp_ifBlock
  expr_append depth_left depth_right depth_succ twp_caseTail)
open Silmaril.Wasm.Logic.Core (Post)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-! ## Inversion of evaluation -/

theorem eval_arith_inv {k : Nat} {ρ : List FunClo.Val} {op : Arith} {a b : Tm}
    {v : FunClo.Val} (h : eval (k + 1) ρ (.arith op a b) = some v) :
    ∃ x y, eval k ρ a = some (.int x) ∧ eval k ρ b = some (.int y) ∧ v = .int (op.eval x y) := by
  simp only [eval] at h
  split at h
  · next x y ha hb => exact ⟨x, y, ha, hb, (Option.some.inj h).symm⟩
  · cases h

theorem eval_cmp_inv {k : Nat} {ρ : List FunClo.Val} {op : Cmp} {a b : Tm} {v : FunClo.Val}
    (h : eval (k + 1) ρ (.cmp op a b) = some v) :
    ∃ x y, eval k ρ a = some (.int x) ∧ eval k ρ b = some (.int y) ∧ v = .bool (op.eval x y) := by
  simp only [eval] at h
  split at h
  · next x y ha hb => exact ⟨x, y, ha, hb, (Option.some.inj h).symm⟩
  · cases h

theorem eval_ite_inv {k : Nat} {ρ : List FunClo.Val} {c t e : Tm} {v : FunClo.Val}
    (h : eval (k + 1) ρ (.ite c t e) = some v) :
    ∃ b, eval k ρ c = some (.bool b) ∧ eval k ρ (if b then t else e) = some v := by
  simp only [eval] at h
  split at h
  · next hc => exact ⟨true, hc, h⟩
  · next hc => exact ⟨false, hc, h⟩
  · cases h

theorem eval_let_inv {k : Nat} {ρ : List FunClo.Val} {a b : Tm} {v : FunClo.Val}
    (h : eval (k + 1) ρ (.let_ a b) = some v) :
    ∃ u, eval k ρ a = some u ∧ eval k (u :: ρ) b = some v := by
  simp only [eval] at h
  split at h
  · next u hu => exact ⟨u, hu, h⟩
  · cases h

theorem eval_pair_inv {k : Nat} {ρ : List FunClo.Val} {a b : Tm} {v : FunClo.Val}
    (h : eval (k + 1) ρ (.pair a b) = some v) :
    ∃ x y, eval k ρ a = some x ∧ eval k ρ b = some y ∧ v = .pair x y := by
  simp only [eval] at h
  split at h
  · next x y ha hb => exact ⟨x, y, ha, hb, (Option.some.inj h).symm⟩
  · cases h

theorem eval_fst_inv {k : Nat} {ρ : List FunClo.Val} {e : Tm} {v : FunClo.Val}
    (h : eval (k + 1) ρ (.fst e) = some v) : ∃ y, eval k ρ e = some (.pair v y) := by
  simp only [eval] at h
  split at h
  · next x y he => exact ⟨y, (Option.some.inj h) ▸ he⟩
  · cases h

theorem eval_snd_inv {k : Nat} {ρ : List FunClo.Val} {e : Tm} {v : FunClo.Val}
    (h : eval (k + 1) ρ (.snd e) = some v) : ∃ x, eval k ρ e = some (.pair x v) := by
  simp only [eval] at h
  split at h
  · next x y he => exact ⟨x, (Option.some.inj h) ▸ he⟩
  · cases h

theorem eval_inl_inv {k : Nat} {ρ : List FunClo.Val} {e : Tm} {v : FunClo.Val}
    (h : eval (k + 1) ρ (.inl e) = some v) : ∃ u, eval k ρ e = some u ∧ v = .inl u := by
  simp only [eval, Option.map_eq_some_iff] at h
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨u, hu, rfl⟩

theorem eval_inr_inv {k : Nat} {ρ : List FunClo.Val} {e : Tm} {v : FunClo.Val}
    (h : eval (k + 1) ρ (.inr e) = some v) : ∃ u, eval k ρ e = some u ∧ v = .inr u := by
  simp only [eval, Option.map_eq_some_iff] at h
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨u, hu, rfl⟩

theorem eval_case_inv {k : Nat} {ρ : List FunClo.Val} {e l r : Tm} {v : FunClo.Val}
    (h : eval (k + 1) ρ (.case e l r) = some v) :
    (∃ u, eval k ρ e = some (.inl u) ∧ eval k (u :: ρ) l = some v) ∨
      (∃ u, eval k ρ e = some (.inr u) ∧ eval k (u :: ρ) r = some v) := by
  simp only [eval] at h
  split at h
  · next u hu => exact .inl ⟨u, hu, h⟩
  · next u hu => exact .inr ⟨u, hu, h⟩
  · cases h

/-! ## Bookkeeping -/

theorem sub_left {L l₁ l₂ : List (Nat × Tm)} (h : ∀ x ∈ l₁ ++ l₂, x ∈ L) : ∀ x ∈ l₁, x ∈ L :=
  fun x hx => h x (List.mem_append_left _ hx)

theorem sub_right {L l₁ l₂ : List (Nat × Tm)} (h : ∀ x ∈ l₁ ++ l₂, x ∈ L) : ∀ x ∈ l₂, x ∈ L :=
  fun x hx => h x (List.mem_append_right _ hx)

theorem Ext.funcs {s s' : Store Nat} {a : Nat} {fi : FuncInst Nat} (h : Ext s s')
    (hf : s.funcs[a]? = some fi) : s'.funcs[a]? = some fi := by
  rw [h.2]; exact hf

theorem Cont.unboxInt {d : Nat} {s : Store Nat} {f : Frame} {x : BitVec 31} {us : List Val}
    {rest : List Admin} {Q : Post Nat}
    (h : ∀ s' f', Ext s s' → Agree d f f' →
      TWP P host s' f' (vals (us ++ [.i32 (x.setWidth 32)]) ++ rest) Q) :
    Cont P host p.table d s f (.int x) us (expression unbox ++ rest) Q := by
  intro s' f' w hs hf hw
  have hw' : w = .ref (.i31 x) := hw
  rw [hw']
  exact twp_unbox (h s' f' hs hf)

theorem Cont.unboxBool {d : Nat} {s : Store Nat} {f : Frame} {b : Bool} {us : List Val}
    {rest : List Admin} {Q : Post Nat}
    (h : ∀ s' f', Ext s s' → Agree d f f' →
      TWP P host s' f'
        (vals (us ++ [.i32 ((if b then (1 : BitVec 31) else 0).setWidth 32)]) ++ rest) Q) :
    Cont P host p.table d s f (.bool b) us (expression unbox ++ rest) Q := by
  intro s' f' w hs hf hw
  have hw' : w = .ref (.i31 (if b then 1 else 0)) := hw
  rw [hw']
  exact twp_unbox (h s' f' hs hf)

/-! ## Leaves -/

theorem spec_var (k d i : Nat) : Spec P host p (k + 1) d (.var i) := by
  intro ρ v hv s f hf _ _ hr _ us rest Q hk
  obtain ⟨w, hw, hrep⟩ := hr.2 i v hv
  exact twp_localGet hf.1 hw (hk s f w (Ext.refl s) (Agree.refl d f) hrep)

theorem spec_int (k d : Nat) (n : BitVec 31) : Spec P host p (k + 1) d (.int n) := by
  intro ρ v hv s f _ _ _ _ _ us rest Q hk
  have hv' : v = .int n := (Option.some.inj hv).symm
  have hw : Rep p.table s v (.ref (.i31 ((n.setWidth 32).setWidth 31))) := by
    rw [hv', setWidth_31_32]; rfl
  exact twp_constBox (hk s f _ (Ext.refl s) (Agree.refl d f) hw)

theorem spec_bool (k d : Nat) (b : Bool) : Spec P host p (k + 1) d (.bool b) := by
  intro ρ v hv s f _ _ _ _ _ us rest Q hk
  have hv' : v = .bool b := (Option.some.inj hv).symm
  have hw : Rep p.table s v (.ref (.i31 ((if b then (1 : BitVec 32) else 0).setWidth 31))) := by
    rw [hv']; cases b <;> rfl
  exact twp_constBox (hk s f _ (Ext.refl s) (Agree.refl d f) hw)

/-! ## Arithmetic and comparisons -/

theorem twp_arithTail {d : Nat} {s s₂ : Store Nat} {f f₂ : Frame} {op : Arith} {x y : BitVec 31}
    {us : List Val} {rest : List Admin} {Q : Post Nat}
    (hk : Cont P host p.table d s f (.int (op.eval x y)) us rest Q) (hs : Ext s s₂)
    (hf : Agree d f f₂) :
    TWP P host s₂ f₂ (vals ((us ++ [.i32 (x.setWidth 32)]) ++ [.i32 (y.setWidth 32)]) ++
      (expression [.intBinOp .i32 (FunCompile.Arith.wasm op), .refI31] ++ rest)) Q := by
  obtain ⟨z, hz, hzw⟩ := arith_wasm op x y
  have hrep : Rep p.table s₂ (.int (op.eval x y)) (.ref (.i31 (z.setWidth 31))) := by
    show Val.ref (.i31 (z.setWidth 31)) = .ref (.i31 (op.eval x y))
    rw [hzw]
  rw [vals_pair]
  exact Wp.intBinOp (m := .total) hz (twp_box (hk s₂ f₂ _ hs hf hrep))

theorem twp_cmpTail {d : Nat} {s s₂ : Store Nat} {f f₂ : Frame} {op : Cmp} {x y : BitVec 31}
    {us : List Val} {rest : List Admin} {Q : Post Nat}
    (hk : Cont P host p.table d s f (.bool (op.eval x y)) us rest Q) (hs : Ext s s₂)
    (hf : Agree d f f₂) :
    TWP P host s₂ f₂ (vals ((us ++ [.i32 (x.setWidth 32)]) ++ [.i32 (y.setWidth 32)]) ++
      (expression [.intRelOp .i32 (FunCompile.Cmp.wasm op), .refI31] ++ rest)) Q := by
  have hrep : Rep p.table s₂ (.bool (op.eval x y))
      (.ref (.i31 ((Numerics.intRelOp .i32 (FunCompile.Cmp.wasm op) (x.setWidth 32)
        (y.setWidth 32)).setWidth 31))) := by
    show Val.ref (.i31 _) = .ref (.i31 (if op.eval x y then 1 else 0))
    rw [cmp_wasm, bool32_31]
  rw [vals_pair]
  exact Wp.intRelOp (m := .total) (twp_box (hk s₂ f₂ _ hs hf hrep))

theorem spec_arith {k d : Nat} {op : Arith} {a b : Tm} (ha : Spec P host p k d a)
    (hb : Spec P host p k d b) : Spec P host p (k + 1) d (.arith op a b) := by
  intro ρ v hv s f hf hfn hd hr hfx us rest Q hk
  obtain ⟨x, y, hxa, hyb, rfl⟩ := eval_arith_inv hv
  show TWP P host s f (vals us ++ (expression (compile p.table d a ++ unbox ++
    compile p.table d b ++ unbox ++ [.intBinOp .i32 (FunCompile.Arith.wasm op), .refI31]) ++
    rest)) Q
  simp only [List.append_assoc, expr_append]
  refine ha ρ _ hxa s f hf hfn (depth_left hd) hr (sub_left hfx) us _ Q
    (Cont.unboxInt fun s₁ f₁ hs₁ hf₁ => ?_)
  have hdb : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  refine hb ρ _ hyb s₁ f₁ (hf.of_agree hf₁) (hs₁.funcs hfn) hdb (hr.of_agree hs₁.1 hf₁)
    (sub_right hfx) _ _ Q (Cont.unboxInt fun s₂ f₂ hs₂ hf₂ => ?_)
  exact twp_arithTail hk (hs₁.trans hs₂) (hf₁.trans hf₂)

theorem spec_cmp {k d : Nat} {op : Cmp} {a b : Tm} (ha : Spec P host p k d a)
    (hb : Spec P host p k d b) : Spec P host p (k + 1) d (.cmp op a b) := by
  intro ρ v hv s f hf hfn hd hr hfx us rest Q hk
  obtain ⟨x, y, hxa, hyb, rfl⟩ := eval_cmp_inv hv
  show TWP P host s f (vals us ++ (expression (compile p.table d a ++ unbox ++
    compile p.table d b ++ unbox ++ [.intRelOp .i32 (FunCompile.Cmp.wasm op), .refI31]) ++
    rest)) Q
  simp only [List.append_assoc, expr_append]
  refine ha ρ _ hxa s f hf hfn (depth_left hd) hr (sub_left hfx) us _ Q
    (Cont.unboxInt fun s₁ f₁ hs₁ hf₁ => ?_)
  have hdb : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  refine hb ρ _ hyb s₁ f₁ (hf.of_agree hf₁) (hs₁.funcs hfn) hdb (hr.of_agree hs₁.1 hf₁)
    (sub_right hfx) _ _ Q (Cont.unboxInt fun s₂ f₂ hs₂ hf₂ => ?_)
  exact twp_cmpTail hk (hs₁.trans hs₂) (hf₁.trans hf₂)

/-! ## Blocks -/

/-- The code of a term inside a block of result `anyref`. -/
theorem twp_inBlock {k d : Nat} {e : Tm} (hsp : Spec P host p k d e) {ρ : List FunClo.Val}
    {v : FunClo.Val} (hv : eval k ρ e = some v) {s : Store Nat} {f : Frame} (hf : FOK f)
    (hfn : s.funcs[1]? = some (applyInst p)) (hd : d + e.depth < f.locals.length)
    (hr : EnvRep p.table s f d ρ) (hfx : ∀ x ∈ e.fixes d, x ∈ p.table) {us : List Val}
    {rest : List Admin} {Q : Post Nat} (hk : Cont P host p.table d s f v us rest Q) :
    TWP P host s f (vals [] ++ expression (compile p.table d e))
      (labelPostT P host 1 [] us (seqPostT P host rest Q)) := by
  have h' := hsp ρ v hv s f hf hfn hd hr hfx [] []
    (labelPostT P host 1 [] us (seqPostT P host rest Q))
    fun s' f' w hs hag hw => Wp.of_vals (m := .total) (vs := [w]) (hk s' f' w hs hag hw)
  simpa using h'

theorem spec_ite {k d : Nat} {c t e : Tm} (hc : Spec P host p k d c) (ht : Spec P host p k d t)
    (he : Spec P host p k d e) : Spec P host p (k + 1) d (.ite c t e) := by
  intro ρ v hv s f hf hfn hd hr hfx us rest Q hk
  obtain ⟨b, hcb, hbr⟩ := eval_ite_inv hv
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
  refine hc ρ _ hcb s f hf hfn (depth_left hd) hr (sub_left (sub_left hfx')) us _ Q
    (Cont.unboxBool fun s₁ f₁ hs₁ hf₁ => ?_)
  refine twp_ifBlock ?_
  rw [hsel]
  exact twp_inBlock hsp hbr (hf.of_agree hf₁) (hs₁.funcs hfn) (hf₁.2.1 ▸ hdb)
    (hr.of_agree hs₁.1 hf₁) hfb (hk.later hs₁ hf₁)

/-! ## Binders -/

theorem spec_let {k d : Nat} {a b : Tm} (ha : Spec P host p k d a)
    (hb : Spec P host p k (d + 1) b) : Spec P host p (k + 1) d (.let_ a b) := by
  intro ρ v hv s f hf hfn hd hr hfx us rest Q hk
  obtain ⟨u, hu, hbv⟩ := eval_let_inv hv
  have hfx' : ∀ x ∈ a.fixes d ++ b.fixes (d + 1), x ∈ p.table := hfx
  have hdb : d + 1 + b.depth < f.locals.length := depth_succ (depth_right hd)
  have hlt : d + 1 < f.locals.length := by omega
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.1 hlt
  show TWP P host s f (vals us ++ (expression (compile p.table d a ++
    .localSet (lx (d + 1)) :: compile p.table (d + 1) b) ++ rest)) Q
  rw [expr_append]
  refine ha ρ u hu s f hf hfn (depth_left hd) hr (sub_left hfx') us _ Q
    fun s₁ f₁ w hs₁ hf₁ hw => ?_
  have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
  refine twp_localSet (hf.of_agree hf₁).1 hlt₁ ?_
  refine hb (u :: ρ) v hbv s₁ _ ((hf.of_agree hf₁).setLocal _ w) (hs₁.funcs hfn)
    (by rw [len_setLocal, hf₁.2.1]; exact hdb) ((hr.of_agree hs₁.1 hf₁).cons hw hlt₁ hlim)
    (sub_right hfx') us rest Q fun s₂ f₂ w₂ hs₂ hf₂ hw₂ => ?_
  exact hk s₂ f₂ w₂ (hs₁.trans hs₂) (hf₁.trans ((Agree.setLocal w hlim).trans hf₂.of_succ)) hw₂

/-! ## Pairs and injections -/

theorem spec_pair {k d : Nat} {a b : Tm} (ha : Spec P host p k d a)
    (hb : Spec P host p k d b) : Spec P host p (k + 1) d (.pair a b) := by
  intro ρ v hv s f hf hfn hd hr hfx us rest Q hk
  obtain ⟨x, y, hxa, hyb, rfl⟩ := eval_pair_inv hv
  show TWP P host s f (vals us ++ (expression (compile p.table d a ++ compile p.table d b ++
    [.structNew boxIdx]) ++ rest)) Q
  simp only [List.append_assoc, expr_append]
  refine ha ρ _ hxa s f hf hfn (depth_left hd) hr (sub_left hfx) us _ Q
    fun s₁ f₁ wa hs₁ hf₁ hwa => ?_
  have hdb : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  refine hb ρ _ hyb s₁ f₁ (hf.of_agree hf₁) (hs₁.funcs hfn) hdb (hr.of_agree hs₁.1 hf₁)
    (sub_right hfx) _ _ Q fun s₂ f₂ wb hs₂ hf₂ hwb => ?_
  rw [vals_pair]
  refine twp_newBox (hf.of_agree (hf₁.trans hf₂)).1 ?_
  have hp := addStruct_prefix s₂ ⟨dBox, [.val wa, .val wb]⟩
  exact hk _ f₂ _ ((hs₁.trans hs₂).trans (Ext.addStruct _ _)) (hf₁.trans hf₂)
    ⟨s₂.structs.length, wa, wb, rfl, addStruct_get _ _, (hwa.mono hs₂.1).mono hp, hwb.mono hp⟩

theorem spec_fst {k d : Nat} {e : Tm} (he : Spec P host p k d e) :
    Spec P host p (k + 1) d (.fst e) := by
  intro ρ v hv s f hf hfn hd hr hfx us rest Q hk
  obtain ⟨y, hev⟩ := eval_fst_inv hv
  show TWP P host s f (vals us ++ (expression (compile p.table d e ++
    [.refCast boxRef, .structGet none boxIdx (fx 0)]) ++ rest)) Q
  rw [expr_append]
  refine he ρ _ hev s f hf hfn hd hr hfx us _ Q fun s₁ f₁ w hs₁ hf₁ hw => ?_
  obtain ⟨addr, wa, wb, hw', hst, hwa, -⟩ := hw
  rw [hw']
  have hf₁' : FrameOK f₁ := (hf.of_agree hf₁).1
  exact twp_castBox hf₁' hst (twp_getBox hf₁' (by omega) hst (hk s₁ f₁ wa hs₁ hf₁ hwa))

theorem spec_snd {k d : Nat} {e : Tm} (he : Spec P host p k d e) :
    Spec P host p (k + 1) d (.snd e) := by
  intro ρ v hv s f hf hfn hd hr hfx us rest Q hk
  obtain ⟨x, hev⟩ := eval_snd_inv hv
  show TWP P host s f (vals us ++ (expression (compile p.table d e ++
    [.refCast boxRef, .structGet none boxIdx (fx 1)]) ++ rest)) Q
  rw [expr_append]
  refine he ρ _ hev s f hf hfn hd hr hfx us _ Q fun s₁ f₁ w hs₁ hf₁ hw => ?_
  obtain ⟨addr, wa, wb, hw', hst, -, hwb⟩ := hw
  rw [hw']
  have hf₁' : FrameOK f₁ := (hf.of_agree hf₁).1
  exact twp_castBox hf₁' hst (twp_getBox hf₁' (by omega) hst (hk s₁ f₁ wb hs₁ hf₁ hwb))

/-- The value of an injection with tag `0` (`inl`) or `1` (`inr`). -/
def inj (tag : BitVec 31) (u : FunClo.Val) : FunClo.Val := if tag = 0 then .inl u else .inr u

theorem rep_inj {s : Store Nat} {tag : BitVec 31} (ht : tag = 0 ∨ tag = 1) {u : FunClo.Val}
    {wv : Val} {addr : Nat}
    (hst : s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 tag)), .val wv]⟩)
    (hu : Rep p.table s u wv) : Rep p.table s (inj tag u) (.ref (.struct addr)) := by
  rcases ht with rfl | rfl
  · exact ⟨addr, wv, rfl, hst, hu⟩
  · exact ⟨addr, wv, rfl, hst, hu⟩

theorem spec_injTag {k d : Nat} {e : Tm} {tag : BitVec 31} (ht : tag = 0 ∨ tag = 1)
    (he : Spec P host p k d e) {ρ : List FunClo.Val} {u : FunClo.Val}
    (hev : eval k ρ e = some u) {s : Store Nat} {f : Frame} (hf : FOK f)
    (hfn : s.funcs[1]? = some (applyInst p)) (hd : d + e.depth < f.locals.length)
    (hr : EnvRep p.table s f d ρ) (hfx : ∀ x ∈ e.fixes d, x ∈ p.table) {us : List Val}
    {rest : List Admin} {Q : Post Nat} (hk : Cont P host p.table d s f (inj tag u) us rest Q) :
    TWP P host s f (vals us ++ (expression (.intConst .i32 (tag.setWidth 32) :: .refI31 ::
      compile p.table d e ++ [.structNew boxIdx]) ++ rest)) Q := by
  show TWP P host s f (vals us ++ (expression [.intConst .i32 (tag.setWidth 32), .refI31] ++
    (expression (compile p.table d e ++ [.structNew boxIdx]) ++ rest))) Q
  refine twp_constBox ?_
  rw [expr_append, setWidth_31_32]
  refine he ρ u hev s f hf hfn hd hr hfx _ _ Q fun s₁ f₁ w hs₁ hf₁ hw => ?_
  rw [vals_pair]
  refine twp_newBox (hf.of_agree hf₁).1 ?_
  have hp := addStruct_prefix s₁ ⟨dBox, [.val (.ref (.i31 tag)), .val w]⟩
  exact hk _ f₁ _ (hs₁.trans (Ext.addStruct _ _)) hf₁ (rep_inj ht (addStruct_get _ _) (hw.mono hp))

theorem spec_inl {k d : Nat} {e : Tm} (he : Spec P host p k d e) :
    Spec P host p (k + 1) d (.inl e) := by
  intro ρ v hv s f hf hfn hd hr hfx us rest Q hk
  obtain ⟨u, hev, rfl⟩ := eval_inl_inv hv
  exact spec_injTag (tag := 0) (.inl rfl) he hev hf hfn hd hr hfx hk

theorem spec_inr {k d : Nat} {e : Tm} (he : Spec P host p k d e) :
    Spec P host p (k + 1) d (.inr e) := by
  intro ρ v hv s f hf hfn hd hr hfx us rest Q hk
  obtain ⟨u, hev, rfl⟩ := eval_inr_inv hv
  exact spec_injTag (tag := 1) (.inr rfl) he hev hf hfn hd hr hfx hk

/-! ## `case` -/

/-- The code of a `case` branch: read the payload into local `d + 1`, then the branch. -/
def branch (L : List (Nat × Tm)) (d : Nat) (t : Tm) : List Instr :=
  getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile L (d + 1) t

theorem twp_branch {k d : Nat} {t : Tm} (hsp : Spec P host p k (d + 1) t)
    {ρ : List FunClo.Val} {u v : FunClo.Val} (hev : eval k (u :: ρ) t = some v) {s : Store Nat}
    {f : Frame} (hf : FOK f) (hfn : s.funcs[1]? = some (applyInst p))
    (hd : d + 1 + t.depth < f.locals.length) (hr : EnvRep p.table s f d ρ)
    (hfx : ∀ x ∈ t.fixes (d + 1), x ∈ p.table) {addr : Nat} {tagw wv : Val}
    (hloc : f.locals[d + 1]? = some (some (.ref (.struct addr))))
    (hst : s.structs[addr]? = some ⟨dBox, [.val tagw, .val wv]⟩) (hu : Rep p.table s u wv)
    {us : List Val} {rest : List Admin} {Q : Post Nat}
    (hk : Cont P host p.table d s f v us rest Q) :
    TWP P host s f (vals [] ++ expression (branch p.table d t))
      (labelPostT P host 1 [] us (seqPostT P host rest Q)) := by
  have hlt : d + 1 < f.locals.length := by omega
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf.1 hlt
  show TWP P host s f (vals [] ++ .plain (.localGet (lx (d + 1))) :: .plain (.refCast boxRef) ::
    .plain (.structGet none boxIdx (fx 1)) :: .plain (.localSet (lx (d + 1))) ::
    expression (compile p.table (d + 1) t)) _
  refine twp_localGet hf.1 hloc (twp_castBox hf.1 hst (twp_getBox hf.1 (by omega) hst
    (twp_localSet (w := wv) hf.1 hlt ?_)))
  have hk' : Cont P host p.table (d + 1) s (f.setLocal (lx (d + 1)) wv) v [] []
      (labelPostT P host 1 [] us (seqPostT P host rest Q)) :=
    fun s' f' w hs hag hw => Wp.of_vals (m := .total) (vs := [w])
      (hk s' f' w hs ((Agree.setLocal wv hlim).trans hag.of_succ) hw)
  have h' := hsp (u :: ρ) v hev s _ (hf.setLocal _ wv) hfn (by rw [len_setLocal]; exact hd)
    (hr.cons hu hlt hlim) hfx [] [] _ hk'
  simpa using h'

theorem spec_case {k d : Nat} {e l r : Tm} (he : Spec P host p k d e)
    (hl : Spec P host p k (d + 1) l) (hr' : Spec P host p k (d + 1) r) :
    Spec P host p (k + 1) d (.case e l r) := by
  intro ρ v hv s f hf hfn hd hr hfx us rest Q hk
  have hfx' : ∀ x ∈ e.fixes d ++ l.fixes (d + 1) ++ r.fixes (d + 1), x ∈ p.table := hfx
  have hdlr : d + 1 + max l.depth r.depth < f.locals.length := depth_succ (depth_right hd)
  have hdl : d + 1 + l.depth < f.locals.length := depth_left hdlr
  have hdr : d + 1 + r.depth < f.locals.length := depth_right hdlr
  have hlt : d + 1 < f.locals.length := by omega
  show TWP P host s f (vals us ++ (expression (compile p.table d e ++ .localSet (lx (d + 1)) ::
    getField (d + 1) 0 ++ unbox ++ [.if_ (.value anyref) (branch p.table d r)
      (branch p.table d l)]) ++ rest)) Q
  simp only [List.append_assoc]
  rw [expr_append]
  rcases eval_case_inv hv with ⟨u, hev, hbv⟩ | ⟨u, hev, hbv⟩
  · show TWP P host s f (vals us ++ (expression (compile p.table d e) ++ _)) Q
    refine he ρ _ hev s f hf hfn (depth_left hd) hr (sub_left (sub_left hfx')) us _ Q
      fun s₁ f₁ w hs₁ hf₁ hw => ?_
    obtain ⟨addr, wv, hw', hst, hu⟩ := hw
    have hf₁' : FOK f₁ := hf.of_agree hf₁
    have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
    rw [hw']
    refine twp_caseTail hf₁'.1 hlt₁ hst ?_
    exact twp_branch hl hbv (hf₁'.setLocal _ _) (hs₁.funcs hfn)
      (by rw [len_setLocal, hf₁.2.1]; exact hdl)
      ((hr.of_agree hs₁.1 hf₁).of_agree (List.prefix_refl _)
        (Agree.setLocal _ (lt_lim hf.1 hlt)))
      (sub_right (sub_left hfx')) (setLocal_get _ hlt₁ (lt_lim hf.1 hlt)) hst hu
      ((hk.later hs₁ hf₁).later (Ext.refl _) (Agree.setLocal _ (lt_lim hf.1 hlt)))
  · show TWP P host s f (vals us ++ (expression (compile p.table d e) ++ _)) Q
    refine he ρ _ hev s f hf hfn (depth_left hd) hr (sub_left (sub_left hfx')) us _ Q
      fun s₁ f₁ w hs₁ hf₁ hw => ?_
    obtain ⟨addr, wv, hw', hst, hu⟩ := hw
    have hf₁' : FOK f₁ := hf.of_agree hf₁
    have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
    rw [hw']
    refine twp_caseTail hf₁'.1 hlt₁ hst ?_
    exact twp_branch hr' hbv (hf₁'.setLocal _ _) (hs₁.funcs hfn)
      (by rw [len_setLocal, hf₁.2.1]; exact hdr)
      ((hr.of_agree hs₁.1 hf₁).of_agree (List.prefix_refl _)
        (Agree.setLocal _ (lt_lim hf.1 hlt)))
      (sub_right hfx') (setLocal_get _ hlt₁ (lt_lim hf.1 hlt)) hst hu
      ((hk.later hs₁ hf₁).later (Ext.refl _) (Agree.setLocal _ (lt_lim hf.1 hlt)))

end Silmaril.Proofs.Wasm.Models.FunCloCompile
