module

public import Silmaril.Proofs.Wasm.Models.FunCompile.Rep

/-!
# Compiling FunLang: correctness of the code of each construct

`Spec P host d e` for every constructor of `Tm`, from `Spec` of its subterms (`spec_var` …
`spec_case`), and **`spec_compile`**: the code of every term is correct, by induction on the term.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunLang (Tm eval Arith Cmp)
open Silmaril.Wasm.Logic.Core (Post)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Inversion of evaluation -/

theorem eval_arith_inv {ρ : List FunLang.Val} {op : Arith} {a b : Tm} {v : FunLang.Val}
    (h : eval ρ (.arith op a b) = some v) :
    ∃ x y, eval ρ a = some (.int x) ∧ eval ρ b = some (.int y) ∧ v = .int (op.eval x y) := by
  simp only [eval] at h
  split at h
  · next x y ha hb => exact ⟨x, y, ha, hb, (Option.some.inj h).symm⟩
  · cases h

theorem eval_cmp_inv {ρ : List FunLang.Val} {op : Cmp} {a b : Tm} {v : FunLang.Val}
    (h : eval ρ (.cmp op a b) = some v) :
    ∃ x y, eval ρ a = some (.int x) ∧ eval ρ b = some (.int y) ∧ v = .bool (op.eval x y) := by
  simp only [eval] at h
  split at h
  · next x y ha hb => exact ⟨x, y, ha, hb, (Option.some.inj h).symm⟩
  · cases h

theorem eval_ite_inv {ρ : List FunLang.Val} {c t e : Tm} {v : FunLang.Val}
    (h : eval ρ (.ite c t e) = some v) :
    ∃ b, eval ρ c = some (.bool b) ∧ eval ρ (if b then t else e) = some v := by
  simp only [eval] at h
  split at h
  · next hc => exact ⟨true, hc, h⟩
  · next hc => exact ⟨false, hc, h⟩
  · cases h

theorem eval_let_inv {ρ : List FunLang.Val} {a b : Tm} {v : FunLang.Val}
    (h : eval ρ (.let_ a b) = some v) : ∃ u, eval ρ a = some u ∧ eval (u :: ρ) b = some v := by
  simp only [eval] at h
  split at h
  · next u hu => exact ⟨u, hu, h⟩
  · cases h

theorem eval_pair_inv {ρ : List FunLang.Val} {a b : Tm} {v : FunLang.Val}
    (h : eval ρ (.pair a b) = some v) :
    ∃ x y, eval ρ a = some x ∧ eval ρ b = some y ∧ v = .pair x y := by
  simp only [eval] at h
  split at h
  · next x y ha hb => exact ⟨x, y, ha, hb, (Option.some.inj h).symm⟩
  · cases h

theorem eval_fst_inv {ρ : List FunLang.Val} {e : Tm} {v : FunLang.Val}
    (h : eval ρ (.fst e) = some v) : ∃ y, eval ρ e = some (.pair v y) := by
  simp only [eval] at h
  split at h
  · next x y he => exact ⟨y, (Option.some.inj h) ▸ he⟩
  · cases h

theorem eval_snd_inv {ρ : List FunLang.Val} {e : Tm} {v : FunLang.Val}
    (h : eval ρ (.snd e) = some v) : ∃ x, eval ρ e = some (.pair x v) := by
  simp only [eval] at h
  split at h
  · next x y he => exact ⟨x, (Option.some.inj h) ▸ he⟩
  · cases h

theorem eval_inl_inv {ρ : List FunLang.Val} {e : Tm} {v : FunLang.Val}
    (h : eval ρ (.inl e) = some v) : ∃ u, eval ρ e = some u ∧ v = .inl u := by
  simp only [eval, Option.map_eq_some_iff] at h
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨u, hu, rfl⟩

theorem eval_inr_inv {ρ : List FunLang.Val} {e : Tm} {v : FunLang.Val}
    (h : eval ρ (.inr e) = some v) : ∃ u, eval ρ e = some u ∧ v = .inr u := by
  simp only [eval, Option.map_eq_some_iff] at h
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨u, hu, rfl⟩

theorem eval_case_inv {ρ : List FunLang.Val} {e l r : Tm} {v : FunLang.Val}
    (h : eval ρ (.case e l r) = some v) :
    (∃ u, eval ρ e = some (.inl u) ∧ eval (u :: ρ) l = some v) ∨
      (∃ u, eval ρ e = some (.inr u) ∧ eval (u :: ρ) r = some v) := by
  simp only [eval] at h
  split at h
  · next u hu => exact .inl ⟨u, hu, h⟩
  · next u hu => exact .inr ⟨u, hu, h⟩
  · cases h

/-! ## Word arithmetic -/

theorem setWidth_31_32 (n : BitVec 31) : (n.setWidth 32).setWidth 31 = n := by simp

theorem arith_wasm (op : Arith) (x y : BitVec 31) :
    ∃ z : BitVec 32,
      Numerics.intBinOp .i32 (Arith.wasm op) (x.setWidth 32) (y.setWidth 32) = .ok z ∧
      z.setWidth 31 = op.eval x y := by
  cases op with
  | add =>
    refine ⟨x.setWidth 32 + y.setWidth 32, rfl, ?_⟩
    rw [BitVec.setWidth_add _ _ (by omega)]
    simp [Arith.eval]
  | sub =>
    refine ⟨x.setWidth 32 - y.setWidth 32, rfl, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp [Arith.eval, BitVec.toNat_sub]
    omega
  | mul =>
    refine ⟨x.setWidth 32 * y.setWidth 32, rfl, ?_⟩
    rw [BitVec.setWidth_mul _ _ (by omega)]
    simp [Arith.eval]

theorem setWidth_inj {x y : BitVec 31} (h : x.setWidth 32 = y.setWidth 32) : x = y := by
  have h' : (x.setWidth 32).setWidth 31 = (y.setWidth 32).setWidth 31 := by rw [h]
  simpa using h'

theorem toNat_setWidth32 (x : BitVec 31) : (x.setWidth 32).toNat = x.toNat := by
  simp [BitVec.toNat_setWidth]; omega

theorem cmp_wasm (op : Cmp) (x y : BitVec 31) :
    Numerics.intRelOp .i32 (Cmp.wasm op) (x.setWidth 32) (y.setWidth 32) =
      Numerics.bool32 (op.eval x y) := by
  cases op with
  | eq =>
    have h : (x.setWidth 32 == y.setWidth 32) = decide (x = y) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
      exact ⟨setWidth_inj, fun h => h ▸ rfl⟩
    exact congrArg Numerics.bool32 h
  | ltu =>
    have h : decide ((x.setWidth 32).toNat < (y.setWidth 32).toNat) = decide (x < y) := by
      rw [toNat_setWidth32, toNat_setWidth32]
      exact decide_eq_decide.2 BitVec.lt_def.symm
    exact congrArg Numerics.bool32 h

theorem bool32_31 (b : Bool) : (Numerics.bool32 b).setWidth 31 = if b then 1 else 0 := by
  cases b <;> rfl

theorem bit_ne_zero (b : Bool) :
    ((if b then (1 : BitVec 31) else 0).setWidth 32 ≠ 0) = (b = true) := by
  cases b <;> decide

/-! ## Continuations through unboxing -/

theorem Cont.unboxInt {d : Nat} {s : Store H} {f : Frame} {x : BitVec 31} {us : List Val}
    {rest : List Admin} {Q : Post H}
    (h : ∀ s' f', s.structs <+: s'.structs → Agree d f f' →
      TWP P host s' f' (vals (us ++ [.i32 (x.setWidth 32)]) ++ rest) Q) :
    Cont P host d s f (.int x) us (expression unbox ++ rest) Q := by
  intro s' f' w hs hf hw
  have hw' : w = .ref (.i31 x) := hw
  rw [hw']
  exact twp_unbox (h s' f' hs hf)

theorem Cont.unboxBool {d : Nat} {s : Store H} {f : Frame} {b : Bool} {us : List Val}
    {rest : List Admin} {Q : Post H}
    (h : ∀ s' f', s.structs <+: s'.structs → Agree d f f' →
      TWP P host s' f'
        (vals (us ++ [.i32 ((if b then (1 : BitVec 31) else 0).setWidth 32)]) ++ rest) Q) :
    Cont P host d s f (.bool b) us (expression unbox ++ rest) Q := by
  intro s' f' w hs hf hw
  have hw' : w = .ref (.i31 (if b then 1 else 0)) := hw
  rw [hw']
  exact twp_unbox (h s' f' hs hf)

/-! ## Depth bounds -/

theorem depth_left {d a b len : Nat} (h : d + max a b < len) : d + a < len :=
  lt_of_le_of_lt (Nat.add_le_add_left (le_max_left _ _) d) h

theorem depth_right {d a b len : Nat} (h : d + max a b < len) : d + b < len :=
  lt_of_le_of_lt (Nat.add_le_add_left (le_max_right _ _) d) h

theorem depth_succ {d a len : Nat} (h : d + (a + 1) < len) : d + 1 + a < len := by omega

/-! ## Leaves -/

theorem spec_var (d i : Nat) : Spec (H := H) P host d (.var i) := by
  intro ρ v hv s f hf _ hr us rest Q hk
  obtain ⟨w, hw, hrep⟩ := hr.2 i v hv
  exact twp_localGet hf hw (hk s f w (List.prefix_refl _) (Agree.refl d f) hrep)

/-- `i32.const k; ref.i31`. -/
theorem twp_constBox {s : Store H} {f : Frame} {us : List Val} {rest : List Admin} {Q : Post H}
    {k : BitVec 32} (h : TWP P host s f (vals (us ++ [.ref (.i31 (k.setWidth 31))]) ++ rest) Q) :
    TWP P host s f (vals us ++ (expression [.intConst .i32 k, .refI31] ++ rest)) Q := by
  have he : vals us ++ (expression [.intConst .i32 k, .refI31] ++ rest) =
      vals (us ++ [.i32 k]) ++ .plain .refI31 :: rest :=
    vals_snoc_const us k (.plain .refI31 :: rest)
  rw [he]
  exact twp_box h

theorem spec_int (d : Nat) (n : BitVec 31) : Spec (H := H) P host d (.int n) := by
  intro ρ v hv s f _ _ _ us rest Q hk
  have hv' : v = .int n := (Option.some.inj hv).symm
  have hw : Rep s v (.ref (.i31 ((n.setWidth 32).setWidth 31))) := by rw [hv', setWidth_31_32]; rfl
  exact twp_constBox (hk s f _ (List.prefix_refl _) (Agree.refl d f) hw)

theorem spec_bool (d : Nat) (b : Bool) : Spec (H := H) P host d (.bool b) := by
  intro ρ v hv s f _ _ _ us rest Q hk
  have hv' : v = .bool b := (Option.some.inj hv).symm
  have hw : Rep s v (.ref (.i31 ((if b then (1 : BitVec 32) else 0).setWidth 31))) := by
    rw [hv']; cases b <;> rfl
  exact twp_constBox (hk s f _ (List.prefix_refl _) (Agree.refl d f) hw)

/-! ## Frames after `local.set` -/

theorem len_setLocal (f : Frame) (x : LocalIdx) (w : Val) :
    (f.setLocal x w).locals.length = f.locals.length := by
  simp [Frame.setLocal]

theorem FrameOK.setLocal {f : Frame} (hf : FrameOK f) (x : LocalIdx) (w : Val) :
    FrameOK (f.setLocal x w) :=
  ⟨hf.1, (len_setLocal f x w).symm ▸ hf.2⟩

theorem setLocal_get {f : Frame} {x : Nat} (w : Val) (hx : x < f.locals.length)
    (hlim : x < 2 ^ 32) : (f.setLocal (lx x) w).locals[x]? = some (some w) := by
  have hn : (lx x).toNat = x := by simp [lx, Idx.toNat]; exact hlim
  simp [Frame.setLocal, hn, hx]

theorem lt_lim {f : Frame} (hf : FrameOK f) {x : Nat} (hx : x < f.locals.length) : x < 2 ^ 32 :=
  lt_of_lt_of_le hx hf.2

/-! ## Arithmetic and comparisons -/

theorem vals_pair (us : List Val) (a b : Val) :
    vals ((us ++ [a]) ++ [b]) = vals (us ++ [a, b]) := by
  simp

theorem twp_arithTail {d : Nat} {s s₂ : Store H} {f f₂ : Frame} {op : Arith} {x y : BitVec 31}
    {us : List Val} {rest : List Admin} {Q : Post H}
    (hk : Cont P host d s f (.int (op.eval x y)) us rest Q) (hs : s.structs <+: s₂.structs)
    (hf : Agree d f f₂) :
    TWP P host s₂ f₂ (vals ((us ++ [.i32 (x.setWidth 32)]) ++ [.i32 (y.setWidth 32)]) ++
      (expression [.intBinOp .i32 (Arith.wasm op), .refI31] ++ rest)) Q := by
  obtain ⟨z, hz, hzw⟩ := arith_wasm op x y
  have hrep : Rep s₂ (.int (op.eval x y)) (.ref (.i31 (z.setWidth 31))) := by
    show Val.ref (.i31 (z.setWidth 31)) = .ref (.i31 (op.eval x y))
    rw [hzw]
  rw [vals_pair]
  exact Wp.intBinOp (m := .total) hz (twp_box (hk s₂ f₂ _ hs hf hrep))

theorem twp_cmpTail {d : Nat} {s s₂ : Store H} {f f₂ : Frame} {op : Cmp} {x y : BitVec 31}
    {us : List Val} {rest : List Admin} {Q : Post H}
    (hk : Cont P host d s f (.bool (op.eval x y)) us rest Q) (hs : s.structs <+: s₂.structs)
    (hf : Agree d f f₂) :
    TWP P host s₂ f₂ (vals ((us ++ [.i32 (x.setWidth 32)]) ++ [.i32 (y.setWidth 32)]) ++
      (expression [.intRelOp .i32 (Cmp.wasm op), .refI31] ++ rest)) Q := by
  have hrep : Rep s₂ (.bool (op.eval x y))
      (.ref (.i31
        ((Numerics.intRelOp .i32 (Cmp.wasm op) (x.setWidth 32) (y.setWidth 32)).setWidth 31))) := by
    show Val.ref (.i31 _) = .ref (.i31 (if op.eval x y then 1 else 0))
    rw [cmp_wasm, bool32_31]
  rw [vals_pair]
  exact Wp.intRelOp (m := .total) (twp_box (hk s₂ f₂ _ hs hf hrep))

theorem spec_arith {d : Nat} {op : Arith} {a b : Tm} (ha : Spec P host d a)
    (hb : Spec P host d b) : Spec (H := H) P host d (.arith op a b) := by
  intro ρ v hv s f hf hd hr us rest Q hk
  obtain ⟨x, y, hxa, hyb, rfl⟩ := eval_arith_inv hv
  show TWP P host s f (vals us ++ (expression (compile d a ++ unbox ++ compile d b ++ unbox ++
    [.intBinOp .i32 (Arith.wasm op), .refI31]) ++ rest)) Q
  simp only [List.append_assoc, expr_append]
  refine ha ρ _ hxa s f hf (depth_left hd) hr us _ Q (Cont.unboxInt fun s₁ f₁ hs₁ hf₁ => ?_)
  have hdb : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  refine hb ρ _ hyb s₁ f₁ (hf.of_agree hf₁) hdb (hr.of_agree hs₁ hf₁) _ _ Q
    (Cont.unboxInt fun s₂ f₂ hs₂ hf₂ => ?_)
  exact twp_arithTail hk (hs₁.trans hs₂) (hf₁.trans hf₂)

theorem spec_cmp {d : Nat} {op : Cmp} {a b : Tm} (ha : Spec P host d a)
    (hb : Spec P host d b) : Spec (H := H) P host d (.cmp op a b) := by
  intro ρ v hv s f hf hd hr us rest Q hk
  obtain ⟨x, y, hxa, hyb, rfl⟩ := eval_cmp_inv hv
  show TWP P host s f (vals us ++ (expression (compile d a ++ unbox ++ compile d b ++ unbox ++
    [.intRelOp .i32 (Cmp.wasm op), .refI31]) ++ rest)) Q
  simp only [List.append_assoc, expr_append]
  refine ha ρ _ hxa s f hf (depth_left hd) hr us _ Q (Cont.unboxInt fun s₁ f₁ hs₁ hf₁ => ?_)
  have hdb : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  refine hb ρ _ hyb s₁ f₁ (hf.of_agree hf₁) hdb (hr.of_agree hs₁ hf₁) _ _ Q
    (Cont.unboxInt fun s₂ f₂ hs₂ hf₂ => ?_)
  exact twp_cmpTail hk (hs₁.trans hs₂) (hf₁.trans hf₂)

/-! ## Blocks -/

/-- `if (result anyref)` on `c`: the selected branch runs in a block. -/
theorem twp_ifBlock {s : Store H} {f : Frame} {us : List Val} {rest : List Admin} {Q : Post H}
    {c : BitVec 32} {b₁ b₂ : List Instr}
    (h : TWP P host s f (vals [] ++ expression (if c ≠ 0 then b₁ else b₂))
      (labelPostT P host 1 [] us (seqPostT P host rest Q))) :
    TWP P host s f (vals (us ++ [.i32 c]) ++ .plain (.if_ (.value anyref) b₁ b₂) :: rest) Q := by
  refine TWP.if_ ?_
  have hb := TWP.block (us := us) (vs := []) (rest := rest) (Q := Q) (bt := .value anyref)
    (body := if c ≠ 0 then b₁ else b₂) (t₁ := []) (t₂ := [f.module.instVal anyref]) rfl rfl h
  simpa using hb

/-- The code of a term inside a block of result `anyref`. -/
theorem twp_inBlock {d : Nat} {e : Tm} (hsp : Spec P host d e) {ρ : List FunLang.Val}
    {v : FunLang.Val} (hv : eval ρ e = some v) {s : Store H} {f : Frame} (hf : FrameOK f)
    (hd : d + e.depth < f.locals.length) (hr : EnvRep s f d ρ) {us : List Val}
    {rest : List Admin} {Q : Post H} (hk : Cont P host d s f v us rest Q) :
    TWP P host s f (vals [] ++ expression (compile d e))
      (labelPostT P host 1 [] us (seqPostT P host rest Q)) := by
  have h' := hsp ρ v hv s f hf hd hr [] [] (labelPostT P host 1 [] us (seqPostT P host rest Q))
    fun s' f' w hs hag hw => Wp.of_vals (m := .total) (vs := [w]) (hk s' f' w hs hag hw)
  simpa using h'

theorem spec_ite {d : Nat} {c t e : Tm} (hc : Spec P host d c) (ht : Spec P host d t)
    (he : Spec P host d e) : Spec (H := H) P host d (.ite c t e) := by
  intro ρ v hv s f hf hd hr us rest Q hk
  obtain ⟨b, hcb, hbr⟩ := eval_ite_inv hv
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
  refine hc ρ _ hcb s f hf (depth_left hd) hr us _ Q (Cont.unboxBool fun s₁ f₁ hs₁ hf₁ => ?_)
  refine twp_ifBlock ?_
  rw [hsel]
  exact twp_inBlock hsp hbr (hf.of_agree hf₁) (hf₁.2.1 ▸ hdb) (hr.of_agree hs₁ hf₁)
    (hk.later hs₁ hf₁)

/-! ## Binders -/

theorem spec_let {d : Nat} {a b : Tm} (ha : Spec P host d a) (hb : Spec P host (d + 1) b) :
    Spec (H := H) P host d (.let_ a b) := by
  intro ρ v hv s f hf hd hr us rest Q hk
  obtain ⟨u, hu, hbv⟩ := eval_let_inv hv
  have hdb : d + 1 + b.depth < f.locals.length := depth_succ (depth_right hd)
  have hlt : d + 1 < f.locals.length := by omega
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf hlt
  show TWP P host s f (vals us ++ (expression (compile d a ++
    .localSet (lx (d + 1)) :: compile (d + 1) b) ++ rest)) Q
  rw [expr_append]
  refine ha ρ u hu s f hf (depth_left hd) hr us _ Q fun s₁ f₁ w hs₁ hf₁ hw => ?_
  have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
  refine twp_localSet (hf.of_agree hf₁) hlt₁ ?_
  refine hb (u :: ρ) v hbv s₁ _ ((hf.of_agree hf₁).setLocal _ w)
    (by rw [len_setLocal, hf₁.2.1]; exact hdb) ((hr.of_agree hs₁ hf₁).cons hw hlt₁ hlim) us rest Q
    fun s₂ f₂ w₂ hs₂ hf₂ hw₂ => ?_
  exact hk s₂ f₂ w₂ (hs₁.trans hs₂) (hf₁.trans ((Agree.setLocal w hlim).trans hf₂.of_succ)) hw₂

/-! ## Pairs -/

theorem twp_pairTail {d : Nat} {s s₁ s₂ : Store H} {f f₂ : Frame} (hf₂ : FrameOK f₂)
    {x y : FunLang.Val} {wa wb : Val} {us : List Val} {rest : List Admin} {Q : Post H}
    (hk : Cont P host d s f (.pair x y) us rest Q) (hs₁ : s.structs <+: s₁.structs)
    (hs₂ : s₁.structs <+: s₂.structs) (hag : Agree d f f₂) (hwa : Rep s₁ x wa)
    (hwb : Rep s₂ y wb) :
    TWP P host s₂ f₂ (vals ((us ++ [wa]) ++ [wb]) ++
      (expression [.structNew boxIdx] ++ rest)) Q := by
  rw [vals_pair]
  refine twp_newBox hf₂ ?_
  have hp := addStruct_prefix s₂ ⟨dBox, [.val wa, .val wb]⟩
  exact hk _ f₂ _ ((hs₁.trans hs₂).trans hp) hag
    ⟨s₂.structs.length, wa, wb, rfl, addStruct_get _ _, (hwa.mono hs₂).mono hp, hwb.mono hp⟩

theorem spec_pair {d : Nat} {a b : Tm} (ha : Spec P host d a) (hb : Spec P host d b) :
    Spec (H := H) P host d (.pair a b) := by
  intro ρ v hv s f hf hd hr us rest Q hk
  obtain ⟨x, y, hxa, hyb, rfl⟩ := eval_pair_inv hv
  show TWP P host s f (vals us ++ (expression (compile d a ++ compile d b ++
    [.structNew boxIdx]) ++ rest)) Q
  simp only [List.append_assoc, expr_append]
  refine ha ρ _ hxa s f hf (depth_left hd) hr us _ Q fun s₁ f₁ wa hs₁ hf₁ hwa => ?_
  have hdb : d + b.depth < f₁.locals.length := by rw [hf₁.2.1]; exact depth_right hd
  refine hb ρ _ hyb s₁ f₁ (hf.of_agree hf₁) hdb (hr.of_agree hs₁ hf₁) _ _ Q
    fun s₂ f₂ wb hs₂ hf₂ hwb => ?_
  exact twp_pairTail (hf.of_agree (hf₁.trans hf₂)) hk hs₁ hs₂ (hf₁.trans hf₂) hwa hwb

theorem spec_fst {d : Nat} {e : Tm} (he : Spec P host d e) : Spec (H := H) P host d (.fst e) := by
  intro ρ v hv s f hf hd hr us rest Q hk
  obtain ⟨y, hev⟩ := eval_fst_inv hv
  show TWP P host s f (vals us ++ (expression (compile d e ++
    [.refCast boxRef, .structGet none boxIdx (fx 0)]) ++ rest)) Q
  rw [expr_append]
  refine he ρ _ hev s f hf hd hr us _ Q fun s₁ f₁ w hs₁ hf₁ hw => ?_
  obtain ⟨addr, wa, wb, hw', hst, hwa, -⟩ := hw
  rw [hw']
  have hf₁' : FrameOK f₁ := hf.of_agree hf₁
  exact twp_castBox hf₁' hst (twp_getBox hf₁' (by omega) hst (hk s₁ f₁ wa hs₁ hf₁ hwa))

theorem spec_snd {d : Nat} {e : Tm} (he : Spec P host d e) : Spec (H := H) P host d (.snd e) := by
  intro ρ v hv s f hf hd hr us rest Q hk
  obtain ⟨x, hev⟩ := eval_snd_inv hv
  show TWP P host s f (vals us ++ (expression (compile d e ++
    [.refCast boxRef, .structGet none boxIdx (fx 1)]) ++ rest)) Q
  rw [expr_append]
  refine he ρ _ hev s f hf hd hr us _ Q fun s₁ f₁ w hs₁ hf₁ hw => ?_
  obtain ⟨addr, wa, wb, hw', hst, -, hwb⟩ := hw
  rw [hw']
  have hf₁' : FrameOK f₁ := hf.of_agree hf₁
  exact twp_castBox hf₁' hst (twp_getBox hf₁' (by omega) hst (hk s₁ f₁ wb hs₁ hf₁ hwb))

/-! ## Injections -/

/-- The value of an injection with tag `0` (`inl`) or `1` (`inr`). -/
def inj (tag : BitVec 31) (u : FunLang.Val) : FunLang.Val := if tag = 0 then .inl u else .inr u

theorem rep_inj {s : Store H} {tag : BitVec 31} (ht : tag = 0 ∨ tag = 1) {u : FunLang.Val}
    {wv : Val} {addr : Nat}
    (hst : s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 tag)), .val wv]⟩)
    (hu : Rep s u wv) : Rep s (inj tag u) (.ref (.struct addr)) := by
  rcases ht with rfl | rfl
  · exact ⟨addr, wv, rfl, hst, hu⟩
  · exact ⟨addr, wv, rfl, hst, hu⟩

theorem spec_injTag {d : Nat} {e : Tm} {tag : BitVec 31} (ht : tag = 0 ∨ tag = 1)
    (he : Spec P host d e) {ρ : List FunLang.Val} {u : FunLang.Val} (hev : eval ρ e = some u)
    {s : Store H} {f : Frame} (hf : FrameOK f) (hd : d + e.depth < f.locals.length)
    (hr : EnvRep s f d ρ) {us : List Val} {rest : List Admin} {Q : Post H}
    (hk : Cont P host d s f (inj tag u) us rest Q) :
    TWP P host s f (vals us ++ (expression (.intConst .i32 (tag.setWidth 32) :: .refI31 ::
      compile d e ++ [.structNew boxIdx]) ++ rest)) Q := by
  show TWP P host s f (vals us ++ (expression [.intConst .i32 (tag.setWidth 32), .refI31] ++
    (expression (compile d e ++ [.structNew boxIdx]) ++ rest))) Q
  refine twp_constBox ?_
  rw [expr_append, setWidth_31_32]
  refine he ρ u hev s f hf hd hr _ _ Q fun s₁ f₁ w hs₁ hf₁ hw => ?_
  rw [vals_pair]
  refine twp_newBox (hf.of_agree hf₁) ?_
  have hp := addStruct_prefix s₁ ⟨dBox, [.val (.ref (.i31 tag)), .val w]⟩
  exact hk _ f₁ _ (hs₁.trans hp) hf₁ (rep_inj ht (addStruct_get _ _) (hw.mono hp))

theorem spec_inl {d : Nat} {e : Tm} (he : Spec P host d e) : Spec (H := H) P host d (.inl e) := by
  intro ρ v hv s f hf hd hr us rest Q hk
  obtain ⟨u, hev, rfl⟩ := eval_inl_inv hv
  exact spec_injTag (tag := 0) (.inl rfl) he hev hf hd hr hk

theorem spec_inr {d : Nat} {e : Tm} (he : Spec P host d e) : Spec (H := H) P host d (.inr e) := by
  intro ρ v hv s f hf hd hr us rest Q hk
  obtain ⟨u, hev, rfl⟩ := eval_inr_inv hv
  exact spec_injTag (tag := 1) (.inr rfl) he hev hf hd hr hk

/-! ## `case` -/

/-- The code of a `case` branch: read the payload into local `d + 1`, then the branch. -/
def branch (d : Nat) (t : Tm) : List Instr :=
  getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile (d + 1) t

theorem twp_branch {d : Nat} {t : Tm} (hsp : Spec P host (d + 1) t) {ρ : List FunLang.Val}
    {u v : FunLang.Val} (hev : eval (u :: ρ) t = some v) {s : Store H} {f : Frame}
    (hf : FrameOK f) (hd : d + 1 + t.depth < f.locals.length) (hr : EnvRep s f d ρ)
    {addr : Nat} {tagw wv : Val} (hloc : f.locals[d + 1]? = some (some (.ref (.struct addr))))
    (hst : s.structs[addr]? = some ⟨dBox, [.val tagw, .val wv]⟩) (hu : Rep s u wv)
    {us : List Val} {rest : List Admin} {Q : Post H} (hk : Cont P host d s f v us rest Q) :
    TWP P host s f (vals [] ++ expression (branch d t))
      (labelPostT P host 1 [] us (seqPostT P host rest Q)) := by
  have hlt : d + 1 < f.locals.length := by omega
  have hlim : d + 1 < 2 ^ 32 := lt_lim hf hlt
  show TWP P host s f (vals [] ++ .plain (.localGet (lx (d + 1))) :: .plain (.refCast boxRef) ::
    .plain (.structGet none boxIdx (fx 1)) :: .plain (.localSet (lx (d + 1))) ::
    expression (compile (d + 1) t)) _
  refine twp_localGet hf hloc (twp_castBox hf hst (twp_getBox hf (by omega) hst
    (twp_localSet (w := wv) hf hlt ?_)))
  have hk' : Cont P host (d + 1) s (f.setLocal (lx (d + 1)) wv) v [] []
      (labelPostT P host 1 [] us (seqPostT P host rest Q)) :=
    fun s' f' w hs hag hw => Wp.of_vals (m := .total) (vs := [w])
      (hk s' f' w hs ((Agree.setLocal wv hlim).trans hag.of_succ) hw)
  have h' := hsp (u :: ρ) v hev s _ (hf.setLocal _ wv) (by rw [len_setLocal]; exact hd)
    (hr.cons hu hlt hlim) [] [] _ hk'
  simpa using h'

/-- The scrutinee of a `case` is in local `d + 1`; its tag selects the branch. -/
theorem twp_caseTail {d : Nat} {s : Store H} {f : Frame} (hf : FrameOK f)
    (hlt : d + 1 < f.locals.length) {addr : Nat} {tag : BitVec 31} {wv : Val}
    (hst : s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 tag)), .val wv]⟩)
    {br bl : List Instr} {us : List Val} {rest : List Admin} {Q : Post H}
    (hb : TWP P host s (f.setLocal (lx (d + 1)) (.ref (.struct addr)))
      (vals [] ++ expression (if tag.setWidth 32 ≠ 0 then br else bl))
      (labelPostT P host 1 [] us (seqPostT P host rest Q))) :
    TWP P host s f (vals (us ++ [.ref (.struct addr)]) ++ (expression (.localSet (lx (d + 1)) ::
      getField (d + 1) 0 ++ unbox ++ [.if_ (.value anyref) br bl]) ++ rest)) Q := by
  have hf₂ : FrameOK (f.setLocal (lx (d + 1)) (.ref (.struct addr))) := hf.setLocal _ _
  have hloc := setLocal_get (f := f) (.ref (.struct addr)) hlt (lt_lim hf hlt)
  show TWP P host s f (vals (us ++ [.ref (.struct addr)]) ++ .plain (.localSet (lx (d + 1))) ::
    .plain (.localGet (lx (d + 1))) :: .plain (.refCast boxRef) ::
    .plain (.structGet none boxIdx (fx 0)) ::
    (expression unbox ++ (.plain (.if_ (.value anyref) br bl) :: rest))) Q
  exact twp_localSet hf hlt (twp_localGet hf₂ hloc (twp_castBox hf₂ hst
    (twp_getBox hf₂ (by omega) hst (twp_unbox (twp_ifBlock hb)))))

theorem spec_case {d : Nat} {e l r : Tm} (he : Spec P host d e) (hl : Spec P host (d + 1) l)
    (hr' : Spec P host (d + 1) r) : Spec (H := H) P host d (.case e l r) := by
  intro ρ v hv s f hf hd hr us rest Q hk
  have hdlr : d + 1 + max l.depth r.depth < f.locals.length := depth_succ (depth_right hd)
  have hdl : d + 1 + l.depth < f.locals.length := depth_left hdlr
  have hdr : d + 1 + r.depth < f.locals.length := depth_right hdlr
  have hlt : d + 1 < f.locals.length := by omega
  show TWP P host s f (vals us ++ (expression (compile d e ++ .localSet (lx (d + 1)) ::
    getField (d + 1) 0 ++ unbox ++ [.if_ (.value anyref) (branch d r) (branch d l)]) ++ rest)) Q
  simp only [List.append_assoc]
  rw [expr_append]
  rcases eval_case_inv hv with ⟨u, hev, hbv⟩ | ⟨u, hev, hbv⟩
  · refine he ρ _ hev s f hf (depth_left hd) hr us _ Q fun s₁ f₁ w hs₁ hf₁ hw => ?_
    obtain ⟨addr, wv, hw', hst, hu⟩ := hw
    have hf₁' : FrameOK f₁ := hf.of_agree hf₁
    have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
    rw [hw']
    refine twp_caseTail hf₁' hlt₁ hst ?_
    exact twp_branch hl hbv (hf₁'.setLocal _ _) (by rw [len_setLocal, hf₁.2.1]; exact hdl)
      ((hr.of_agree hs₁ hf₁).of_agree (List.prefix_refl _) (Agree.setLocal _ (lt_lim hf hlt)))
      (setLocal_get _ hlt₁ (lt_lim hf hlt)) hst hu
      ((hk.later hs₁ hf₁).later (List.prefix_refl _) (Agree.setLocal _ (lt_lim hf hlt)))
  · refine he ρ _ hev s f hf (depth_left hd) hr us _ Q fun s₁ f₁ w hs₁ hf₁ hw => ?_
    obtain ⟨addr, wv, hw', hst, hu⟩ := hw
    have hf₁' : FrameOK f₁ := hf.of_agree hf₁
    have hlt₁ : d + 1 < f₁.locals.length := by rw [hf₁.2.1]; exact hlt
    rw [hw']
    refine twp_caseTail hf₁' hlt₁ hst ?_
    exact twp_branch hr' hbv (hf₁'.setLocal _ _) (by rw [len_setLocal, hf₁.2.1]; exact hdr)
      ((hr.of_agree hs₁ hf₁).of_agree (List.prefix_refl _) (Agree.setLocal _ (lt_lim hf hlt)))
      (setLocal_get _ hlt₁ (lt_lim hf hlt)) hst hu
      ((hk.later hs₁ hf₁).later (List.prefix_refl _) (Agree.setLocal _ (lt_lim hf hlt)))

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

end Silmaril.Proofs.Wasm.Models.FunCompile
