module

public import Silmaril.Wasm.Component.Chunked.Defs
public import Silmaril.Wasm.Binary.Core.DecodeSound

/-!
# Chunked decode certificates: soundness and composition

**PROVED**:

* slices: `slice_append` (adjacent slices concatenate), `slice_eq_flatten` (the slices
  between sorted cut points flatten to the whole slice), `slice_decode` (a slice of an
  included file is its `window`), `length_bytesChunks` (an included file has its stated size);
* silmaril readers on a slice: `runAll_sound` (a reader that consumes exactly the slice gives
  its production), `readAllOf_sound`, `readInstrs_sound`, `readLocalsGroup_sound`;
* the checkers: `chkI_sound` (instruction plans give `Instrs`), `chkCode_sound` (`Code`),
  `codesOk_sound` (a run of code entries: `Seq Code`, its length and no data index),
  `chkSeq_sound`, `chkVec_sound` (`Vec`), `chkSection_sound` (`Section`),
  `chkDatas_sound` (kind-`0` data segments, bytes not read), `customSec_of` (a custom
  section from its size and name only);
* composition: `seq_append`, `seq_flatten` (code entries certified in groups, possibly in
  different modules, form one `Seq`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Chunked

open Silmaril.IncludeBytes
open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core
open Silmaril.Wasm.Binary.Core.Decode

/-! ## Slices -/

@[simp] theorem slice_self (l : List UInt8) (a : Nat) : slice l a a = [] := by
  simp [slice]

theorem slice_append (l : List UInt8) {a b c : Nat} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    slice l a b ++ slice l b c = slice l a c := by
  unfold slice
  have e : c - a = (b - a) + (c - b) := by omega
  rw [e, List.take_add, List.drop_drop]
  congr 3
  omega

theorem sorted_cons {a b : Nat} {bs : List Nat} (h : sorted a (b :: bs) = true) :
    a ≤ b ∧ sorted b bs = true := by
  simpa [sorted] using h

theorem sorted_le_last : ∀ {b : Nat} {bs : List Nat}, sorted b bs = true → b ≤ lastCut b bs
  | _, [], _ => Nat.le_refl _
  | _, _ :: _, h => Nat.le_trans (sorted_cons h).1 (sorted_le_last (sorted_cons h).2)

theorem slice_eq_flatten (l : List UInt8) :
    ∀ (a : Nat) (cuts : List Nat), sorted a cuts = true →
      slice l a (lastCut a cuts) = (pieces l a cuts).flatten
  | a, [], _ => by simp [lastCut, pieces]
  | a, b :: bs, h => by
    have hab : a ≤ b := (sorted_cons h).1
    have hs : sorted b bs = true := (sorted_cons h).2
    simp only [lastCut, pieces, List.flatten_cons]
    rw [← slice_eq_flatten l b bs hs, slice_append l hab (sorted_le_last hs)]

theorem slice_slice (l : List UInt8) {A B a b : Nat} (hA : A ≤ a) (hab : a ≤ b) (hB : b ≤ B) :
    slice (slice l A B) (a - A) (b - A) = slice l a b := by
  unfold slice
  rw [List.drop_take, List.drop_drop, List.take_take]
  congr 2
  · omega
  · omega

theorem bytesChunks_zero (c : Nat) : ∀ cs : List Nat, bytesChunks c 0 cs = []
  | [] => rfl
  | _ :: cs => by
    rw [bytesChunks_cons, Nat.min_zero, bytesLE_zero, Nat.zero_sub, bytesChunks_zero c cs]
    rfl

theorem drop_bytesChunks (c : Nat) :
    ∀ (i n : Nat) (cs : List Nat),
      (bytesChunks c n cs).drop (c * i) = bytesChunks c (n - c * i) (cs.drop i)
  | 0, n, cs => by simp
  | _ + 1, _, [] => by simp [bytesChunks_nil]
  | i + 1, n, x :: xs => by
    have hd : ∀ L : List UInt8, L.drop (c * (i + 1)) = (L.drop c).drop (c * i) := by
      intro L
      rw [List.drop_drop]
      congr 1
      rw [Nat.mul_succ]
      omega
    rw [bytesChunks_cons, hd, List.drop_succ_cons]
    by_cases hn : c ≤ n
    · rw [List.drop_left' (by simp [Nat.min_eq_left hn]), drop_bytesChunks c i (n - c) xs]
      congr 1
      rw [Nat.mul_succ]
      omega
    · have hz : n - c = 0 := by omega
      rw [hz, bytesChunks_zero, List.append_nil, List.drop_eq_nil_of_le (by simp)]
      have hz' : n - c * (i + 1) = 0 := by rw [Nat.mul_succ]; omega
      rw [hz', bytesChunks_zero]

/-- **A slice of an included file is its window.** -/
theorem slice_decode (c n : Nat) (cs : List Nat) (a b : Nat) :
    slice (bytesChunks c n cs) a b = window c n cs a b := by
  unfold slice window
  have e : (bytesChunks c n cs).drop a =
      ((bytesChunks c n cs).drop (c * (a / c))).drop (a % c) := by
    rw [List.drop_drop]
    congr 1
    have := Nat.div_add_mod a c
    omega
  rw [e, drop_bytesChunks]

theorem length_bytesChunks (c : Nat) :
    ∀ (n : Nat) (cs : List Nat), n ≤ c * cs.length → (bytesChunks c n cs).length = n
  | n, [], h => by simp at h; simp [bytesChunks_nil, h]
  | n, x :: xs, h => by
    rw [bytesChunks_cons, List.length_append, length_bytesLE,
      length_bytesChunks c (n - c) xs (by simp [Nat.mul_succ] at h; omega)]
    omega

theorem le_length {l : List UInt8} {n e : Nat} (hl : l.length = n) (h : e ≤ n) : e ≤ l.length :=
  hl ▸ h

theorem length_slice (l : List UInt8) {a b : Nat} (_hab : a ≤ b) (hb : b ≤ l.length) :
    (slice l a b).length = b - a := by
  simp [slice]
  omega

/-! ## Readers on a slice -/

theorem arr_rest (l : List UInt8) : (⟨arr l, 0⟩ : Cursor).rest = l := by
  simp [Cursor.rest, arr]

theorem runAll_sound {α : Type} {G : Bytes → α → Prop} {p : DecodeM α} (hp : Sound G p)
    {l : List UInt8} {a : α} (h : runAll p l = some a) : G l a := by
  unfold runAll at h
  split at h
  · rename_i x c hrun
    split at h
    · rename_i hpos
      cases h
      obtain ⟨hb, pre, hr, hg⟩ := hp hrun
      have hc : c.rest = [] := by
        simp only [Cursor.rest, hb, arr, hpos]
        simp
      rw [arr_rest, hc, List.append_nil] at hr
      exact hr ▸ hg
    · cases h
  · cases h

theorem readAllOf_sound {α : Type} {G : Bytes → α → Prop} {f : DecodeM α} (hf : Sound G f) :
    ∀ fuel : Nat, Sound (Seq G) (readAllOf f fuel)
  | 0 => by
    intro c a c' h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact ⟨rfl, [], by simp, Seq.nil⟩
  | fuel + 1 => by
    intro c a c' h
    simp only [readAllOf] at h
    obtain ⟨n, cm, hn, h⟩ := run_bind_ok h
    rw [remaining_run] at hn
    cases hn
    split at h
    · obtain ⟨rfl, rfl⟩ := run_pure_ok h
      exact ⟨rfl, [], by simp, Seq.nil⟩
    · obtain ⟨x, c₁, hx, h⟩ := run_bind_ok h
      obtain ⟨xs, c₂, hxs, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hb₁, p₁, hr₁, hg₁⟩ := hf hx
      obtain ⟨hb₂, p₂, hr₂, hg₂⟩ := readAllOf_sound hf fuel hxs
      exact ⟨hb₂.trans hb₁, p₁ ++ p₂, by simp [hr₁, hr₂], Seq.cons hg₁ hg₂⟩

theorem readInstrs_sound : ∀ fuel : Nat, Sound (Silmaril.Wasm.Binary.Core.Instrs Forms.all) (readInstrs fuel)
  | 0 => by
    intro c a c' h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact ⟨rfl, [], by simp, Instrs.nil⟩
  | fuel + 1 => by
    intro c a c' h
    simp only [readInstrs] at h
    obtain ⟨n, cm, hn, h⟩ := run_bind_ok h
    rw [remaining_run] at hn
    cases hn
    split at h
    · obtain ⟨rfl, rfl⟩ := run_pure_ok h
      exact ⟨rfl, [], by simp, Instrs.nil⟩
    · obtain ⟨b, c₁, hb, h⟩ := run_bind_ok h
      obtain ⟨hbb, hbr⟩ := readByte_ok hb
      obtain ⟨i, c₂, hi, h⟩ := run_bind_ok h
      obtain ⟨is, c₃, his, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hb₂, p₂, hr₂, hg₂⟩ := (readInstr_readSeq_sound fuel).1 b hi
      obtain ⟨hb₃, p₃, hr₃, hg₃⟩ := readInstrs_sound fuel his
      refine ⟨hb₃.trans (hb₂.trans hbb), ([b] ++ p₂) ++ p₃, ?_, Instrs.cons hg₂ hg₃⟩
      simp [hbr, hr₂, hr₃]

theorem readLocalsGroup_sound : Sound (Silmaril.Wasm.Binary.Core.Locals Forms.all) readLocalsGroup := by
  intro c a c' h
  obtain ⟨⟨n, t⟩, c₁, h₁, h⟩ := run_bind_ok
    (show ((do let n ← readU 32; let t ← readValType; pure (n, t)) >>=
      fun p => pure (List.replicate p.1 p.2)).run c = _ by
        simpa [readLocalsGroup] using h)
  obtain ⟨rfl, rfl⟩ := run_pure_ok h
  exact readLocals_sound h₁

/-! ## Grammar composition -/

theorem instrs_append {b₂ : Bytes} {is₂ : List Instr} (h₂ : Silmaril.Wasm.Binary.Core.Instrs Forms.all b₂ is₂) :
    ∀ {is₁ : List Instr} {b₁ : Bytes}, Silmaril.Wasm.Binary.Core.Instrs Forms.all b₁ is₁ →
      Silmaril.Wasm.Binary.Core.Instrs Forms.all (b₁ ++ b₂) (is₁ ++ is₂)
  | [], _, h₁ => by cases h₁; exact h₂
  | _ :: _, _, h₁ => by
    cases h₁ with
    | cons h hs =>
      simpa only [List.append_assoc, List.cons_append] using Instrs.cons h (instrs_append h₂ hs)

theorem seq_append {α : Type} {G : Bytes → α → Prop} {b₁ b₂ : Bytes} {l₁ l₂ : List α}
    (h₁ : Seq G b₁ l₁) (h₂ : Seq G b₂ l₂) : Seq G (b₁ ++ b₂) (l₁ ++ l₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons ha _ ih => simpa only [List.append_assoc, List.cons_append] using Seq.cons ha ih

/-- Groups of elements certified one by one (each group's bytes and values) form one `Seq`. -/
theorem seq_flatten {α : Type} {G : Bytes → α → Prop} :
    ∀ {bs : List Bytes} {xs : List (List α)}, List.Forall₂ (Seq G) bs xs →
      Seq G bs.flatten xs.flatten
  | [], [], .nil => Seq.nil
  | _ :: _, _ :: _, .cons h hs => by
    simpa only [List.flatten_cons] using seq_append h (seq_flatten hs)

theorem take_append_drop' (r : List UInt8) (k : Nat) : r = r.take k ++ r.drop k :=
  (List.take_append_drop k r).symm

/-! ## The instruction checker -/

theorem blockInstr_sound {op : UInt8} {bt : BlockType} {is : List Instr} {i : Instr}
    {hdr body : Bytes} (h : blockInstr op bt is = some i) (ht : Core.BlockType Forms.all hdr bt)
    (hb : Silmaril.Wasm.Binary.Core.Instrs Forms.all body is) : Binary.Core.Instr Forms.all ([op] ++ hdr ++ body ++ [0x0B]) i := by
  unfold blockInstr at h
  split at h
  · rename_i e; cases h; subst e; exact Instr.block ht hb
  · split at h
    · rename_i e; cases h; subst e; exact Instr.loop ht hb
    · split at h
      · rename_i e; cases h; subst e; exact Instr.if_ ht hb
      · cases h

/-- **Instruction plans give `Instrs`** on the bytes they consume. -/
theorem chkI_sound : ∀ (p : IPlan) {r r' : List UInt8} {is : List Instr},
    chkI p r = some (is, r') → ∃ b, r = b ++ r' ∧ Silmaril.Wasm.Binary.Core.Instrs Forms.all b is
  | .nil, r, r', is, h => by
    simp only [chkI, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, Instrs.nil⟩
  | .leaf k p, r, r', is, h => by
    simp only [chkI] at h
    split at h
    · rename_i is₁ h₁
      obtain ⟨⟨js, r₂⟩, h₂, e⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨b, hb, hg⟩ := chkI_sound p h₂
      refine ⟨r.take k ++ b, ?_, instrs_append hg (runAll_sound (readInstrs_sound _) h₁)⟩
      rw [List.append_assoc, ← hb, List.take_append_drop]
    · cases h
  | .block k body p, r, r', is, h => by
    simp only [chkI] at h
    split at h
    · rename_i op r₁
      split at h
      · rename_i bt is₁ r₂ hbt hbody
        split at h
        · rename_i i hi
          obtain ⟨⟨js, r₃⟩, h₃, e⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          obtain ⟨bb, hbb, hgb⟩ := chkI_sound body hbody
          obtain ⟨b', hb', hg'⟩ := chkI_sound p h₃
          refine ⟨([op] ++ r₁.take (k - 1) ++ bb ++ [0x0B]) ++ b', ?_,
            Instrs.cons (blockInstr_sound hi (runAll_sound readBlockType_sound hbt) hgb) hg'⟩
          calc op :: r₁ = op :: (r₁.take (k - 1) ++ r₁.drop (k - 1)) := by
                rw [List.take_append_drop]
            _ = _ := by rw [hbb, hb']; simp
        · cases h
      · cases h
    · cases h
  | .ifElse k thn els p, r, r', is, h => by
    simp only [chkI] at h
    split at h
    · rename_i op r₁
      split at h
      · rename_i hop
        split at h
        · rename_i bt is₁ r₂ hbt hthn
          split at h
          · rename_i is₂ r₃ hels
            obtain ⟨⟨js, r₄⟩, h₄, e⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            obtain ⟨b₁, hb₁, hg₁⟩ := chkI_sound thn hthn
            obtain ⟨b₂, hb₂, hg₂⟩ := chkI_sound els hels
            obtain ⟨b', hb', hg'⟩ := chkI_sound p h₄
            subst hop
            refine ⟨([0x04] ++ r₁.take (k - 1) ++ b₁ ++ [0x05] ++ b₂ ++ [0x0B]) ++ b', ?_,
              Instrs.cons (Instr.ifElse (runAll_sound readBlockType_sound hbt) hg₁ hg₂) hg'⟩
            calc 0x04 :: r₁ = 0x04 :: (r₁.take (k - 1) ++ r₁.drop (k - 1)) := by
                  rw [List.take_append_drop]
              _ = _ := by rw [hb₁, hb₂, hb']; simp
          · cases h
        · cases h
      · cases h
    · cases h

/-! ## Code entries -/

/-- What a successful `chkCode` run checked. -/
theorem chkCode_parts {p : CPlan} {r r' : List UInt8} {code : List ValType × Expr}
    (h : chkCode p r = some (code, r')) :
    ∃ len lss is, runAll (readU 32) (r.take p.kSize) = some len ∧
      ((r.drop p.kSize).take len).length = len ∧
      runAll (readVec readLocalsGroup) (((r.drop p.kSize).take len).take p.kLocals) = some lss ∧
      chkI p.body (((r.drop p.kSize).take len).drop p.kLocals) = some (is, [0x0B]) ∧
      lss.flatten.length < 2 ^ 32 ∧ code = (lss.flatten, is) ∧ r' = (r.drop p.kSize).drop len := by
  unfold chkCode at h
  split at h
  · rename_i len hlen
    dsimp only at h
    split at h
    · rename_i hclen
      split at h
      · rename_i lss is hl hbody
        split at h
        · rename_i hcount
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨len, lss, is, hlen, hclen, hl, hbody, hcount, h.1.symm, h.2.symm⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- **A code entry plan gives `Code`** on the bytes it consumes. -/
theorem chkCode_sound {p : CPlan} {r r' : List UInt8} {code : List ValType × Expr}
    (h : chkCode p r = some (code, r')) : ∃ b, r = b ++ r' ∧ Silmaril.Wasm.Binary.Core.Code Forms.all b code := by
  obtain ⟨len, lss, is, hlen, hclen, hl, hbody, hcount, rfl, rfl⟩ := chkCode_parts h
  let c := (r.drop p.kSize).take len
  obtain ⟨bb, hbb, hgb⟩ : ∃ bb, c.drop p.kLocals = bb ++ [0x0B] ∧ Silmaril.Wasm.Binary.Core.Instrs Forms.all bb is := by
    obtain ⟨bb, hbb, hgb⟩ := chkI_sound p.body hbody
    exact ⟨bb, hbb, hgb⟩
  have hv : Vec (Silmaril.Wasm.Binary.Core.Locals Forms.all) (c.take p.kLocals) lss :=
    runAll_sound (readVec_sound readLocalsGroup_sound) hl
  have hf : Silmaril.Wasm.Binary.Core.Func Forms.all c (lss.flatten, is) := by
    have hf' := Func.mk hv (Expr.mk hgb) hcount
    rwa [← hbb, List.take_append_drop] at hf'
  have hr : r = (r.take p.kSize ++ c) ++ (r.drop p.kSize).drop len := by
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  exact ⟨_, hr, Code.mk (runAll_sound (readU_sound 32) hlen) hclen.symm hf⟩

theorem chkCodes_sound : ∀ {ps : List CPlan} {r r' : List UInt8}
    {cs : List (List ValType × Expr)}, chkCodes ps r = some (cs, r') →
      ∃ b, r = b ++ r' ∧ Seq (Silmaril.Wasm.Binary.Core.Code Forms.all) b cs ∧ cs.length = ps.length
  | [], r, r', cs, h => by
    simp only [chkCodes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, Seq.nil, rfl⟩
  | p :: ps, r, r', cs, h => by
    simp only [chkCodes] at h
    split at h
    · rename_i c r₁ h₁
      obtain ⟨⟨cs', r₂⟩, h₂, e⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨b₁, hb₁, hg₁⟩ := chkCode_sound h₁
      obtain ⟨b₂, hb₂, hg₂, hl⟩ := chkCodes_sound h₂
      refine ⟨b₁ ++ b₂, by rw [hb₁, hb₂, List.append_assoc], Seq.cons hg₁ hg₂, ?_⟩
      simp [hl]
    · cases h

/-- **A group of code entries**: the plans consume all of `r`, which is the `Seq` of their
entries, one per plan, with no data index. -/
theorem codesOk_sound {ps : List CPlan} {r : List UInt8} (h : codesOk ps r = true) :
    Seq (Silmaril.Wasm.Binary.Core.Code Forms.all) r (codesOf ps r) ∧ (codesOf ps r).length = ps.length ∧
      codesDataIdxs (codesOf ps r) = [] := by
  unfold codesOk at h
  unfold codesOf
  split at h
  · rename_i cs hc
    obtain ⟨b, hb, hg, hl⟩ := chkCodes_sound hc
    rw [List.append_nil] at hb
    subst hb
    exact ⟨hg, hl, of_decide_eq_true h⟩
  · cases h

theorem codesDataIdxs_nil : codesDataIdxs [] = [] := rfl

theorem codesDataIdxs_flatten_cons (c : List (List ValType × Expr))
    (cs : List (List (List ValType × Expr))) :
    codesDataIdxs (c :: cs).flatten = codesDataIdxs c ++ codesDataIdxs cs.flatten := by
  simp [codesDataIdxs, List.flatMap_append]

theorem length_flatten_of {α : Type} :
    ∀ {xss : List (List α)} {ns : List Nat}, List.Forall₂ (fun xs n => xs.length = n) xss ns →
      xss.flatten.length = ns.sum
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    rw [List.flatten_cons, List.length_append, h, length_flatten_of hs, List.sum_cons]

theorem codesDataIdxs_flatten_of :
    ∀ {css : List (List (List ValType × Expr))}, allP (fun c => codesDataIdxs c = []) css →
      codesDataIdxs css.flatten = []
  | [], _ => rfl
  | _ :: _, ⟨h, hs⟩ => by
    rw [codesDataIdxs_flatten_cons, h, codesDataIdxs_flatten_of hs]
    rfl

/-! ## Vectors and sections -/

theorem chkSeq_sound {α : Type} {G : Bytes → α → Prop} {f : DecodeM α} (hf : Sound G f) :
    ∀ {ks : List Nat} {r r' : List UInt8} {xs : List α}, chkSeq f ks r = some (xs, r') →
      ∃ b, r = b ++ r' ∧ Seq G b xs
  | [], r, r', xs, h => by
    simp only [chkSeq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, Seq.nil⟩
  | k :: ks, r, r', xs, h => by
    simp only [chkSeq] at h
    split at h
    · rename_i xs₁ h₁
      obtain ⟨⟨ys, r₂⟩, h₂, e⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨b, hb, hg⟩ := chkSeq_sound hf h₂
      refine ⟨r.take k ++ b, ?_, seq_append (runAll_sound (readAllOf_sound hf _) h₁) hg⟩
      rw [List.append_assoc, ← hb, List.take_append_drop]
    · cases h

theorem chkVec_sound {α : Type} {G : Bytes → α → Prop} {f : DecodeM α} (hf : Sound G f)
    {k : Nat} {ks : List Nat} {r : List UInt8} {xs : List α} (h : chkVec f k ks r = some xs) :
    Vec G r xs := by
  unfold chkVec at h
  split at h
  · rename_i n xs' hn hs
    split at h
    · rename_i hlen
      cases h
      obtain ⟨b, hb, hg⟩ := chkSeq_sound hf hs
      rw [List.append_nil] at hb
      have hv := Vec.mk (G := G) (hlen ▸ runAll_sound (readU_sound 32) hn) hg
      rwa [← hb, List.take_append_drop] at hv
    · cases h
  · cases h

theorem chkSection_sound {α : Type} {N : UInt8} {G : Bytes → List α → Prop} {k : Nat}
    {inner : List UInt8 → Option (List α)} (hin : ∀ {c a}, inner c = some a → G c a)
    {r : List UInt8} {a : List α} (h : chkSection N k inner r = some a) : Section N G r a := by
  cases r with
  | nil => cases h
  | cons id r₁ =>
    simp only [chkSection] at h
    split at h
    · rename_i hid
      subst hid
      split at h
      · rename_i len hlen
        split at h
        · rename_i hl
          have hs := Section.mk (N := id) (runAll_sound (readU_sound 32) hlen) hl.symm (hin h)
          rwa [List.append_assoc, List.take_append_drop] at hs
        · cases h
      · cases h
    · cases h

/-! ## Data segments -/

theorem chkData0_sound {kk ke kl : Nat} {r r' : List UInt8} {d : Silmaril.Wasm.Data}
    (h : chkData0 kk ke kl r = some (d, r')) : ∃ b, r = b ++ r' ∧ Silmaril.Wasm.Binary.Core.Data Forms.all b d := by
  unfold chkData0 at h
  split at h
  · rename_i e n hk he hn
    simp only at h
    split at h
    · rename_i hlen
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨r.take kk ++ ((r.drop kk).take ke ++ (((r.drop kk).drop ke).take kl ++
          (((r.drop kk).drop ke).drop kl).take n)), ?_, ?_⟩
      · simp only [List.append_assoc, List.take_append_drop]
      · have hd := Data.k0 (F := Forms.all) (runAll_sound (readU_sound 32) hk)
          (runAll_sound readExpr_sound he)
          (Vec.mk (hlen ▸ runAll_sound (readU_sound 32) hn) (seqByte _))
        simpa only [List.append_assoc] using hd
    · cases h
  · cases h

theorem chkDatas_sound : ∀ {ps : List (Nat × Nat × Nat)} {r r' : List UInt8}
    {ds : List Silmaril.Wasm.Data}, chkDatas ps r = some (ds, r') →
      ∃ b, r = b ++ r' ∧ Seq (Silmaril.Wasm.Binary.Core.Data Forms.all) b ds ∧ ds.length = ps.length
  | [], r, r', ds, h => by
    simp only [chkDatas, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, Seq.nil, rfl⟩
  | (a, b, c) :: ps, r, r', ds, h => by
    simp only [chkDatas] at h
    split at h
    · rename_i d r₁ h₁
      obtain ⟨⟨ds', r₂⟩, h₂, e⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨b₁, hb₁, hg₁⟩ := chkData0_sound h₁
      obtain ⟨b₂, hb₂, hg₂, hl⟩ := chkDatas_sound h₂
      refine ⟨b₁ ++ b₂, by rw [hb₁, hb₂, List.append_assoc], Seq.cons hg₁ hg₂, ?_⟩
      simp [hl]
    · cases h

/-! ## Custom sections -/

/-- **A custom section from its size and name**: its other bytes are not read. -/
theorem customSec_of (l : List UInt8) {s x y e len : Nat} {nm : String}
    (hid : slice l s (s + 1) = [0]) (hsz : runAll (readU 32) (slice l (s + 1) x) = some len)
    (hname : runAll readName (slice l x y) = some nm) (hlen : len = e - x)
    (h₁ : s + 1 ≤ x) (h₂ : x ≤ y) (h₃ : y ≤ e) (h₄ : e ≤ l.length) :
    CustomSec (slice l s e) := by
  have hc : Custom (slice l x y ++ slice l y e) [()] :=
    Custom.mk _ (runAll_sound readName_sound hname)
  rw [slice_append l h₂ h₃] at hc
  have hs := Section.mk (N := 0) (runAll_sound (readU_sound 32) hsz)
    (by rw [hlen, length_slice l (by omega) h₄]) hc
  rw [← hid, slice_append l (by omega) h₁, slice_append l (by omega) (by omega)] at hs
  exact ⟨[()], hs⟩


/-! ## Assembling sections from slices -/

theorem getD_of_isSome {α : Type} {o : Option α} (d : α) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o with
  | none => cases h
  | some a => rfl

/-- **A vector section from its plan**: `N size:u32 n:u32 el*`, elements decoded in pieces. -/
theorem vecSection_of {α : Type} {G : Bytes → α → Prop} {f : DecodeM α} (hf : Sound G f)
    {N : UInt8} {kS kC : Nat} {ks : List Nat} {r : List UInt8}
    (h : (chkSection N kS (chkVec f kC ks) r).isSome = true) :
    Section N (Vec G) r ((chkSection N kS (chkVec f kC ks) r).getD []) := by
  have e : chkSection N kS (chkVec f kC ks) r =
      some ((chkSection N kS (chkVec f kC ks) r).getD []) := getD_of_isSome [] h
  exact chkSection_sound (G := Vec G) (inner := chkVec f kC ks)
    (fun hc => chkVec_sound hf hc) e

theorem chkDataVec_sound {kC : Nat} {ps : List (Nat × Nat × Nat)} {r : List UInt8}
    {ds : List Silmaril.Wasm.Data} (h : chkDataVec kC ps r = some ds) : Vec (Silmaril.Wasm.Binary.Core.Data Forms.all) r ds := by
  unfold chkDataVec at h
  split at h
  · rename_i n ds' hn hs
    split at h
    · rename_i hlen
      cases h
      obtain ⟨b, hb, hg, _⟩ := chkDatas_sound hs
      rw [List.append_nil] at hb
      have hv := Vec.mk (G := Silmaril.Wasm.Binary.Core.Data Forms.all) (hlen ▸ runAll_sound (readU_sound 32) hn) hg
      rwa [← hb, List.take_append_drop] at hv
    · cases h
  · cases h

/-- **The data section from its plan** (segment bytes not read). -/
theorem dataSection_of {kS kC : Nat} {ps : List (Nat × Nat × Nat)} {r : List UInt8}
    (h : (chkSection 11 kS (chkDataVec kC ps) r).isSome = true) :
    Section 11 (Vec (Silmaril.Wasm.Binary.Core.Data Forms.all)) r ((chkSection 11 kS (chkDataVec kC ps) r).getD []) := by
  have e : chkSection 11 kS (chkDataVec kC ps) r =
      some ((chkSection 11 kS (chkDataVec kC ps) r).getD []) := getD_of_isSome [] h
  exact chkSection_sound (G := Vec (Silmaril.Wasm.Binary.Core.Data Forms.all)) (inner := chkDataVec kC ps)
    (fun hc => chkDataVec_sound hc) e

/-- **A section from its parts**: the id byte, the size, and the contents' production. -/
theorem section_of_parts {α : Type} {N : UInt8} {G : Bytes → List α → Prop} (l : List UInt8)
    {s x e len : Nat} {xs : List α} (hid : slice l s (s + 1) = [N])
    (hsz : runAll (readU 32) (slice l (s + 1) x) = some len) (hlen : len = e - x)
    (h₁ : s + 1 ≤ x) (h₂ : x ≤ e) (h₃ : e ≤ l.length) (hc : G (slice l x e) xs) :
    Section N G (slice l s e) xs := by
  have hs := Section.mk (N := N) (runAll_sound (readU_sound 32) hsz)
    (by rw [hlen, length_slice l h₂ h₃]) hc
  rwa [← hid, slice_append l (by omega) h₁, slice_append l (by omega) h₂] at hs

/-- **A vector from its parts**: the count, then the elements. -/
theorem vec_of_parts {α : Type} {G : Bytes → α → Prop} (l : List UInt8) {x y e n : Nat}
    {xs : List α} (hn : runAll (readU 32) (slice l x y) = some n) (hlen : xs.length = n)
    (hxy : x ≤ y) (hye : y ≤ e) (hs : Seq G (slice l y e) xs) : Vec G (slice l x e) xs := by
  have hv := Vec.mk (G := G) (hlen ▸ runAll_sound (readU_sound 32) hn) hs
  rwa [slice_append l hxy hye] at hv

/-- Groups of elements on consecutive slices form one `Seq` on their union. -/
theorem seq_of_spans {α : Type} {G : Bytes → α → Prop} (l : List UInt8) {a : Nat}
    {cuts : List Nat} {xss : List (List α)} (hs : sorted a cuts = true)
    (h : List.Forall₂ (Seq G) (pieces l a cuts) xss) :
    Seq G (slice l a (lastCut a cuts)) xss.flatten := by
  rw [slice_eq_flatten l a cuts hs]
  exact seq_flatten h

/-- Custom sections on consecutive slices. -/
theorem customs_of_spans (l : List UInt8) :
    ∀ {a : Nat} {cuts : List Nat}, sorted a cuts = true →
      allP CustomSec (pieces l a cuts) → Customs (slice l a (lastCut a cuts))
  | a, [], _, _ => by simpa [lastCut] using Customs.nil
  | a, b :: bs, hs, h => by
    have hab : a ≤ b := (sorted_cons hs).1
    have hbs : sorted b bs = true := (sorted_cons hs).2
    have h₁ : CustomSec (slice l a b) := h.1
    have h₂ : Customs (slice l b (lastCut b bs)) := customs_of_spans l hbs h.2
    have e : slice l a (lastCut a (b :: bs)) = slice l a b ++ slice l b (lastCut b bs) := by
      simp only [lastCut]
      rw [slice_append l hab (sorted_le_last hbs)]
    rw [e]
    exact Customs.cons h₁ h₂

theorem customs_empty (l : List UInt8) (a : Nat) : Customs (slice l a a) := by
  rw [slice_self]
  exact Customs.nil

/-- Restate a module's bytes. -/
theorem moduleWith_of_eq {I : Bytes → List Silmaril.Wasm.Import → Prop} {bs bs' : Bytes}
    {m : Silmaril.Wasm.Module} (h : Silmaril.Wasm.Binary.Core.ModuleWithImports Forms.all I bs m) (e : bs = bs') :
    Silmaril.Wasm.Binary.Core.ModuleWithImports Forms.all I bs' m := e ▸ h

/-! ## Raw component frames -/

/-- **One frame from its parts**: the id byte, the minimal LEB128 size, and the body's length. -/
theorem frameEnc_of (l : List UInt8) {id : UInt8} {s x e : Nat}
    (hid : slice l s (s + 1) = [id])
    (hsz : Silmaril.Parse.ByteParse.Enc.u32 (e - x) = some (slice l (s + 1) x))
    (h₁ : s + 1 ≤ x) (h₂ : x ≤ e) (h₃ : e ≤ l.length) :
    frameEnc (id, slice l x e) = some (slice l s e) := by
  have hl : (slice l x e).length = e - x := length_slice l h₂ h₃
  have e₁ : slice l s e = [id] ++ (slice l (s + 1) x ++ slice l x e) := by
    rw [← hid, slice_append l h₁ h₂, slice_append l (by omega) (by omega)]
  rw [e₁]
  simp only [frameEnc, Silmaril.Parse.ByteParse.Enc.sized, hl, hsz]
  rfl

theorem framesEnc_of :
    ∀ {ss : List RawSection} {fs : List Bytes},
      List.Forall₂ (fun s f => frameEnc s = some f) ss fs → framesEnc ss = some fs.flatten
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [framesEnc, h, framesEnc_of hs, Option.bind_eq_bind, Option.bind_some,
      List.flatten_cons]
    rfl

/-- **The framing of a whole file**: the preamble, then frames on consecutive slices. -/
theorem framing_of (l : List UInt8) {cuts : List Nat} {ss : List RawSection}
    (hpre : slice l 0 8 = Silmaril.Wasm.Component.Binary.preambleBytes)
    (hs : sorted 8 cuts = true) (hend : lastCut 8 cuts = l.length)
    (h : List.Forall₂ (fun s f => frameEnc s = some f) ss (pieces l 8 cuts)) :
    framing ss = some l := by
  have e : l = slice l 0 8 ++ slice l 8 (lastCut 8 cuts) := by
    rw [slice_append l (by omega) (by have := sorted_le_last hs; omega), hend]
    simp [slice]
  simp only [framing, framesEnc_of h, ← slice_eq_flatten l 8 cuts hs, ← hpre, Option.map_eq_map,
    Option.map_some]
  exact congrArg some e.symm

end Silmaril.Wasm.Component.Chunked

end
