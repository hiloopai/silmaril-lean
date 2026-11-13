module

public import Silmaril.Proofs.Wasm.Auto2.Valid2.Atom

/-!
# The extended checker against silmaril-lean's sequence checker

`instrC_sound`: each case of `instrC` (direct atoms, blocks, branches, calls) is a step of
silmaril-lean's `checkInstr atomC tyOkC` on the reversed stack, given that `rec` is sound for the
bodies; `runL_sound`, `seqN_sound`: an accepted sequence is accepted by `checkSeq` with its goal;
`exprC_of_exprG`: hence `exprG` implies the default expression checker.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.Valid2

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto2.Valid Silmaril.Wasm.Auto2.Valid2
open Silmaril.Proofs.Wasm.Auto2.Valid

/-- What a stack-polymorphic step of the extended checker promises. -/
def PolyOk (C : Context) (t : List CValType) (i : Instr) : Prop :=
  ∃ t₁, checkInstr atomC tyOkC C t.reverse i = some (.poly t₁)

/-- What an accepted sequence promises: `checkSeq` accepts it with the goal `g`, and the locals
it initialises are already set. -/
def SeqOk (C : Context) (t g : List CValType) (is : List Instr) : Prop :=
  ∃ xs k, checkSeq atomC tyOkC C t.reverse false (some g) is = some (g, xs, k) ∧ SetIn C xs

/-- A sound sequence checker for block bodies. -/
def RecOk (rec : Context → List CValType → List CValType → List Instr → Bool) : Prop :=
  ∀ C t g is, rec C t g is = true → allNum g = true → SeqOk C t g is

theorem allNum_app_i32 {l : List CValType} (h : allNum l = true) : allNum (l ++ [Ty.i32]) = true := by
  rw [allNum_append, h]
  rfl

theorem labelsEq_mem {C : Context} {lt : List CValType} :
    ∀ {ls : List LabelIdx}, labelsEq C lt ls = true → ∀ l ∈ ls, C.labels[l.toNat]? = some lt
  | [], _, _, hl => by cases hl
  | l :: ls, h, l', hl' => by
    simp only [labelsEq, Bool.and_eq_true] at h
    obtain ⟨h₁, h₂⟩ := h
    rcases List.mem_cons.mp hl' with rfl | hl'
    · split at h₁
      · rename_i lt' hl
        obtain ⟨rfl, _⟩ := numsEq_spec h₁
        exact hl
      · cases h₁
    · exact labelsEq_mem h₂ l' hl'

theorem resSub_bots (Δ : TypeCtx) :
    ∀ {g : List CValType}, allNum g = true → resSub Δ (List.replicate g.length .botv) g = true
  | [], _ => rfl
  | .num n :: g, h => by
    simp only [allNum] at h
    have ih := resSub_bots Δ h
    simp only [resSub, Sub.check, Sub.checkK, Ty.toList_ofList] at ih ⊢
    simp only [List.length_cons, List.replicate_succ, forall2B, ih, Bool.and_true]
    rfl

/-! ## One instruction -/

/-- What one case of `instrC` promises (`instrC_sound`). -/
def CaseOk (rec : Context → List CValType → List CValType → List Instr → Bool) (C : Context)
    (t : List CValType) (i : Instr) (c : Cls) : Prop :=
  (∀ t', instrC rec C t i c = .next t' → NextOk C t i t') ∧
    (instrC rec C t i c = .poly → PolyOk C t i)

/-- `instrC` on `other`. -/
theorem instrC_other {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {i : Instr} :
    CaseOk rec C t i (.other) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC, ofOpt] at h <;> split at h <;>
    cases h
  exact nextOk_of_atomG ‹_›

/-- `instrC` on `lget`. -/
theorem instrC_lget {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {x : LocalIdx} :
    CaseOk rec C t (.localGet x) (.lget x) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;> cases h
  exact nextOk_of_atomG (by simp [atomG, stepF, sigF, *, popsF, allNum])

/-- `instrC` on `lset`. -/
theorem instrC_lset {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {x : LocalIdx} :
    CaseOk rec C t (.localSet x) (.lset x) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> cases h
  rename_i a _ b hl hab
  obtain rfl := ntEq_eq hab
  exact nextOk_of_atomG (by simp [atomG, stepF, sigF, hl, popsF, numIs, ntEq_refl, allNum])

/-- `instrC` on `ltee`. -/
theorem instrC_ltee {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {x : LocalIdx} :
    CaseOk rec C t (.localTee x) (.ltee x) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> cases h
  rename_i a _ b hl hab
  obtain rfl := ntEq_eq hab
  exact nextOk_of_atomG (by simp [atomG, stepF, sigF, hl, popsF, numIs, ntEq_refl, allNum])

/-- `instrC` on `iconst`. -/
theorem instrC_iconst {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {ty : IntType} {bits : BitVec ty.width} :
    CaseOk rec C t (.intConst ty bits) (.iconst ty bits) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> cases h
  exact nextOk_of_atomG (by simp [atomG, stepF, sigF, numericType?, popsF, allNum])

/-- `instrC` on `ibin`. -/
theorem instrC_ibin {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {ty : IntType} {op : IntBinOp} :
    CaseOk rec C t (.intBinOp ty op) (.ibin ty op) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> cases h
  rename_i a b _ hab
  simp only [Bool.and_eq_true] at hab
  obtain rfl := ntEq_eq hab.1
  obtain rfl := ntEq_eq hab.2
  exact nextOk_of_atomG (by simp [atomG, stepF, sigF, numericType?, popsF, numIs, ntEq_refl,
    allNum])

/-- `instrC` on `irel`. -/
theorem instrC_irel {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {ty : IntType} {op : IntRelOp} :
    CaseOk rec C t (.intRelOp ty op) (.irel ty op) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> cases h
  rename_i a b _ hab
  simp only [Bool.and_eq_true] at hab
  obtain rfl := ntEq_eq hab.1
  obtain rfl := ntEq_eq hab.2
  exact nextOk_of_atomG (by simp [atomG, stepF, sigF, numericType?, popsF, numIs, ntEq_refl,
    allNum, Ty.i32])

/-- `instrC` on `itest`. -/
theorem instrC_itest {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {ty : IntType} {op : IntTestOp} :
    CaseOk rec C t (.intTestOp ty op) (.itest ty op) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> cases h
  rename_i a _ ha
  obtain rfl := ntEq_eq ha
  exact nextOk_of_atomG (by simp [atomG, stepF, sigF, numericType?, popsF, numIs, ntEq_refl,
    allNum, Ty.i32])

/-- `instrC` on `drop`. -/
theorem instrC_drop {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} :
    CaseOk rec C t (.drop) (.drop) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;> cases h
  exact nextOk_of_atomG (by simp [atomG, stepF, sigF, popsF, numIs, ntEq_refl, allNum])

/-- `instrC` on `gget`. -/
theorem instrC_gget {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {x : GlobalIdx} :
    CaseOk rec C t (.globalGet x) (.gget x) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;> cases h
  exact nextOk_of_atomG (by simp [atomG, stepF, sigF, numericType?, stepM, sigM, *, popsF,
    allNum])

/-- `instrC` on `gset`. -/
theorem instrC_gset {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {x : GlobalIdx} :
    CaseOk rec C t (.globalSet x) (.gset x) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> cases h
  rename_i a _ b hl hab
  obtain rfl := ntEq_eq hab
  exact nextOk_of_atomG (by simp [atomG, stepF, sigF, numericType?, stepM, sigM, hl, popsF,
    numIs, ntEq_refl, allNum])

/-- `instrC` on `block`. -/
theorem instrC_block {rec : Context → List CValType → List CValType → List Instr → Bool}
    (hrec : RecOk rec) {C : Context} {t : List CValType} {bt : BlockType} {body : List Instr} :
    CaseOk rec C t (.block bt body) (.block bt body) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> cases h
  rename_i t₁ t₂ hbt hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h₁, h₂⟩, hp⟩, hr⟩ := hc
  obtain ⟨r, hrv, hd, -⟩ := rev_of_popsF hp
  obtain ⟨xsb, kb, hseq, hset⟩ := hrec _ _ _ _ hr h₂
  rw [List.reverse_reverse] at hseq
  refine ⟨t₁.length, [], t₂, ?_, SetIn.nil C, resOk_num _ h₂, stack_after hrv hd⟩
  have hl : localsOk C xsb = true := localsOk_of_setIn hset
  rw [hrv]
  simp only [checkInstr, hbt, resOk_num _ h₁, resOk_num _ h₂, Bool.and_self, ite_true, hseq,
    hl, stepA_app _ h₁]

/-- `instrC` on `loop`. -/
theorem instrC_loop {rec : Context → List CValType → List CValType → List Instr → Bool}
    (hrec : RecOk rec) {C : Context} {t : List CValType} {bt : BlockType} {body : List Instr} :
    CaseOk rec C t (.loop bt body) (.loop bt body) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> cases h
  rename_i t₁ t₂ hbt hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h₁, h₂⟩, hp⟩, hr⟩ := hc
  obtain ⟨r, hrv, hd, -⟩ := rev_of_popsF hp
  obtain ⟨xsb, kb, hseq, hset⟩ := hrec _ _ _ _ hr h₂
  rw [List.reverse_reverse] at hseq
  refine ⟨t₁.length, [], t₂, ?_, SetIn.nil C, resOk_num _ h₂, stack_after hrv hd⟩
  have hl : localsOk C xsb = true := localsOk_of_setIn hset
  rw [hrv]
  simp only [checkInstr, hbt, resOk_num _ h₁, resOk_num _ h₂, Bool.and_self, ite_true, hseq,
    hl, stepA_app _ h₁]

/-- `instrC` on `if_`. -/
theorem instrC_if {rec : Context → List CValType → List CValType → List Instr → Bool}
    (hrec : RecOk rec) {C : Context} {t : List CValType} {bt : BlockType} {b₁ b₂ : List Instr} :
    CaseOk rec C t (.if_ bt b₁ b₂) (.if_ bt b₁ b₂) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> cases h
  rename_i t₁ t₂ hbt hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h₁, h₂⟩, hp⟩, hr₁⟩, hr₂⟩ := hc
  obtain ⟨r, hrv, hd, hn⟩ := rev_of_popsF hp
  obtain ⟨xs₁, k₁, hseq₁, hset₁⟩ := hrec _ _ _ _ hr₁ h₂
  obtain ⟨xs₂, k₂, hseq₂, hset₂⟩ := hrec _ _ _ _ hr₂ h₂
  rw [List.reverse_reverse] at hseq₁ hseq₂
  refine ⟨(t₁ ++ [Ty.i32]).length, [], t₂, ?_, SetIn.nil C, resOk_num _ h₂,
    stack_after hrv hd⟩
  have hl₁ : localsOk C xs₁ = true := localsOk_of_setIn hset₁
  have hl₂ : localsOk C xs₂ = true := localsOk_of_setIn hset₂
  rw [hrv]
  simp only [checkInstr, hbt, resOk_num _ h₁, resOk_num _ h₂, Bool.and_self, ite_true, hseq₁,
    hseq₂, hl₁, hl₂, stepA_app _ hn]

/-- `instrC` on `br`. -/
theorem instrC_br {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {l : LabelIdx} :
    CaseOk rec C t (.br l) (.br l) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> cases h
  rename_i ts hl hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨r, hrv, -, hn⟩ := rev_of_popsF hc.2
  refine ⟨ts, ?_⟩
  rw [hrv]
  simp only [checkInstr, directStep, hl, stepB_app _ hn]

/-- `instrC` on `brIf`. -/
theorem instrC_brIf {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {l : LabelIdx} :
    CaseOk rec C t (.brIf l) (.brIf l) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> cases h
  rename_i ts hl hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨r, hrv, hd, hn⟩ := rev_of_popsF hc.2
  refine ⟨(ts ++ [Ty.i32]).length, [], ts, ?_, SetIn.nil C, resOk_num _ hc.1,
    stack_after hrv hd⟩
  rw [hrv]
  simp only [checkInstr, directStep, hl, stepA_app _ hn]

theorem take_drop_top (r lt : List CValType) :
    ((r ++ (lt ++ [Ty.i32])).drop
      ((r ++ (lt ++ [Ty.i32])).length - (lt.length + 1))).take lt.length = lt := by
  have hl : (r ++ (lt ++ [Ty.i32])).length - (lt.length + 1) = r.length := by simp
  rw [hl, List.drop_left]
  simp

/-- `checkInstr` on `br_table` with every label of type `lt` (number types). -/
theorem checkInstr_brTable {C : Context} {ls : List LabelIdx} {l' : LabelIdx}
    {lt r : List CValType} (hl : C.labels[l'.toNat]? = some lt) (h₁ : allNum lt = true)
    (hmem : ∀ l ∈ ls, C.labels[l.toNat]? = some lt) :
    checkInstr atomC tyOkC C (r ++ (lt ++ [Ty.i32])) (.brTable ls l') =
      some (.poly (lt ++ [Ty.i32])) := by
  have hlen : lt.length + 1 ≤ (r ++ (lt ++ [Ty.i32])).length := by simp
  have hself : resSub C.toTypeCtx lt lt = true := resSub_self _ h₁
  simp only [checkInstr, directStep, hl, hlen, ite_true, take_drop_top, resOk_num _ h₁,
    List.all_cons, hself]
  split
  · exact stepB_app _ (allNum_app_i32 h₁) _
  · rename_i hne
    refine absurd ?_ hne
    simp only [Bool.true_and, List.all_eq_true]
    intro l hl'
    rw [hmem l hl']
    exact hself

/-- `instrC` on `brTable`. -/
theorem instrC_brTable {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {ls : List LabelIdx} {l' : LabelIdx} :
    CaseOk rec C t (.brTable ls l') (.brTable ls l') := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> cases h
  rename_i lt hl hc
  have hc' : (allNum lt = true ∧ popsF (lt ++ [Ty.i32]).reverse t = true) ∧
      labelsEq C lt ls = true := by simpa only [Bool.and_eq_true] using hc
  obtain ⟨r, hrv, -, -⟩ := rev_of_popsF hc'.1.2
  refine ⟨lt ++ [Ty.i32], ?_⟩
  rw [hrv]
  exact checkInstr_brTable hl hc'.1.1 (labelsEq_mem hc'.2)

/-- `instrC` on `ret`. -/
theorem instrC_ret {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} :
    CaseOk rec C t (.return_) (.ret) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> cases h
  rename_i ts hl hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨r, hrv, -, hn⟩ := rev_of_popsF hc.2
  refine ⟨ts, ?_⟩
  rw [hrv]
  simp only [checkInstr, directStep, hl, stepB_app _ hn]

/-- `instrC` on `unreach`. -/
theorem instrC_unreach {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} :
    CaseOk rec C t (.unreachable) (.unreach) := by
  refine ⟨fun t' h => ?_, fun _ => ⟨[], ?_⟩⟩
  · simp only [instrC] at h
    cases h
  · have := stepB_app C.toTypeCtx (ps := []) rfl t.reverse
    simp only [List.append_nil] at this
    simp only [checkInstr, directStep, this]

/-- `instrC` on `call`. -/
theorem instrC_call {rec : Context → List CValType → List CValType → List Instr → Bool}
    {C : Context} {t : List CValType} {x : FuncIdx} :
    CaseOk rec C t (.call x) (.call x) := by
  refine ⟨fun t' h => ?_, fun h => ?_⟩ <;> simp only [instrC] at h <;> split at h <;>
    (try split at h) <;> (try split at h) <;> cases h
  rename_i d hd _ ps rs hf hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h₁, h₂⟩, hp⟩ := hc
  obtain ⟨r, hrv, hdr, -⟩ := rev_of_popsF hp
  refine ⟨ps.toList.length, [], rs.toList, ?_, SetIn.nil C, resOk_num _ h₂,
    stack_after hrv hdr⟩
  rw [hrv]
  simp only [checkInstr, directStep, hd, hf, stepA_app _ h₁]

/-- **One instruction of `instrC`**, for a sound body checker `rec` and the class `c` of `i`. -/
theorem instrC_sound {rec : Context → List CValType → List CValType → List Instr → Bool}
    (hrec : RecOk rec) {C : Context} {t : List CValType} {i : Instr} {c : Cls}
    (hb : c ≠ .other → c.back = i) : CaseOk rec C t i c :=
  match c, hb with
  | .other, _ => instrC_other
  | .lget x, hb => by
    obtain rfl : (.localGet x : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_lget
  | .lset x, hb => by
    obtain rfl : (.localSet x : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_lset
  | .ltee x, hb => by
    obtain rfl : (.localTee x : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_ltee
  | .iconst ty bits, hb => by
    obtain rfl : (.intConst ty bits : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_iconst
  | .ibin ty op, hb => by
    obtain rfl : (.intBinOp ty op : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_ibin
  | .irel ty op, hb => by
    obtain rfl : (.intRelOp ty op : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_irel
  | .itest ty op, hb => by
    obtain rfl : (.intTestOp ty op : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_itest
  | .drop, hb => by
    obtain rfl : (.drop : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_drop
  | .gget x, hb => by
    obtain rfl : (.globalGet x : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_gget
  | .gset x, hb => by
    obtain rfl : (.globalSet x : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_gset
  | .block bt body, hb => by
    obtain rfl : (.block bt body : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_block hrec
  | .loop bt body, hb => by
    obtain rfl : (.loop bt body : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_loop hrec
  | .if_ bt b₁ b₂, hb => by
    obtain rfl : (.if_ bt b₁ b₂ : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_if hrec
  | .br l, hb => by
    obtain rfl : (.br l : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_br
  | .brIf l, hb => by
    obtain rfl : (.brIf l : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_brIf
  | .brTable ls l', hb => by
    obtain rfl : (.brTable ls l' : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_brTable
  | .ret, hb => by
    obtain rfl : (.return_ : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_ret
  | .unreach, hb => by
    obtain rfl : (.unreachable : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_unreach
  | .call x, hb => by
    obtain rfl : (.call x : Instr) = i := hb (fun h => Cls.noConfusion h)
    exact instrC_call

/-- The class of an instruction gives it back (`other` aside). -/
theorem back_classify (i : Instr) : classify i ≠ .other → (classify i).back = i := by
  cases i <;> first | (intro h; rfl) | (intro h; exact absurd rfl h)

/-- **One instruction of `instrN`**. -/
theorem instrN_sound {rec : Context → List CValType → List CValType → List Instr → Bool}
    (hrec : RecOk rec) {C : Context} {t : List CValType} {i : Instr} :
    (∀ t', instrN rec C t i = .next t' → NextOk C t i t') ∧
      (instrN rec C t i = .poly → PolyOk C t i) :=
  instrC_sound hrec (back_classify i)

/-! ## Sequences -/

/-- **A sequence of `runL`** with a sound step checker. -/
theorem runL_sound {step : Context → List CValType → Instr → StepG} {C : Context}
    {g : List CValType} (hg : allNum g = true)
    (hs : ∀ t i, (∀ t', step C t i = .next t' → NextOk C t i t') ∧
      (step C t i = .poly → PolyOk C t i)) :
    ∀ (is : List Instr) (t : List CValType), runL step C g t is = true → SeqOk C t g is
  | [], t, h => by
    simp only [runL] at h
    obtain ⟨heq, hn⟩ := numsEq_spec h
    refine ⟨[], 0, ?_, SetIn.nil C⟩
    have hr : resSub C.toTypeCtx t.reverse g = true := by
      rw [heq]
      exact resSub_self _ (heq ▸ hn)
    simp [checkSeq, hr, resOk_num _ hg, endPad]
  | i :: is, t, h => by
    simp only [runL] at h
    have hpad : padStack (padFor C false i) t.reverse = t.reverse := by
      simp [padFor, padStack]
    split at h
    · rename_i t' hst
      obtain ⟨n, xs, out, hc, hset, hro, hstk⟩ := (hs t i).1 t' hst
      obtain ⟨xs', k', hseq, hset'⟩ := runL_sound hg hs is t' h
      refine ⟨xs ++ xs', k' + (n - t.reverse.length), ?_, hset.append hset'⟩
      simp only [checkSeq, hpad, hc, localsOk_of_setIn hset, hro, Bool.and_self, ite_true,
        initLocals_self hset, hstk, hseq]
    · rename_i hst
      obtain ⟨t₁, hc⟩ := (hs t i).2 hst
      have hnil : is = [] := List.isEmpty_iff.mp h
      subst hnil
      refine ⟨[], t₁.length - t.reverse.length, ?_, SetIn.nil C⟩
      have hb : resSub C.toTypeCtx (List.replicate (endPad true [] g) .botv ++ []) g = true := by
        simp only [endPad, ite_true, List.length_nil, Nat.sub_zero, List.append_nil]
        exact resSub_bots _ hg
      simp only [checkSeq, hpad, hc, hb, resOk_num _ hg, Bool.and_self, ite_true]
    · cases h

/-- **The depth-bounded sequence checker is sound.** -/
theorem seqN_sound : ∀ n, RecOk (seqN n)
  | 0, _, _, _, _, h, _ => by simp [seqN] at h
  | n + 1, C, t, g, is, h, hg => by
    simp only [seqN] at h
    exact runL_sound hg (fun _ _ => instrN_sound (seqN_sound n)) is t h

/-- **`exprG` implies the default expression checker.** -/
theorem exprC_of_exprG {C : Context} {e : Expr} {ts : List CValType} (h : exprG C e ts = true) :
    exprC C e ts = true := by
  simp only [exprG, Bool.and_eq_true] at h
  obtain ⟨hn, hs⟩ := h
  obtain ⟨xs, k, hseq, -⟩ := seqN_sound depthBound C [] ts e hs hn
  simp only [List.reverse_nil] at hseq
  simp [exprC, checkExpr?, resOk_num _ hn, hseq]

end Silmaril.Proofs.Wasm.Auto2.Valid2
