module

public import Silmaril.Wasm.SpecTecLean.Defs

/-!
# Their `Step_pure` rules against Core 3.0, rule by rule

For a Core sequence in the fragment of `slAdmins?`, each of their transcribed rules holds at the
image exactly when the Core rule of the same name does (`slNop_iff`, …). Each transcription is
also sound for the generated constructor (`slNop_sound`, …).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTecLean

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-! ## Decoding the translation -/

theorem slAdmins?_cons_iff {a : Admin} {is : List Admin} {I : List SpecTecLean.instr} :
    slAdmins? (a :: is) = some I ↔
      ∃ x X, slAdmin? a = some x ∧ slAdmins? is = some X ∧ I = x :: X := by
  cases h1 : slAdmin? a <;> cases h2 : slAdmins? is <;> simp [slAdmins?, h1, h2, eq_comm]

theorem slAdmins?_eq_nil {is : List Admin} (h : slAdmins? is = some []) : is = [] := by
  cases is with
  | nil => rfl
  | cons a as =>
      obtain ⟨x, X, -, -, hI⟩ := slAdmins?_cons_iff.1 h
      cases hI

theorem slAdmins?_eq_cons {is : List Admin} {x : SpecTecLean.instr} {X : List SpecTecLean.instr}
    (h : slAdmins? is = some (x :: X)) :
    ∃ a as, is = a :: as ∧ slAdmin? a = some x ∧ slAdmins? as = some X := by
  cases is with
  | nil => cases h
  | cons a as =>
      obtain ⟨y, Y, hy, hY, hI⟩ := slAdmins?_cons_iff.1 h
      obtain ⟨rfl, rfl⟩ := List.cons.inj hI
      exact ⟨a, as, rfl, hy, hY⟩

/-- Every element of a sequence with an image has an image. -/
theorem slAdmins?_mem {is : List Admin} {I : List SpecTecLean.instr} {a : Admin}
    (h : slAdmins? is = some I) (ha : a ∈ is) : ∃ x, slAdmin? a = some x := by
  induction is generalizing I with
  | nil => cases ha
  | cons b bs ih =>
      obtain ⟨x, X, hx, hX, -⟩ := slAdmins?_cons_iff.1 h
      rcases List.mem_cons.1 ha with rfl | hm
      · exact ⟨x, hx⟩
      · exact ih hX hm

/-- Every instruction of the fragment, with its image. -/
theorem slAdmin?_dec {a : Admin} {x : SpecTecLean.instr} (h : slAdmin? a = some x) :
    (a = .plain .unreachable ∧ x = .UNREACHABLE) ∨ (a = .plain .nop ∧ x = .NOP) ∨
    (a = .plain .drop ∧ x = .DROP) ∨ (a = .plain (.select none) ∧ x = .SELECT none) ∨
    (∃ t b, a = .plain (.intConst t b) ∧ x = .CONST (numT t) (numSL t b)) ∨
    (∃ t, a = .plain (.intBinOp t .add) ∧ x = .BINOP (numT t) (.mk_binop__0 (addrT t) .ADD)) ∨
    (a = .trap ∧ x = .TRAP) := by
  cases a with
  | plain i =>
    simp only [slAdmin?] at h
    unfold slInstr? at h
    split at h <;> cases h <;>
      first | exact .inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, rfl⟩)))) | simp
  | trap => simp_all [slAdmin?]
  | _ => simp [slAdmin?] at h

theorem dec_UNREACHABLE {a : Admin} (h : slAdmin? a = some .UNREACHABLE) :
    a = .plain .unreachable := by
  rcases slAdmin?_dec h with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨_, _, -, h2⟩ |
    ⟨_, -, h2⟩ | ⟨-, h2⟩ <;> first | exact h1 | cases h2

theorem dec_NOP {a : Admin} (h : slAdmin? a = some .NOP) : a = .plain .nop := by
  rcases slAdmin?_dec h with ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨_, _, -, h2⟩ |
    ⟨_, -, h2⟩ | ⟨-, h2⟩ <;> first | exact h1 | cases h2

theorem dec_DROP {a : Admin} (h : slAdmin? a = some .DROP) : a = .plain .drop := by
  rcases slAdmin?_dec h with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨_, _, -, h2⟩ |
    ⟨_, -, h2⟩ | ⟨-, h2⟩ <;> first | exact h1 | cases h2

theorem dec_TRAP {a : Admin} (h : slAdmin? a = some .TRAP) : a = .trap := by
  rcases slAdmin?_dec h with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨_, _, -, h2⟩ |
    ⟨_, -, h2⟩ | ⟨h1, -⟩ <;> first | exact h1 | cases h2

theorem dec_SELECT {a : Admin} {t : Option (List SpecTecLean.valtype)}
    (h : slAdmin? a = some (.SELECT t)) : a = .plain (.select none) ∧ t = none := by
  rcases slAdmin?_dec h with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨h1, h2⟩ | ⟨_, _, -, h2⟩ |
    ⟨_, -, h2⟩ | ⟨-, h2⟩ <;> first | exact ⟨h1, by cases h2; rfl⟩ | cases h2

theorem dec_CONST {a : Admin} {nt : SpecTecLean.numtype} {c : SpecTecLean.num_}
    (h : slAdmin? a = some (.CONST nt c)) :
    ∃ t b, a = .plain (.intConst t b) ∧ nt = numT t ∧ c = numSL t b := by
  rcases slAdmin?_dec h with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨t, b, h1, h2⟩ |
    ⟨_, -, h2⟩ | ⟨-, h2⟩ <;> first | (cases h2; exact ⟨t, b, h1, rfl, rfl⟩) | cases h2

theorem dec_BINOP {a : Admin} {nt : SpecTecLean.numtype} {op : SpecTecLean.binop_}
    (h : slAdmin? a = some (.BINOP nt op)) :
    ∃ t, a = .plain (.intBinOp t .add) ∧ nt = numT t ∧ op = .mk_binop__0 (addrT t) .ADD := by
  rcases slAdmin?_dec h with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨_, _, -, h2⟩ |
    ⟨t, h1, h2⟩ | ⟨-, h2⟩ <;> first | (cases h2; exact ⟨t, h1, rfl, rfl⟩) | cases h2

/-- An instruction whose image is `instr_val v` is an integer constant, and `v` its value. -/
theorem dec_val {a : Admin} {v : SpecTecLean.val}
    (h : slAdmin? a = some (SpecTecLean.instr_val v)) :
    ∃ t b, a = .plain (.intConst t b) ∧ v = slVal t b := by
  cases v with
  | CONST nt c =>
      obtain ⟨t, b, h1, rfl, rfl⟩ := dec_CONST h
      exact ⟨t, b, h1, rfl⟩
  | _ =>
      rcases slAdmin?_dec h with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨_, _, -, h2⟩ |
        ⟨_, -, h2⟩ | ⟨-, h2⟩ <;> cases h2

/-- A Core value of the fragment is an integer constant. -/
theorem slAdmin?_toAdmin {v : Val} {x : SpecTecLean.instr} (h : slAdmin? v.toAdmin = some x) :
    ∃ t b, v = .num ⟨.int t, b⟩ ∧ x = SpecTecLean.instr_val (slVal t b) := by
  cases v with
  | num n =>
      obtain ⟨ty, b⟩ := n
      cases ty with
      | int t =>
          simp only [Val.toAdmin, slAdmin?, slInstr?, Option.some.injEq] at h
          exact ⟨t, b, rfl, h.symm⟩
      | float t => simp [Val.toAdmin, slAdmin?, slInstr?] at h
  | vec b => simp [Val.toAdmin, slAdmin?, slInstr?] at h
  | ref r => simp [Val.toAdmin, slAdmin?] at h

theorem numT_inj {t t' : IntType} (h : numT t = numT t') : t = t' := by
  cases t <;> cases t' <;> first | rfl | cases h

theorem slVal_inj {t t' : IntType} {b : BitVec t.width} {b' : BitVec t'.width}
    (h : slVal t b = slVal t' b') :
    (Admin.plain (.intConst t b) : Admin) = .plain (.intConst t' b') := by
  cases t <;> cases t' <;> simp_all [slVal, numT, numSL, addrT, BitVec.toNat_inj]

/-! ## Well-formedness of the images -/

theorem wf_uN_of_lt {N n : Nat} (h : n < 2 ^ N) : SpecTecLean.wf_uN N (.mk_uN n) := by
  refine .uN_case_0 N n ?_
  simp only [ge_iff_le, Nat.zero_le, decide_true, Bool.true_and, decide_eq_true_eq,
    Int.ofNat_eq_natCast]
  omega

theorem wf_numSL (t : IntType) (b : BitVec t.width) :
    SpecTecLean.wf_num_ (numT t) (numSL t b) := by
  cases t
  · exact .num__case_0 _ _ _ (wf_uN_of_lt b.isLt) rfl
  · exact .num__case_0 _ _ _ (wf_uN_of_lt b.isLt) rfl

theorem wf_slVal (t : IntType) (b : BitVec t.width) : SpecTecLean.wf_val (slVal t b) :=
  .val_case_0 _ _ (wf_numSL t b)

theorem wf_const (t : IntType) (b : BitVec t.width) :
    SpecTecLean.wf_instr (.CONST (numT t) (numSL t b)) :=
  .instr_case_76 _ _ (wf_numSL t b)

theorem wf_selectNone : SpecTecLean.wf_instr (.SELECT none) :=
  .instr_case_3 none (fun _ h => by simp at h)

/-! ## The transcriptions are their constructors -/

theorem slUnreachable_sound {I J : List SpecTecLean.instr} (h : SLUnreachable I J) :
    SpecTecLean.Step_pure I J := by
  obtain ⟨rfl, rfl, h1, h2⟩ := h
  exact .unreachable h1 h2

theorem slNop_sound {I J : List SpecTecLean.instr} (h : SLNop I J) :
    SpecTecLean.Step_pure I J := by
  obtain ⟨rfl, rfl, h1⟩ := h
  exact .nop h1

theorem slDrop_sound {I J : List SpecTecLean.instr} (h : SLDrop I J) :
    SpecTecLean.Step_pure I J := by
  obtain ⟨v, rfl, rfl, h1, h2⟩ := h
  exact .drop v h1 h2

theorem slSelectTrue_sound {I J : List SpecTecLean.instr} (h : SLSelectTrue I J) :
    SpecTecLean.Step_pure I J := by
  obtain ⟨v₁, v₂, c, t, rfl, rfl, h1, h2, h3, h4, h5, h6⟩ := h
  exact .select_true v₁ v₂ c t h1 h2 h3 h4 h5 h6

theorem slSelectFalse_sound {I J : List SpecTecLean.instr} (h : SLSelectFalse I J) :
    SpecTecLean.Step_pure I J := by
  obtain ⟨v₁, v₂, c, t, rfl, rfl, h1, h2, h3, h4, h5, h6⟩ := h
  exact .select_false v₁ v₂ c t h1 h2 h3 h4 h5 h6

theorem slBinopVal_sound {I J : List SpecTecLean.instr} (h : SLBinopVal I J) :
    SpecTecLean.Step_pure I J := by
  obtain ⟨nt, c₁, c₂, op, c, r, rfl, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact .binop_val nt c₁ c₂ op c r h1 h2 h3 h4 h5 h6 h7 h8 h9

/-! ## Rule by rule: their rule at the image iff the Core rule -/

section Rules

variable {is js : List Admin} {I J : List SpecTecLean.instr}

theorem slUnreachable_iff (hI : slAdmins? is = some I) (hJ : slAdmins? js = some J) :
    SLUnreachable I J ↔ CoreUnreachable is js := by
  constructor
  · rintro ⟨rfl, rfl, -, -⟩
    obtain ⟨a, as, rfl, ha, has⟩ := slAdmins?_eq_cons hI
    obtain ⟨b, bs, rfl, hb, hbs⟩ := slAdmins?_eq_cons hJ
    rw [dec_UNREACHABLE ha, slAdmins?_eq_nil has, dec_TRAP hb, slAdmins?_eq_nil hbs]
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    have hI' : I = [.UNREACHABLE] := (Option.some.inj hI).symm
    have hJ' : J = [.TRAP] := (Option.some.inj hJ).symm
    exact ⟨hI', hJ', .instr_case_1, .instr_case_115⟩

theorem slNop_iff (hI : slAdmins? is = some I) (hJ : slAdmins? js = some J) :
    SLNop I J ↔ CoreNop is js := by
  constructor
  · rintro ⟨rfl, rfl, -⟩
    obtain ⟨a, as, rfl, ha, has⟩ := slAdmins?_eq_cons hI
    rw [dec_NOP ha, slAdmins?_eq_nil has, slAdmins?_eq_nil hJ]
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    have hI' : I = [.NOP] := (Option.some.inj hI).symm
    have hJ' : J = [] := (Option.some.inj hJ).symm
    exact ⟨hI', hJ', .instr_case_0⟩

/-- The image of `v.toAdmin :: is`, for a Core value `v`. -/
theorem slAdmins?_val_cons {v : Val} {as : List Admin} {I : List SpecTecLean.instr}
    (h : slAdmins? (v.toAdmin :: as) = some I) :
    ∃ t b X, v = .num ⟨.int t, b⟩ ∧ slAdmins? as = some X ∧
      I = SpecTecLean.instr_val (slVal t b) :: X := by
  obtain ⟨x, X, hx, hX, rfl⟩ := slAdmins?_cons_iff.1 h
  obtain ⟨t, b, rfl, rfl⟩ := slAdmin?_toAdmin hx
  exact ⟨t, b, X, rfl, hX, rfl⟩

theorem slDrop_iff (hI : slAdmins? is = some I) (hJ : slAdmins? js = some J) :
    SLDrop I J ↔ CoreDrop is js := by
  constructor
  · rintro ⟨v, rfl, rfl, -, -⟩
    obtain ⟨a, as, rfl, ha, has⟩ := slAdmins?_eq_cons hI
    obtain ⟨d, ds, rfl, hd, hds⟩ := slAdmins?_eq_cons has
    obtain ⟨t, b, rfl, -⟩ := dec_val ha
    rw [dec_DROP hd, slAdmins?_eq_nil hds, slAdmins?_eq_nil hJ]
    exact ⟨.num ⟨.int t, b⟩, rfl, rfl⟩
  · rintro ⟨v, rfl, rfl⟩
    obtain ⟨t, b, X, rfl, hX, rfl⟩ := slAdmins?_val_cons hI
    have hX' : X = [.DROP] := (Option.some.inj hX).symm
    have hJ' : J = [] := (Option.some.inj hJ).symm
    exact ⟨slVal t b, by rw [hX'], hJ', wf_slVal t b, .instr_case_2⟩

/-- The image of `select`'s left-hand side: two integer values, an `i32` constant, and
`select` without annotation. -/
theorem select_lhs {I : List SpecTecLean.instr} {u₁ u₂ : SpecTecLean.val} {c : SpecTecLean.num_}
    {ts : Option (List SpecTecLean.valtype)}
    (hI : slAdmins? is = some I)
    (hI' : I = [SpecTecLean.instr_val u₁, SpecTecLean.instr_val u₂, .CONST .I32 c, .SELECT ts]) :
    ∃ (t₁ : IntType) (b₁ : BitVec t₁.width) (t₂ : IntType) (b₂ : BitVec t₂.width) (k : BitVec 32),
      is = [.plain (.intConst t₁ b₁), .plain (.intConst t₂ b₂),
      constI32 k, .plain (.select none)] ∧ u₁ = slVal t₁ b₁ ∧ u₂ = slVal t₂ b₂ ∧
      c = numSL .i32 k ∧ ts = none := by
  subst hI'
  obtain ⟨a₁, as₁, rfl, h₁, hs₁⟩ := slAdmins?_eq_cons hI
  obtain ⟨a₂, as₂, rfl, h₂, hs₂⟩ := slAdmins?_eq_cons hs₁
  obtain ⟨a₃, as₃, rfl, h₃, hs₃⟩ := slAdmins?_eq_cons hs₂
  obtain ⟨a₄, as₄, rfl, h₄, hs₄⟩ := slAdmins?_eq_cons hs₃
  obtain ⟨t₁, b₁, rfl, rfl⟩ := dec_val h₁
  obtain ⟨t₂, b₂, rfl, rfl⟩ := dec_val h₂
  obtain ⟨t₃, k, rfl, ht₃, rfl⟩ := dec_CONST h₃
  obtain rfl : t₃ = .i32 := numT_inj ht₃.symm
  obtain ⟨rfl, rfl⟩ := dec_SELECT h₄
  rw [slAdmins?_eq_nil hs₄]
  exact ⟨t₁, b₁, t₂, b₂, k, rfl, rfl, rfl, rfl, rfl⟩

/-- `select`'s test, at the image of an `i32` constant. -/
theorem selNe_iff (k : BitVec 32) :
    (SpecTecLean.proj_uN_0 (Option.get! (SpecTecLean.proj_num__0 (numSL .i32 k))) != 0) = true ↔
      k ≠ 0 := by
  show (k.toNat != 0) = true ↔ k ≠ 0
  rw [bne_iff_ne]
  exact not_congr ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => h ▸ rfl⟩

theorem selEq_iff (k : BitVec 32) :
    (SpecTecLean.proj_uN_0 (Option.get! (SpecTecLean.proj_num__0 (numSL .i32 k))) == 0) = true ↔
      k = 0 := by
  show (k.toNat == 0) = true ↔ k = 0
  rw [beq_iff_eq]
  exact ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => h ▸ rfl⟩

/-- The image of a Core `select` left-hand side. -/
theorem select_img {v₁ v₂ : Val} {k : BitVec 32} {ts : Option (List ValType)}
    (hI : slAdmins? [v₁.toAdmin, v₂.toAdmin, constI32 k, .plain (.select ts)] = some I) :
    ∃ t₁ b₁ t₂ b₂, v₁ = .num ⟨.int t₁, b₁⟩ ∧ v₂ = .num ⟨.int t₂, b₂⟩ ∧ ts = none ∧
      I = [SpecTecLean.instr_val (slVal t₁ b₁), SpecTecLean.instr_val (slVal t₂ b₂),
        .CONST .I32 (numSL .i32 k), .SELECT none] := by
  obtain ⟨t₁, b₁, X, rfl, hX, rfl⟩ := slAdmins?_val_cons hI
  obtain ⟨t₂, b₂, Y, rfl, hY, rfl⟩ := slAdmins?_val_cons hX
  cases ts with
  | none =>
      have hY' : Y = [.CONST .I32 (numSL .i32 k), .SELECT none] := (Option.some.inj hY).symm
      exact ⟨t₁, b₁, t₂, b₂, rfl, rfl, rfl, by rw [hY']⟩
  | some l => cases hY

theorem slSelectTrue_iff (hI : slAdmins? is = some I) (hJ : slAdmins? js = some J) :
    SLSelectTrue I J ↔ CoreSelectTrue is js := by
  constructor
  · rintro ⟨u₁, u₂, c, ts, hI', rfl, -, h2, -, -, -, -⟩
    obtain ⟨t₁, b₁, t₂, b₂, k, rfl, rfl, rfl, rfl, rfl⟩ := select_lhs hI hI'
    obtain ⟨a, as, rfl, ha, has⟩ := slAdmins?_eq_cons hJ
    obtain ⟨t, b, rfl, hv⟩ := dec_val ha
    rw [slAdmins?_eq_nil has, ← slVal_inj hv]
    exact ⟨.num ⟨.int t₁, b₁⟩, .num ⟨.int t₂, b₂⟩, k, none, (selNe_iff k).1 h2, rfl, rfl⟩
  · rintro ⟨v₁, v₂, k, ts, hk, rfl, rfl⟩
    obtain ⟨t₁, b₁, t₂, b₂, rfl, rfl, rfl, hI'⟩ := select_img hI
    have hJ' : J = [SpecTecLean.instr_val (slVal t₁ b₁)] := (Option.some.inj hJ).symm
    exact ⟨slVal t₁ b₁, slVal t₂ b₂, numSL .i32 k, none, hI', hJ', rfl, (selNe_iff k).2 hk,
      wf_slVal t₁ b₁, wf_slVal t₂ b₂, wf_const .i32 k, wf_selectNone⟩

theorem slSelectFalse_iff (hI : slAdmins? is = some I) (hJ : slAdmins? js = some J) :
    SLSelectFalse I J ↔ CoreSelectFalse is js := by
  constructor
  · rintro ⟨u₁, u₂, c, ts, hI', rfl, -, h2, -, -, -, -⟩
    obtain ⟨t₁, b₁, t₂, b₂, k, rfl, rfl, rfl, rfl, rfl⟩ := select_lhs hI hI'
    obtain rfl := (selEq_iff k).1 h2
    obtain ⟨a, as, rfl, ha, has⟩ := slAdmins?_eq_cons hJ
    obtain ⟨t, b, rfl, hv⟩ := dec_val ha
    rw [slAdmins?_eq_nil has, ← slVal_inj hv]
    exact ⟨.num ⟨.int t₁, b₁⟩, .num ⟨.int t₂, b₂⟩, none, rfl, rfl⟩
  · rintro ⟨v₁, v₂, ts, rfl, rfl⟩
    obtain ⟨t₁, b₁, t₂, b₂, rfl, rfl, rfl, hI'⟩ := select_img hI
    have hJ' : J = [SpecTecLean.instr_val (slVal t₂ b₂)] := (Option.some.inj hJ).symm
    exact ⟨slVal t₁ b₁, slVal t₂ b₂, numSL .i32 0, none, hI', hJ', rfl, (selEq_iff 0).2 rfl,
      wf_slVal t₁ b₁, wf_slVal t₂ b₂, wf_const .i32 0, wf_selectNone⟩

/-! ### `binop-val` at `add` -/

/-- Their `$iadd_` at the width of `t` is Core's `+`. -/
theorem iadd_numSL (t : IntType) (x y : BitVec t.width) :
    (SpecTecLean.num_.mk_num__0 (addrT t) (SpecTecLean.iadd_
      (SpecTecLean.sizenn (SpecTecLean.numtype_addrtype (addrT t))) (.mk_uN x.toNat)
      (.mk_uN y.toNat))) = numSL t (x + y) := by
  have hs : (x + y).toNat = (x.toNat + y.toNat) % 2 ^ t.width := BitVec.toNat_add x y
  cases t
  · show SpecTecLean.num_.mk_num__0 .I32 (.mk_uN ((x.toNat + y.toNat) % 2 ^ 32)) =
      .mk_num__0 .I32 (.mk_uN (x + y).toNat)
    rw [hs]; rfl
  · show SpecTecLean.num_.mk_num__0 .I64 (.mk_uN ((x.toNat + y.toNat) % 2 ^ 64)) =
      .mk_num__0 .I64 (.mk_uN (x + y).toNat)
    rw [hs]; rfl

/-- Their `$binop_` relation at `add` derives the image of Core's sum. -/
theorem funBinop_add (t : IntType) (x y : BitVec t.width) :
    SpecTecLean.fun_binop_ (numT t) (.mk_binop__0 (addrT t) .ADD) (numSL t x) (numSL t y)
      (some [numSL t (x + y)]) := by
  have hw := wf_numSL t (x + y)
  rw [← iadd_numSL] at hw ⊢
  cases t
  · exact .fun_binop__case_0 _ _ hw
  · exact .fun_binop__case_1 _ _ hw

/-- … and nothing else but `none` (the generated `otherwise` case). -/
theorem funBinop_add_inv {t : IntType} {x y : BitVec t.width}
    {r : Option (List SpecTecLean.num_)}
    (h : SpecTecLean.fun_binop_ (numT t) (.mk_binop__0 (addrT t) .ADD) (numSL t x) (numSL t y) r) :
    r = some [numSL t (x + y)] ∨ r = none := by
  rw [← iadd_numSL]
  cases t <;> cases h <;> first | exact .inl rfl | exact .inr rfl

theorem numSL_beq (t : IntType) (z w : BitVec t.width) :
    (numSL t z == numSL t w) = (z.toNat == w.toNat) := by
  cases t <;> rfl

theorem contains_numSL {t : IntType} {z w : BitVec t.width} :
    List.contains [numSL t w] (numSL t z) = true ↔ z = w := by
  have hc : List.contains [numSL t w] (numSL t z) = (numSL t z == numSL t w) := by
    unfold List.contains List.elem List.elem
    cases numSL t z == numSL t w <;> rfl
  rw [hc, numSL_beq, beq_iff_eq]
  exact ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => h ▸ rfl⟩

theorem wf_binopAdd (t : IntType) :
    SpecTecLean.wf_instr (.BINOP (numT t) (.mk_binop__0 (addrT t) .ADD)) := by
  cases t
  · exact .instr_case_78 _ _ (.binop__case_0 _ _ _ rfl)
  · exact .instr_case_78 _ _ (.binop__case_0 _ _ _ rfl)

/-- The image of `binop`'s left-hand side: two constants and `add`, all at one type. -/
theorem binop_lhs {nt : SpecTecLean.numtype} {c₁ c₂ : SpecTecLean.num_} {op : SpecTecLean.binop_}
    (hI : slAdmins? is = some [.CONST nt c₁, .CONST nt c₂, .BINOP nt op]) :
    ∃ (t : IntType) (x y : BitVec t.width),
      is = [.plain (.intConst t x), .plain (.intConst t y), .plain (.intBinOp t .add)] ∧
      nt = numT t ∧ c₁ = numSL t x ∧ c₂ = numSL t y ∧ op = .mk_binop__0 (addrT t) .ADD := by
  obtain ⟨a₁, as₁, rfl, h₁, hs₁⟩ := slAdmins?_eq_cons hI
  obtain ⟨a₂, as₂, rfl, h₂, hs₂⟩ := slAdmins?_eq_cons hs₁
  obtain ⟨a₃, as₃, rfl, h₃, hs₃⟩ := slAdmins?_eq_cons hs₂
  obtain ⟨t, x, rfl, rfl, rfl⟩ := dec_CONST h₁
  obtain ⟨t₂, y, rfl, ht₂, rfl⟩ := dec_CONST h₂
  obtain rfl := numT_inj ht₂
  obtain ⟨t₃, rfl, ht₃, rfl⟩ := dec_BINOP h₃
  obtain rfl := numT_inj ht₃
  rw [slAdmins?_eq_nil hs₃]
  exact ⟨t, x, y, rfl, rfl, rfl, rfl, rfl⟩

theorem slBinopVal_add_iff (hI : slAdmins? is = some I) (hJ : slAdmins? js = some J) :
    SLBinopVal I J ↔ CoreAdd is js := by
  constructor
  · rintro ⟨nt, c₁, c₂, op, c, r, rfl, rfl, hf, -, hr, hc, -⟩
    obtain ⟨t, x, y, rfl, rfl, rfl, rfl, rfl⟩ := binop_lhs hI
    obtain ⟨a, as, rfl, ha, has⟩ := slAdmins?_eq_cons hJ
    obtain ⟨t', z, rfl, ht', rfl⟩ := dec_CONST ha
    obtain rfl := numT_inj ht'
    rcases funBinop_add_inv hf with rfl | rfl
    · rw [slAdmins?_eq_nil has, contains_numSL.1 hc]
      exact ⟨t, x, y, rfl, rfl⟩
    · cases hr
  · rintro ⟨t, x, y, rfl, rfl⟩
    have hI' : I = [.CONST (numT t) (numSL t x), .CONST (numT t) (numSL t y),
        .BINOP (numT t) (.mk_binop__0 (addrT t) .ADD)] := (Option.some.inj hI).symm
    have hJ' : J = [.CONST (numT t) (numSL t (x + y))] := (Option.some.inj hJ).symm
    have hall : SpecTecLean.Forall (fun w => SpecTecLean.wf_num_ (numT t) w) [numSL t (x + y)] :=
      fun w hw => (List.mem_singleton.1 hw) ▸ wf_numSL t (x + y)
    exact ⟨numT t, numSL t x, numSL t y, _, numSL t (x + y), some [numSL t (x + y)], hI', hJ',
      funBinop_add t x y, by simp, rfl, contains_numSL.2 rfl, hall, wf_const t x, wf_const t y,
      wf_binopAdd t, wf_const t (x + y)⟩

end Rules

end Silmaril.Wasm.SpecTecLean
