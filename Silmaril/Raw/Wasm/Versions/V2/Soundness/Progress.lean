module

public import Silmaril.Raw.Wasm.Versions.V2.Soundness.Preservation

/-!
# WebAssembly 2.0 soundness: progress

`Config.progress`: a well-typed configuration is **terminal** — a value stack or
`TRAP` (`4-runtime:46`) — or it steps.

**Deviation (no SpecTec source).** As recorded in
`Silmaril/Wasm/V2/Soundness/Store.lean`, the pinned SpecTec wasm-2.0 sources
(WebAssembly/spec `608711107b7f1edb13efd57b7d79b49477462d36`, see
`specs/wasm/core-2.0.json`) contain **no `7-soundness` file**, so 2.0 states no
progress theorem. The statement below is the W3C WebAssembly 2.0 appendix
*Soundness*, theorem "Progress", cross-checked against the Core 3.0 development
(`Silmaril/Wasm/Execution/Core/Soundness/Progress.lean` and
`.../ProgressControl.lean`). 2.0 is far smaller: no subtyping between concrete
types, no defined or recursive types, no `Expand`, no GC, no exceptions, no
handlers, no tail calls, no multiple or 64-bit memories, no relaxed SIMD and no
local-initialisation tracking, so none of 3.0's machinery for those appears
here.

## Progress fails for Wasm 2.0 exactly as SpecTec writes it

This is decided deviation 3 (an earlier decision record). `1-syntax:470-472` attaches
`;; TODO: missing constraints` to `VCVTOP shape shape vcvtop`, and
`Instr_ok/vcvtop` (`6-typing:365`) is correspondingly **unconditional**. Under
that literal reading

    VCVTOP (I8 X 16) (F64 X 2) (EXTEND LOW S)

is a well-typed instruction of type `V128 -> V128`, and `Step_pure/vcvtop-*`
(`8-reduction:353,360,367`) has no instance for it: `$vcvtop__` is undefined on
that shape pair. So `(VCONST V128 c) (VCVTOP (I8 X 16) (F64 X 2) (EXTEND LOW S))`
is a closed, well-typed, non-terminal configuration with no reduct — progress is
*false* for the literal 2.0 rules. `vcvtop_badShape_stuck` below is that
counterexample, proved with no `sorry` and stated for the **full** `Step`
relation (`8-reduction:5`), which is what `Config.progress` quantifies over: no
`Step/pure`, `Step/read`, context or state-writing rule applies to it. The
`example` after it checks that
our `Instr.immediatesValid` (and hence `Instr_ok/vcvtop`, which carries
`VecCvtOp.valid target source` as a premise) rejects the instruction. **That
premise is why progress holds here.**

## The same defect once more: scalar `CVTOP`

`1-syntax:437` declares `CVTOP numtype_1 numtype_2 cvtop` with the **flat**
operator set `cvtop ::= EXTEND sx | WRAP | CONVERT sx | TRUNC sx | TRUNC_SAT sx |
PROMOTE | DEMOTE` (`1-syntax:305-312`) — unlike `unop_(numtype)` and friends it
is *not* indexed by the type — and the only syntactic side condition is
`numtype_1 =/= numtype_2`. Read literally, `Instr_ok/cvtop-convert`
(`6-typing:285`) is then unconditional; the pinned source even carries the
comment `;; TODO: move side conditions to syntax` at `6-typing:280`. So

    CVTOP I64 I32 WRAP

would be well typed as `I32 -> I64` and would have **no** `Step_pure/cvtop-*`
instance: `CvtOp.toShared` (`V2/Ops.lean`) returns `none` and both
`CvtOpResult` and `CvtOpTraps` (`V2/Execution/Numerics.lean`) are `False` there.
`cvtop_badOp_stuck` below is that counterexample, proved with no `sorry` and,
like the vector one, stated for the full `Step` relation.

This is **decided deviation 16**: `Instr.immediatesValid`
(`Silmaril/Wasm/V2/Instructions.lean`) and `InstrOk.cvtOpConvert`
(`Silmaril/Wasm/V2/Validation/Instructions.lean`) both carry the definedness
premise `(op.toShared target source).isSome`, which is exactly
"`$cvtop__(nt_2, nt_1, op, ·)` is defined". `cvtop_badOp_not_ok` below checks
that the instruction above is rejected, and that premise is what makes the
`cvtop` case of `numeric_progress` — and hence `Config.progress` — true.

## Shape of the proof

Progress is one induction (`progress_aux`) on the typing derivation of
administrative code, generalised over

* the frame — the body of a `FRAME_` runs in its own frame;
* a prefix of values typed by the parameters of the code;
* the typing context, related to the frame's context by `CtxOk` (which is
  `CtxUnder` of `Soundness/Preservation.lean` plus a `Frame_ok`): its labels and
  return type are those of the enclosing `LABEL_`s and `FRAME_`, which is what
  makes `br l` and `return` well scoped.

The outcome of a typed piece of code (`Out`) is: a value stack typed by the
results, a step, or one of the three *exit forms* that the enclosing
administrative instruction consumes — a trap, a branch to an enclosing label
with enough operands, or a `return` with enough operands. Core 3.0's `Out` has
two more (a thrown exception and a pending `return_call_ref`); 2.0 has neither.

The per-instruction work is sharded by instruction family, mirroring the
preservation shards of `Soundness/Preservation.lean`: `parametric_progress`,
`numeric_progress`, `vector_progress`, `reference_progress`, `local_progress`,
`global_progress`, `table_progress`, `memory_progress`, `data_progress`,
`control_progress`, `call_progress` and `callAddr_progress` (the administrative
`CALL_ADDR`). `Instr.family` is the partition; `plain_progress` is the dispatch.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Memory (Bytes readBytes writeBytes)

variable {H : Type}

/-! ## List plumbing -/

/-- Split a `Forall₂` along a split of the right-hand list. -/
theorem forall₂_split {α β : Type} {R : α → β → Prop} {l : List α} {m₁ m₂ : List β}
    (h : List.Forall₂ R l (m₁ ++ m₂)) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂ := by
  induction m₁ generalizing l with
  | nil => exact ⟨[], l, rfl, .nil, h⟩
  | cons b m₁ ih =>
    cases h with
    | cons hab h =>
      obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := ih h
      exact ⟨_ :: l₁, l₂, rfl, .cons hab h₁, h₂⟩

/-- Every list splits with a suffix of any admissible length. -/
theorem exists_split_right {α : Type} (l : List α) (n : Nat) (h : n ≤ l.length) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₂.length = n :=
  ⟨l.take (l.length - n), l.drop (l.length - n), (List.take_append_drop _ _).symm,
    by simp; omega⟩

/-- `vals vs₀ ++ as` is a value stack only if `as` is. -/
theorem vals_append_eq_vals {vs₀ vs₁ : List Val} {l : List Admin}
    (h : vals vs₀ ++ l = vals vs₁) : ∃ w, l = vals w := by
  unfold vals at h
  obtain ⟨-, l₂, -, -, e⟩ := List.map_eq_append_iff.mp h.symm
  exact ⟨l₂, e.symm⟩

/-- `vals (vs ++ [v]) ++ l = vals vs ++ (v.toAdmin :: l)`. -/
theorem vals_snoc_append (vs : List Val) (v : Val) (l : List Admin) :
    vals (vs ++ [v]) ++ l = vals vs ++ (v.toAdmin :: l) := by simp [vals]

/-! ## Canonical forms

A well-typed runtime value at each 2.0 value type. 2.0 has no subtyping between
concrete types, so `Val_ok` (`wasm-3.0/4.1-execution.values.spectec:72-83`) pins
the value's shape exactly:
these are inversions of `ValOk`/`RefOk` from `Soundness/Store.lean`. -/

/-- **Canonical forms, integers.** A value of type `Inn` is `(CONST Inn c)`. -/
theorem ValOk.int_inv {s : Store H} {v : Val} {t : IntType}
    (h : ValOk s v (.num (.int t))) :
    ∃ c : BitVec t.width, v = .num ⟨.int t, c⟩ ∧ v.toAdmin = .plain (.intConst t c) := by
  rcases v with ⟨nt, b⟩ | b | r
  · cases nt with
    | int t' => cases h; exact ⟨b, rfl, rfl⟩
    | float t' => cases h
  · cases h
  · cases h

/-- **Canonical forms, `I32`.** -/
theorem ValOk.i32_inv {s : Store H} {v : Val} (h : ValOk s v .i32) :
    ∃ c : BitVec 32, v = .num ⟨.int .i32, c⟩ ∧ v.toAdmin = constI32 c :=
  ValOk.int_inv h

/-- **Canonical forms, `I64`.** -/
theorem ValOk.i64_inv {s : Store H} {v : Val} (h : ValOk s v .i64) :
    ∃ c : BitVec 64, v = .num ⟨.int .i64, c⟩ ∧ v.toAdmin = .plain (.intConst .i64 c) :=
  ValOk.int_inv h

/-- **Canonical forms, floats.** A value of type `Fnn` is `(CONST Fnn c)`. -/
theorem ValOk.float_inv {s : Store H} {v : Val} {t : FloatType}
    (h : ValOk s v (.num (.float t))) :
    ∃ c : BitVec t.width, v = .num ⟨.float t, c⟩ ∧ v.toAdmin = .plain (.floatConst t c) := by
  rcases v with ⟨nt, b⟩ | b | r
  · cases nt with
    | int t' => cases h
    | float t' => cases h; exact ⟨b, rfl, rfl⟩
  · cases h
  · cases h

/-- **Canonical forms, `F32`.** -/
theorem ValOk.f32_inv {s : Store H} {v : Val} (h : ValOk s v .f32) :
    ∃ c : BitVec 32, v = .num ⟨.float .f32, c⟩ ∧ v.toAdmin = .plain (.floatConst .f32 c) :=
  ValOk.float_inv h

/-- **Canonical forms, `F64`.** -/
theorem ValOk.f64_inv {s : Store H} {v : Val} (h : ValOk s v .f64) :
    ∃ c : BitVec 64, v = .num ⟨.float .f64, c⟩ ∧ v.toAdmin = .plain (.floatConst .f64 c) :=
  ValOk.float_inv h

/-- **Canonical forms, vectors.** A value of type `V128` is `(VCONST V128 c)`. -/
theorem ValOk.vec_inv {s : Store H} {v : Val} (h : ValOk s v .v128) :
    ∃ c : BitVec 128, v = .vec c ∧ v.toAdmin = vconst c := by
  rcases v with ⟨nt, b⟩ | b | r
  · cases h
  · cases h; exact ⟨b, rfl, rfl⟩
  · cases h

/-- **Canonical forms, numbers.** A value of a number type is a `CONST` of that
type. -/
theorem ValOk.num_inv {s : Store H} {v : Val} {t : NumType}
    (h : ValOk s v (.num t)) : ∃ c : BitVec t.width, v = .num ⟨t, c⟩ := by
  rcases v with ⟨nt, b⟩ | b | r
  · cases h; exact ⟨b, rfl⟩
  · cases h
  · cases h

/-- **Canonical forms, references.** A value of a reference type is a reference
typed at it. -/
theorem ValOk.ref_inv {s : Store H} {v : Val} {rt : RefType} (h : ValOk s v (.ref rt)) :
    ∃ r : Ref, v = .ref r ∧ RefOk s r rt := by
  rcases v with ⟨nt, b⟩ | b | r
  · cases h
  · cases h
  · cases h with | ref hr => exact ⟨r, rfl, hr⟩

/-- **Canonical forms, `FUNCREF`.** A `funcref` is `REF.NULL FUNCREF` or an
allocated `REF.FUNC_ADDR`. -/
theorem RefOk.funcref_inv {s : Store H} {r : Ref} (h : RefOk s r .funcref) :
    r = .null .funcref ∨
      ∃ (a : FuncAddr) (fi : FuncInst H), r = .funcAddr a ∧ s.funcInst? a = some fi := by
  cases h with
  | null t => exact .inl rfl
  | funcAddr hf => exact .inr ⟨_, _, rfl, hf⟩

/-- **Canonical forms, `EXTERNREF`.** An `externref` is `REF.NULL EXTERNREF` or
a `REF.HOST_ADDR`. -/
theorem RefOk.externref_inv {s : Store H} {r : Ref} (h : RefOk s r .externref) :
    r = .null .externref ∨ ∃ a : HostAddr, r = .hostAddr a := by
  cases h with
  | null t => exact .inl rfl
  | hostAddr a => exact .inr ⟨a, rfl⟩

/-- A typed value stack has no `BOT` in its type, so 2.0 subtyping is trivial on
it: `Resulttype_sub` (`6-typing:80`) transports `ValsOk`. -/
theorem ValsOk.sub {s : Store H} {vs : List Val} {ts ts' : CResultType}
    (h : ValsOk s vs ts) (hsub : CResultType.Sub ts ts') : ValsOk s vs ts' := by
  induction hsub generalizing vs with
  | nil => cases h; exact .nil
  | cons h1 _ ih =>
    cases h with
    | cons hv hvs =>
      obtain ⟨t, rfl, hvt⟩ := hv
      obtain rfl := CValType.sub_val_iff.mp h1
      exact .cons ⟨t, rfl, hvt⟩ (ih hvs)

/-! ## `Step` inversion for a two-instruction configuration

The two unsoundness witnesses below have to be irreducible under the **full**
`Step` relation (`8-reduction:5`), which is what `Config.progress` quantifies
over, not merely under its pure fragment `Step_pure` (`8-reduction:6`). The
three lemmas here do that inversion once and for all. -/

/-- The contiguous sublists of a two-element list are exactly `eps`, each of the
two elements, and the list itself. -/
theorem infix_pair {α : Type} {a b : α} {l : List α} (h : l <:+: [a, b]) :
    l = [] ∨ l = [a] ∨ l = [b] ∨ l = [a, b] := by
  obtain ⟨p, q, hpq⟩ := h
  rcases p with _ | ⟨x, _ | ⟨x2, p2⟩⟩ <;>
    rcases l with _ | ⟨y, _ | ⟨z, l⟩⟩ <;> simp_all

/-- An administrative instruction that is not a value is not the image of one. -/
theorem Admin.ne_toAdmin {a : Admin} (h : a.val? = none) (v : Val) : a ≠ v.toAdmin := by
  intro hv
  have h2 := Admin.val?_toAdmin v
  rw [← hv, h] at h2
  exact absurd h2 (by simp)

/-- `val instr` contains no administrative instruction other than `val` and
`instr`; in particular no `LABEL_`, `FRAME_` or `CALL_ADDR`. -/
theorem false_of_mem_pair {v : Val} {i : Instr} {a : Admin}
    (hmem : a ∈ [v.toAdmin, Admin.plain i])
    (hav : a.val? = none) (hai : a ≠ .plain i) : False := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact Admin.ne_toAdmin hav v rfl
  · exact hai rfl

/-- **`Step` inversion for a two-instruction stuck configuration.**

For a code `val instr` built from a value `v` and an instruction `i` such that

* no `Step_pure` and no `Step_read` rule applies to `val instr` or to `instr`
  alone (`hp1`, `hp2`, `hr1`, `hr2`; the shapes `eps` and `val` are handled by
  `PureStep.not_allVals`/`ReadStep.not_allVals`), and
* `i` is none of the five instructions whose `Step` rule has a left-hand side of
  at most two administrative instructions — `LOCAL.SET` (`8-reduction:380`),
  `GLOBAL.SET` (`:392`), `ELEM.DROP` (`:483`), `DATA.DROP` (`:663`) and
  `MEMORY.GROW` (`:600`, `:605`),

no `Step` rule applies. The conclusion is stated for every *contiguous sublist*
of `val instr`, which is what makes it an invariant of `Step/ctxt-instrs`: that
rule splits the code as `val* admininstr* admininstr*` and recurses on the
middle part, which is again a sublist. The remaining rules either introduce a
`LABEL_`, a `FRAME_` or a `CALL_ADDR` — none of which occurs in `val instr` — or
have a three-instruction left-hand side, which is too long to be a sublist. -/
theorem noStep_of_infix_two {P : Profile} {host : HostSemantics H} {v : Val} {i : Instr}
    (hp1 : ∀ is', ¬ PureStep P [Admin.plain i] is')
    (hp2 : ∀ is', ¬ PureStep P [v.toAdmin, Admin.plain i] is')
    (hr1 : ∀ (s : Store H) (f : Frame) is', ¬ ReadStep s f [Admin.plain i] is')
    (hr2 : ∀ (s : Store H) (f : Frame) is', ¬ ReadStep s f [v.toAdmin, Admin.plain i] is')
    (hls : ∀ x, i ≠ .localSet x) (hgs : ∀ x, i ≠ .globalSet x)
    (hed : ∀ x, i ≠ .elemDrop x) (hdd : ∀ x, i ≠ .dataDrop x)
    (hmg : i ≠ .memoryGrow)
    {c c' : Config H} (h : Step P host c c') :
    ¬ c.code <:+: [v.toAdmin, Admin.plain i] := by
  induction h with
  | pure hs =>
    intro hinf
    dsimp only at hinf
    rcases infix_pair hinf with h' | h' | h' | h' <;> rw [h'] at hs
    · exact absurd hs.not_allVals (by simp)
    · exact absurd hs.not_allVals (by simp)
    · exact hp1 _ hs
    · exact hp2 _ hs
  | read hs =>
    intro hinf
    dsimp only at hinf
    rcases infix_pair hinf with h' | h' | h' | h' <;> rw [h'] at hs
    · exact absurd hs.not_allVals (by simp)
    · exact absurd hs.not_allVals (by simp)
    · exact hr1 _ _ _ hs
    · exact hr2 _ _ _ hs
  | ctxtInstrs _ _ ih =>
    intro hinf
    dsimp only at hinf ih ⊢
    exact ih ((List.infix_append _ _ _).trans hinf)
  | ctxtLabel _ _ =>
    intro hinf
    dsimp only at hinf
    exact false_of_mem_pair (hinf.subset (List.mem_cons_self ..))
      (by simp [Admin.val?]) (by simp)
  | ctxtFrame _ _ =>
    intro hinf
    dsimp only at hinf
    exact false_of_mem_pair (hinf.subset (List.mem_cons_self ..))
      (by simp [Admin.val?]) (by simp)
  | callAddrHost _ _ _ _ =>
    intro hinf
    dsimp only at hinf
    exact false_of_mem_pair
      (hinf.subset (List.mem_append_right _ (List.mem_cons_self ..)))
      (by simp [Admin.val?]) (by simp)
  | callAddrHostDiv _ _ _ _ =>
    intro hinf
    dsimp only at hinf
    exact false_of_mem_pair
      (hinf.subset (List.mem_append_right _ (List.mem_cons_self ..)))
      (by simp [Admin.val?]) (by simp)
  | localSet _ =>
    intro hinf
    dsimp only at hinf
    exact false_of_mem_pair
      (hinf.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (by simp [Admin.val?]) (by simpa using fun h => hls _ h.symm)
  | globalSet _ _ =>
    intro hinf
    dsimp only at hinf
    exact false_of_mem_pair
      (hinf.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (by simp [Admin.val?]) (by simpa using fun h => hgs _ h.symm)
  | elemDrop _ _ =>
    intro hinf
    dsimp only at hinf
    exact false_of_mem_pair (hinf.subset (List.mem_cons_self ..))
      (by simp [Admin.val?]) (by simpa using fun h => hed _ h.symm)
  | dataDrop _ _ =>
    intro hinf
    dsimp only at hinf
    exact false_of_mem_pair (hinf.subset (List.mem_cons_self ..))
      (by simp [Admin.val?]) (by simpa using fun h => hdd _ h.symm)
  | memoryGrowSucceed _ _ _ _ =>
    intro hinf
    dsimp only at hinf
    exact false_of_mem_pair
      (hinf.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (by simp [Admin.val?]) (by simpa using fun h => hmg h.symm)
  | memoryGrowFail _ _ _ =>
    intro hinf
    dsimp only at hinf
    exact false_of_mem_pair
      (hinf.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (by simp [Admin.val?]) (by simpa using fun h => hmg h.symm)
  | _ =>
    intro hinf
    dsimp only at hinf
    exact absurd hinf.length_le (by simp)

/-- `noStep_of_infix_two` at the whole code `val instr`: the configuration
`s; f; val instr` is irreducible under `Step`. -/
theorem noStep_two {P : Profile} {host : HostSemantics H} {v : Val} {i : Instr}
    {s : Store H} {f : Frame}
    (hp1 : ∀ is', ¬ PureStep P [Admin.plain i] is')
    (hp2 : ∀ is', ¬ PureStep P [v.toAdmin, Admin.plain i] is')
    (hr1 : ∀ (s : Store H) (f : Frame) is', ¬ ReadStep s f [Admin.plain i] is')
    (hr2 : ∀ (s : Store H) (f : Frame) is', ¬ ReadStep s f [v.toAdmin, Admin.plain i] is')
    (hls : ∀ x, i ≠ .localSet x) (hgs : ∀ x, i ≠ .globalSet x)
    (hed : ∀ x, i ≠ .elemDrop x) (hdd : ∀ x, i ≠ .dataDrop x)
    (hmg : i ≠ .memoryGrow) :
    ¬ ∃ c', Step P host ⟨s, f, [v.toAdmin, Admin.plain i]⟩ c' := by
  rintro ⟨c', h⟩
  exact noStep_of_infix_two hp1 hp2 hr1 hr2 hls hgs hed hdd hmg h List.infix_rfl

/-! ## Deviation #676: the literal 2.0 `VCVTOP` is stuck

`Instr_ok/vcvtop` (`6-typing:365`) has no shape premise in SpecTec 2.0, and
`1-syntax:472` says `TODO: missing constraints`. The instruction below is what
that literal reading admits; it has no reduct. -/

/-- **No `Step_pure` rule applies to the witness for deviation #676.**
`VCVTOP (I8 X 16) (F64 X 2) (EXTEND LOW S)` applied to a `V128` matches no
left-hand side of `Step_pure` (`8-reduction:6`), for any `Numerics.Profile`. -/
theorem vcvtop_badShape_noPureStep {P : Profile} (c : BitVec 128) :
    ¬ ∃ as, PureStep P
      [(Val.vec c).toAdmin,
        .plain (.vecCvtOp (.int .i8x16) (.float .f64x2) (.extend .low .signed))] as := by
  rintro ⟨as, h⟩
  generalize hL : [(Val.vec c).toAdmin,
    Admin.plain (.vecCvtOp (.int .i8x16) (.float .f64x2) (.extend .low .signed))] = L at h
  cases h with
  | vecCvtOp hr =>
    rename_i target source op c₀ r
    simp only [Val.toAdmin, vconst, List.cons.injEq, Admin.plain.injEq, Instr.vecConst.injEq,
      Instr.vecCvtOp.injEq, and_true] at hL
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hL
    simp only [VecCvtOpResult, Numerics.VecConvertRel, VecCvtOp.toShared] at hr
    cases hP : P.nan <;> rw [hP] at hr <;>
      simp only [Numerics.vcvtopRel, Numerics.vcvtop, reduceCtorEq] at hr
  | trapVals hne =>
    have hmem : Admin.trap ∈ [(Val.vec c).toAdmin,
        Admin.plain (.vecCvtOp (.int .i8x16) (.float .f64x2) (.extend .low .signed))] := by
      rw [hL]; simp
    simp [Val.toAdmin] at hmem
  | _ => exact absurd hL (by simp [Val.toAdmin, vconst, vals])

/-- The vector conversion alone, with no operand, is no `Step_pure` redex. -/
theorem vcvtop_badShape_noPureStep1 {P : Profile} (is' : List Admin) :
    ¬ PureStep P
      [Admin.plain (.vecCvtOp (.int .i8x16) (.float .f64x2) (.extend .low .signed))] is' := by
  intro h
  generalize hL :
    [Admin.plain (Instr.vecCvtOp (.int .i8x16) (.float .f64x2) (.extend .low .signed))] = L at h
  cases h <;> simp_all [vconst, vals, List.cons_eq_append_iff]

/-- The vector conversion alone is no `Step_read` redex either: no `Step_read`
rule (`8-reduction:7`) mentions `VCVTOP`. -/
theorem vcvtop_badShape_noReadStep1 {s : Store H} {f : Frame} (is' : List Admin) :
    ¬ ReadStep s f
      [Admin.plain (.vecCvtOp (.int .i8x16) (.float .f64x2) (.extend .low .signed))] is' := by
  intro h
  generalize hL :
    [Admin.plain (Instr.vecCvtOp (.int .i8x16) (.float .f64x2) (.extend .low .signed))] = L at h
  cases h <;> simp_all [vconst, vals, constI32, List.cons_eq_append_iff]

/-- No `Step_read` rule applies to the witness either. -/
theorem vcvtop_badShape_noReadStep {s : Store H} {f : Frame} {c : BitVec 128}
    (is' : List Admin) :
    ¬ ReadStep s f
      [(Val.vec c).toAdmin,
        .plain (.vecCvtOp (.int .i8x16) (.float .f64x2) (.extend .low .signed))] is' := by
  intro h
  generalize hL : [(Val.vec c).toAdmin,
    Admin.plain (.vecCvtOp (.int .i8x16) (.float .f64x2) (.extend .low .signed))] = L at h
  cases h <;> simp_all [vconst, vals, constI32, Val.toAdmin, List.cons_eq_append_iff]

/-- **The witness for deviation #676.** `VCVTOP (I8 X 16) (F64 X 2) (EXTEND LOW S)`
applied to a `V128` is genuinely stuck: **no `Step` rule at all** applies, in any
store, under any frame, for any `Numerics.Profile` and any host semantics.
Together with `Instr_ok/vcvtop` being unconditional in SpecTec 2.0, this is why
**progress fails for Wasm 2.0 exactly as SpecTec writes it** — the configuration
is closed, well typed at `eps -> V128`, non-terminal and irreducible — and why
`Instr.immediatesValid` and `InstrOk.vecCvtOp` carry the premise
`VecCvtOp.valid target source`. -/
theorem vcvtop_badShape_stuck {P : Profile} {host : HostSemantics H} (c : BitVec 128)
    (s : Store H) (f : Frame) :
    ¬ ∃ c', Step P host ⟨s, f,
      [(Val.vec c).toAdmin,
        .plain (.vecCvtOp (.int .i8x16) (.float .f64x2) (.extend .low .signed))]⟩ c' :=
  noStep_two vcvtop_badShape_noPureStep1
    (fun _ h => vcvtop_badShape_noPureStep c ⟨_, h⟩)
    (fun _ _ => vcvtop_badShape_noReadStep1) (fun _ _ => vcvtop_badShape_noReadStep)
    (by simp) (by simp) (by simp) (by simp) (by simp)

/-- The syntactic side condition our development adds, checked on the witness:
`Instr.immediatesValid` rejects it, so no 2.0 module we accept contains it. -/
example :
    ¬ (Instr.vecCvtOp (.int .i8x16) (.float .f64x2) (.extend .low .signed)).immediatesValid := by
  simp [Instr.immediatesValid, VecCvtOp.valid, VecCvtOp.toShared,
    Silmaril.Wasm.VecConvertOp.valid]

/-! ## The same defect, scalar `CVTOP`

`Instr_ok/cvtop-convert` (`6-typing:285`) is unconditional and `cvtop`
(`1-syntax:305`) is a flat operator set, not indexed by the type pair the way
`unop_(numtype)` is, so a literal reading types a `CVTOP` whose operator does not
match its types — for instance `CVTOP I64 I32 WRAP`, i.e. a hypothetical
`i64.wrap_i32` — for which `$cvtop__` (`3-numerics:310-318`) has no equation and
no `Step_pure/cvtop-*` rule applies. Wasm 3.0 repaired this by indexing the
syntax, `cvtop__(numtype_1, numtype_2)`
(`wasm-3.0/1.3-syntax.instructions.spectec:55-68`).

This is **decided deviation 16**: `Instr.immediatesValid` and
`Instr_ok/cvtop-convert` both carry the definedness premise
`(op.toShared target source).isSome`. The three results below are the evidence —
the instruction is genuinely stuck, and both of our side conditions reject it, so
`Config.progress` below is true. -/

/-- The witness instruction is rejected by the syntactic side condition. -/
example : ¬ (Instr.cvtOp (.int .i64) (.int .i32) .wrap).immediatesValid := by
  simp [Instr.immediatesValid, CvtOp.toShared]

/-- And by `Instr_ok`: no derivation of any instruction type exists for it. -/
theorem cvtop_badOp_not_ok {C : Context} {it : InstrType} :
    ¬ InstrOk C (.cvtOp (.int .i64) (.int .i32) .wrap) it := by
  intro h
  exact absurd (InstrOk.immediatesValid h) (by simp [Instr.immediatesValid, CvtOp.toShared])

/-- **No `Step_pure` rule applies to the scalar witness.** `CVTOP I64 I32 WRAP`
applied to an `I32` matches no left-hand side of `Step_pure`: `CvtOp.toShared`
has no equation for the combination, so `Step_pure/cvtop-val` and `/cvtop-trap`
(`8-reduction:201,205`) both have empty premises, for every
`Numerics.Profile`. -/
theorem cvtop_badOp_noPureStep {P : Profile} (x : BitVec 32) :
    ¬ ∃ as, PureStep P [(Val.num ⟨.int .i32, x⟩).toAdmin,
      .plain (.cvtOp (.int .i64) (.int .i32) .wrap)] as := by
  rintro ⟨as, h⟩
  generalize hL : [(Val.num ⟨NumType.int .i32, x⟩).toAdmin,
    Admin.plain (.cvtOp (.int .i64) (.int .i32) .wrap)] = L at h
  cases h with
  | cvtOp hr =>
    simp only [Val.toAdmin, List.cons.injEq, Admin.plain.injEq, Instr.cvtOp.injEq,
      and_true] at hL
    obtain ⟨-, rfl, rfl, rfl⟩ := hL
    exact hr
  | cvtOpTrap hr =>
    simp only [Val.toAdmin, List.cons.injEq, Admin.plain.injEq, Instr.cvtOp.injEq,
      and_true] at hL
    obtain ⟨-, rfl, rfl, rfl⟩ := hL
    exact hr
  | trapVals hne =>
    have hmem : Admin.trap ∈ [(Val.num ⟨NumType.int .i32, x⟩).toAdmin,
        Admin.plain (.cvtOp (.int .i64) (.int .i32) .wrap)] := by rw [hL]; simp
    simp [Val.toAdmin] at hmem
  | _ => exact absurd hL (by simp [Val.toAdmin, vconst, vals])

/-- The conversion alone, with no operand, is no `Step_pure` redex. -/
theorem cvtop_badOp_noPureStep1 {P : Profile} (is' : List Admin) :
    ¬ PureStep P [Admin.plain (.cvtOp (.int .i64) (.int .i32) .wrap)] is' := by
  intro h
  generalize hL : [Admin.plain (Instr.cvtOp (.int .i64) (.int .i32) .wrap)] = L at h
  cases h <;> simp_all [vconst, vals, List.cons_eq_append_iff]

/-- The conversion alone is no `Step_read` redex either: no `Step_read` rule
(`8-reduction:7`) mentions `CVTOP`. -/
theorem cvtop_badOp_noReadStep1 {s : Store H} {f : Frame} (is' : List Admin) :
    ¬ ReadStep s f [Admin.plain (.cvtOp (.int .i64) (.int .i32) .wrap)] is' := by
  intro h
  generalize hL : [Admin.plain (Instr.cvtOp (.int .i64) (.int .i32) .wrap)] = L at h
  cases h <;> simp_all [vconst, vals, constI32, List.cons_eq_append_iff]

/-- No `Step_read` rule applies to the scalar witness either. -/
theorem cvtop_badOp_noReadStep {s : Store H} {f : Frame} {x : BitVec 32}
    (is' : List Admin) :
    ¬ ReadStep s f [(Val.num ⟨.int .i32, x⟩).toAdmin,
      .plain (.cvtOp (.int .i64) (.int .i32) .wrap)] is' := by
  intro h
  generalize hL : [(Val.num ⟨NumType.int .i32, x⟩).toAdmin,
    Admin.plain (.cvtOp (.int .i64) (.int .i32) .wrap)] = L at h
  cases h <;> simp_all [vconst, vals, constI32, Val.toAdmin, List.cons_eq_append_iff]

/-- **The witness for the scalar-`CVTOP` defect.** `CVTOP I64 I32 WRAP` applied
to an `I32` is genuinely stuck: **no `Step` rule at all** applies, in any store,
under any frame, for any `Numerics.Profile` and any host semantics. With the
premise removed from `Instr_ok/cvtop-convert` — that is, with SpecTec 2.0 read
literally — this configuration would be well typed, closed, non-terminal and
irreducible, so **progress would be false**. -/
theorem cvtop_badOp_stuck {P : Profile} {host : HostSemantics H} (x : BitVec 32)
    (s : Store H) (f : Frame) :
    ¬ ∃ c', Step P host ⟨s, f, [(Val.num ⟨.int .i32, x⟩).toAdmin,
      .plain (.cvtOp (.int .i64) (.int .i32) .wrap)]⟩ c' :=
  noStep_two cvtop_badOp_noPureStep1 (fun _ h => cvtop_badOp_noPureStep x ⟨_, h⟩)
    (fun _ _ => cvtop_badOp_noReadStep1) (fun _ _ => cvtop_badOp_noReadStep)
    (by simp) (by simp) (by simp) (by simp) (by simp)

/-! ## The instruction families

The partition of `instr` (`1-syntax:406-522`) used to shard the per-instruction
half of progress, mirroring the preservation shards of
`Soundness/Preservation.lean`. `data` is the segment-dropping family
(`ELEM.DROP`, `DATA.DROP`), which `Preservation.lean` also handles as one
shard. -/

/-- The instruction families of `1-syntax:406-522`. -/
inductive InstrFamily where
  /-- `NOP`, `UNREACHABLE`, `DROP`, `SELECT` (`1-syntax:406-410`). -/
  | parametric
  /-- `BLOCK`, `LOOP`, `IF`, `BR`, `BR_IF`, `BR_TABLE`, `RETURN`
  (`1-syntax:413-422`, `:428`). -/
  | control
  /-- `CALL`, `CALL_INDIRECT` (`1-syntax:425-427`). -/
  | call
  /-- `CONST`, `UNOP`, `BINOP`, `TESTOP`, `RELOP`, `CVTOP` (`1-syntax:431-439`). -/
  | numeric
  /-- `VCONST` and the vector operators (`1-syntax:442-473`). -/
  | vector
  /-- `REF.NULL`, `REF.FUNC`, `REF.IS_NULL` (`1-syntax:475-479`). -/
  | reference
  /-- `LOCAL.GET`, `LOCAL.SET`, `LOCAL.TEE` (`1-syntax:481-485`). -/
  | locals
  /-- `GLOBAL.GET`, `GLOBAL.SET` (`1-syntax:487-490`). -/
  | global
  /-- The `TABLE.*` instructions (`1-syntax:492-500`). -/
  | table
  /-- The `MEMORY.*` instructions, the loads and the stores (`1-syntax:506-519`). -/
  | memory
  /-- `ELEM.DROP` and `DATA.DROP` (`1-syntax:503`, `:522`). -/
  | data
  deriving DecidableEq, Repr

/-- The family of an instruction. -/
def _root_.Silmaril.Wasm.V2.Instr.family : Instr → InstrFamily
  | .nop | .unreachable | .drop | .select _ => .parametric
  | .block .. | .loop .. | .if_ .. | .br _ | .brIf _ | .brTable .. | .return_ => .control
  | .call _ | .callIndirect .. => .call
  | .intConst .. | .floatConst .. | .intUnOp .. | .floatUnOp .. | .intBinOp ..
  | .floatBinOp .. | .intTestOp .. | .intRelOp .. | .floatRelOp .. | .cvtOp .. => .numeric
  | .vecConst _ | .vvUnOp _ | .vvBinOp _ | .vvTernOp _ | .vvTestOp _ | .vecIntUnOp ..
  | .vecFloatUnOp .. | .vecIntBinOp .. | .vecFloatBinOp .. | .vecAllTrue _
  | .vecIntRelOp .. | .vecFloatRelOp .. | .vecShiftOp .. | .vecBitmask _ | .vecSwizzle
  | .vecShuffle _ | .vecSplat _ | .vecExtractLane .. | .vecReplaceLane ..
  | .vecExtUnOp .. | .vecExtBinOp .. | .vecNarrow .. | .vecCvtOp .. => .vector
  | .refNull _ | .refFunc _ | .refIsNull => .reference
  | .localGet _ | .localSet _ | .localTee _ => .locals
  | .globalGet _ | .globalSet _ => .global
  | .tableGet _ | .tableSet _ | .tableSize _ | .tableGrow _ | .tableFill _
  | .tableCopy .. | .tableInit .. => .table
  | .intLoad .. | .floatLoad .. | .intStore .. | .floatStore .. | .vecLoad ..
  | .vecLoadLane .. | .vecStore _ | .vecStoreLane .. | .memorySize | .memoryGrow
  | .memoryFill | .memoryCopy | .memoryInit _ => .memory
  | .elemDrop _ | .dataDrop _ => .data

/-! ## The context invariant

The typing context of running code differs from the frame's context only in
`LABELS` and `RETURN` — that is `CtxUnder` of `Soundness/Preservation.lean`.
2.0 has no local-initialisation tracking, so unlike Core 3.0's `CtxOk` there is
nothing else to carry. -/

/-- The invariant relating the context `C` of running code to the frame `f`. -/
structure CtxOk (s : Store H) (f : Frame) (C : Context) : Prop where
  /-- The frame realizes a context that `C` sits under. -/
  frame : ∃ Cf, FrameOk s f Cf ∧ CtxUnder C Cf

/-- The context a frame realizes satisfies the invariant. -/
theorem CtxOk.ofFrame {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    CtxOk s f C := ⟨C, h, CtxUnder.refl C⟩

/-- Entering a `LABEL_` keeps the invariant (`Instr_ok2/label`). -/
theorem CtxOk.withLabel {s : Store H} {f : Frame} {C : Context} (h : CtxOk s f C)
    (ts : CResultType) : CtxOk s f (C.withLabel ts) := by
  obtain ⟨Cf, hf, hu⟩ := h.frame
  exact ⟨Cf, hf, hu.withLabel ts⟩

/-- Entering a `FRAME_` keeps the invariant (`Instr_ok2/frame`). -/
theorem CtxOk.setReturn {s : Store H} {f : Frame} {C : Context} (h : CtxOk s f C)
    (r : Option CResultType) : CtxOk s f { C with return_ := r } := by
  obtain ⟨Cf, hf, hu⟩ := h.frame
  exact ⟨Cf, hf, hu.setReturn r⟩

/-- The frame's locals are typed by the context's locals. -/
theorem CtxOk.locals_forall₂ {s : Store H} {f : Frame} {C : Context} (h : CtxOk s f C) :
    List.Forall₂ (ValOk s) f.locals C.locals := by
  obtain ⟨Cf, hf, hu⟩ := h.frame
  rw [hu.locals_eq]
  exact hf.locals_forall₂

/-- The frame's module instance realizes the non-`LABELS`/`RETURN` part of `C`. -/
theorem CtxOk.frameOk {s : Store H} {f : Frame} {C : Context} (h : CtxOk s f C) :
    ∃ Cf, FrameOk s f Cf ∧ CtxUnder C Cf := h.frame

/-! ## Outcomes of typed code -/

/-- Non-value outcomes: a step, or one of the three exit forms the enclosing
administrative instruction consumes. Core 3.0 has two more (a thrown exception
and a pending `return_call_ref`); 2.0 has neither. -/
def OutN (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (L : List CResultType) (R : Option CResultType) (code : List Admin) : Prop :=
  (∃ c', Step P host ⟨s, f, code⟩ c') ∨
  (∃ vs rest, code = vals vs ++ [.trap] ++ rest) ∨
  (∃ vs l rest tl, code = vals vs ++ [.plain (.br l)] ++ rest ∧ L[l.toNat]? = some tl ∧
    tl.length ≤ vs.length) ∨
  (∃ vs rest rt, code = vals vs ++ [.plain .return_] ++ rest ∧ R = some rt ∧
    rt.length ≤ vs.length)

/-- Outcomes of typed code: a value stack of the result types, or a non-value
outcome. -/
def Out (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (L : List CResultType) (R : Option CResultType) (code : List Admin)
    (ts : CResultType) : Prop :=
  (∃ vs, code = vals vs ∧ ValsOk s vs ts) ∨ OutN P host s f L R code

section Outcomes

variable {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
  {L : List CResultType} {R : Option CResultType}

/-- A step still applies inside an evaluation context (`Step/ctxt-instrs`). -/
theorem Step.inCtx {code : List Admin} {c' : Config H} (h : Step P host ⟨s, f, code⟩ c')
    (vs : List Val) (rest : List Admin) :
    ∃ c'', Step P host ⟨s, f, vals vs ++ code ++ rest⟩ c'' := by
  obtain ⟨s', f', code'⟩ := c'
  by_cases hne : vs = [] ∧ rest = []
  · obtain ⟨rfl, rfl⟩ := hne
    exact ⟨_, by simpa using h⟩
  · exact ⟨_, Step.ctxtInstrs h (not_and_or.mp hne)⟩

/-- A step is an outcome. -/
theorem OutN.step {code : List Admin} (h : ∃ c', Step P host ⟨s, f, code⟩ c') :
    OutN P host s f L R code := Or.inl h

theorem OutN.append {code : List Admin} (h : OutN P host s f L R code) (rest : List Admin) :
    OutN P host s f L R (code ++ rest) := by
  rcases h with ⟨c', hc⟩ | ⟨vs, r, rfl⟩ | ⟨vs, l, r, tl, rfl, h1, h2⟩ | ⟨vs, r, rt, rfl, h1, h2⟩
  · obtain ⟨c'', h⟩ := Step.inCtx (vs := []) (rest := rest) hc
    exact .inl ⟨c'', by simpa using h⟩
  · exact .inr (.inl ⟨vs, r ++ rest, by simp⟩)
  · exact .inr (.inr (.inl ⟨vs, l, r ++ rest, tl, by simp, h1, h2⟩))
  · exact .inr (.inr (.inr ⟨vs, r ++ rest, rt, by simp, h1, h2⟩))

theorem OutN.prepend {code : List Admin} (h : OutN P host s f L R code) (vs₀ : List Val) :
    OutN P host s f L R (vals vs₀ ++ code) := by
  rcases h with ⟨c', hc⟩ | ⟨vs, r, rfl⟩ | ⟨vs, l, r, tl, rfl, h1, h2⟩ | ⟨vs, r, rt, rfl, h1, h2⟩
  · obtain ⟨c'', h⟩ := Step.inCtx (vs := vs₀) (rest := []) hc
    exact .inl ⟨c'', by simpa using h⟩
  · exact .inr (.inl ⟨vs₀ ++ vs, r, by simp⟩)
  · exact .inr (.inr (.inl ⟨vs₀ ++ vs, l, r, tl, by simp, h1, by simp; omega⟩))
  · exact .inr (.inr (.inr ⟨vs₀ ++ vs, r, rt, by simp, h1, by simp; omega⟩))

theorem Out.prepend {code : List Admin} {ts ts₀ : CResultType} {vs₀ : List Val}
    (h : Out P host s f L R code ts) (hv : ValsOk s vs₀ ts₀) :
    Out P host s f L R (vals vs₀ ++ code) (ts₀ ++ ts) := by
  rcases h with ⟨vs, rfl, hv'⟩ | h
  · exact .inl ⟨vs₀ ++ vs, by simp, List.rel_append hv hv'⟩
  · exact .inr (h.prepend vs₀)

theorem Out.sub {code : List Admin} {ts ts' : CResultType}
    (h : Out P host s f L R code ts) (hs : CResultType.Sub ts ts') :
    Out P host s f L R code ts' := by
  rcases h with ⟨vs, e, hv⟩ | h
  · exact .inl ⟨vs, e, hv.sub hs⟩
  · exact .inr h

/-- `TRAP` under a value prefix is terminal only when it is alone
(`Step_pure/trap-vals`, `8-reduction:150`). -/
theorem trap_or_step (vs : List Val) (rest : List Admin) :
    (vs = [] ∧ rest = []) ∨ ∃ c', Step P host ⟨s, f, vals vs ++ [.trap] ++ rest⟩ c' := by
  by_cases h : vs = [] ∧ rest = []
  · exact .inl h
  · exact .inr ⟨_, .pure (.trapVals (not_and_or.mp h))⟩

/-- A value instruction is its own outcome. -/
theorem value_out {C : Context} {a : Admin} {it : InstrType} {v : Val} {vs₀ : List Val}
    (ha : AdminOk s C a it) (hva : a.val? = some v) (hv : ValsOk s vs₀ it.params) :
    Out P host s f L R (vals vs₀ ++ [a]) it.results := by
  obtain rfl := Admin.toAdmin_of_val? hva
  obtain ⟨hp, t, hvt, hr⟩ := AdminOk.toAdmin_inv ha
  rw [hp] at hv
  cases hv
  rw [hr]
  exact .inl ⟨[v], by simp [vals], .cons ⟨t, rfl, hvt⟩ .nil⟩

end Outcomes

/-! ## The two administrative control forms over a stuck body -/

section Admin

variable {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
  {L : List CResultType} {R : Option CResultType}

/-- `LABEL_ n {instr*} admininstr*` steps whenever its body has an outcome
(`Step_pure/label-vals`, `/br-zero`, `/br-succ`, `/return-label`, `/trap-label`,
`Step/ctxt-label`). -/
theorem label_step {n : Nat} {cont : List Instr} {body : List Admin} {t' ts : CResultType}
    (hn : t'.length = n) (h : Out P host s f (t' :: L) R body ts) :
    ∃ c', Step P host ⟨s, f, [.label n cont body]⟩ c' := by
  rcases h with ⟨vs, rfl, -⟩ | ⟨⟨s', f', is'⟩, hc⟩ | ⟨vs, rest, rfl⟩ |
    ⟨vs, l, rest, tl, rfl, h1, h2⟩ | ⟨vs, rest, rt, rfl, h1, h2⟩
  · exact ⟨_, .pure .labelVals⟩
  · exact ⟨_, .ctxtLabel hc⟩
  · rcases trap_or_step (P := P) (host := host) (s := s) (f := f) vs rest with
      ⟨rfl, rfl⟩ | ⟨⟨s', f', is'⟩, hc⟩
    · exact ⟨_, .pure .trapLabel⟩
    · exact ⟨_, .ctxtLabel hc⟩
  · by_cases hl : l.toNat = 0
    · rw [hl] at h1
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
      subst h1
      obtain ⟨vs₁, vs₂, rfl, hlen⟩ := exists_split_right vs n (by omega)
      rw [vals_append]
      exact ⟨_, .pure (.brZero hl hlen)⟩
    · exact ⟨_, .pure (.brSucc (by omega))⟩
  · exact ⟨_, .pure .returnLabel⟩

/-- `FRAME_ n {frame} admininstr*` steps whenever its body has an outcome
(`Step_pure/frame-vals`, `/return-frame`, `/trap-frame`, `Step/ctxt-frame`). -/
theorem frame_step {fr : Frame} {n : Nat} {body : List Admin} {ts : CResultType}
    (hL : L = []) (hn : ts.length = n) (h : Out P host s fr L (some ts) body ts) :
    ∃ c', Step P host ⟨s, f, [.frame n fr body]⟩ c' := by
  subst hL
  rcases h with ⟨vs, rfl, hv⟩ | ⟨⟨s', f', is'⟩, hc⟩ | ⟨vs, rest, rfl⟩ |
    ⟨vs, l, rest, tl, rfl, h1, h2⟩ | ⟨vs, rest, rt, rfl, h1, h2⟩
  · exact ⟨_, .pure (.frameVals (hv.length_eq.trans hn))⟩
  · exact ⟨_, .ctxtFrame hc⟩
  · rcases trap_or_step (P := P) (host := host) (s := s) (f := fr) vs rest with
      ⟨rfl, rfl⟩ | ⟨⟨s', f', is'⟩, hc⟩
    · exact ⟨_, .pure .trapFrame⟩
    · exact ⟨_, .ctxtFrame hc⟩
  · simp at h1
  · obtain rfl := Option.some.inj h1
    obtain ⟨vs₁, vs₂, rfl, hlen⟩ := exists_split_right vs n (by omega)
    rw [vals_append]
    exact ⟨_, .pure (.returnFrame hlen)⟩

end Admin


/-! ## Helpers for the per-family shards

The glue every shard needs: lifting a redex step into an outcome, the
context-to-store bridges that `Soundness/Preservation.lean` does not already
provide (memories and data segments), the grow dichotomy of
`Numerics.Profile`, and the two facts that make a load and a store *inside the
bounds* always applicable. -/

section Helpers

variable {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
  {L : List CResultType} {R : Option CResultType}

/-- A step of the redex `val* admininstr` sitting on top of the stack is an
outcome of the whole code (`Step/ctxt-instrs`). -/
theorem outN_redex {vs₀ vsR vt : List Val} {a : Admin} {rest : List Admin}
    (hsplit : vs₀ = vsR ++ vt)
    (h : ∃ c', Step P host ⟨s, f, vals vt ++ [a]⟩ c') :
    OutN P host s f L R (vals vs₀ ++ a :: rest) := by
  subst hsplit
  have h2 := ((OutN.step (L := L) (R := R) h).prepend vsR).append rest
  simpa using h2

/-- The common case of `outN_redex`: the redex consumes the whole value prefix. -/
theorem outN_redex' {vs₀ : List Val} {a : Admin} {rest : List Admin}
    (h : ∃ c', Step P host ⟨s, f, vals vs₀ ++ [a]⟩ c') :
    OutN P host s f L R (vals vs₀ ++ a :: rest) :=
  outN_redex (vsR := []) (List.nil_append _).symm h

/-! ### Destructuring a typed value stack -/

theorem ValsOk.one_inv {vs : List Val} {t₁ : CValType} (h : ValsOk s vs [t₁]) :
    ∃ v₁, vs = [v₁] ∧ CValOk s v₁ t₁ := by
  cases h with
  | cons h₁ h =>
    cases h
    exact ⟨_, rfl, h₁⟩

theorem ValsOk.two_inv {vs : List Val} {t₁ t₂ : CValType} (h : ValsOk s vs [t₁, t₂]) :
    ∃ v₁ v₂, vs = [v₁, v₂] ∧ CValOk s v₁ t₁ ∧ CValOk s v₂ t₂ := by
  cases h with
  | cons h₁ h =>
    obtain ⟨v₂, rfl, h₂⟩ := ValsOk.one_inv h
    exact ⟨_, _, rfl, h₁, h₂⟩

theorem ValsOk.three_inv {vs : List Val} {t₁ t₂ t₃ : CValType}
    (h : ValsOk s vs [t₁, t₂, t₃]) :
    ∃ v₁ v₂ v₃, vs = [v₁, v₂, v₃] ∧ CValOk s v₁ t₁ ∧ CValOk s v₂ t₂ ∧ CValOk s v₃ t₃ := by
  cases h with
  | cons h₁ h =>
    obtain ⟨v₂, v₃, rfl, h₂, h₃⟩ := ValsOk.two_inv h
    exact ⟨_, _, _, rfl, h₁, h₂, h₃⟩

theorem cvalOk_i32_inv {v : Val} (h : CValOk s v (.val .i32)) :
    ∃ c : BitVec 32, v = .num ⟨.int .i32, c⟩ ∧ v.toAdmin = constI32 c :=
  ValOk.i32_inv (cValOk_val.mp h)

theorem cvalOk_int_inv {v : Val} {t : IntType} (h : CValOk s v (.val (.num (.int t)))) :
    ∃ c : BitVec t.width, v = .num ⟨.int t, c⟩ ∧ v.toAdmin = .plain (.intConst t c) :=
  ValOk.int_inv (cValOk_val.mp h)

theorem cvalOk_float_inv {v : Val} {t : FloatType} (h : CValOk s v (.val (.num (.float t)))) :
    ∃ c : BitVec t.width, v = .num ⟨.float t, c⟩ ∧ v.toAdmin = .plain (.floatConst t c) :=
  ValOk.float_inv (cValOk_val.mp h)

theorem cvalOk_num_inv {v : Val} {t : NumType} (h : CValOk s v (.val (.num t))) :
    ∃ c : BitVec t.width, v = .num ⟨t, c⟩ :=
  ValOk.num_inv (cValOk_val.mp h)

theorem cvalOk_v128_inv {v : Val} (h : CValOk s v (.val .v128)) :
    ∃ c : BitVec 128, v = .vec c ∧ v.toAdmin = vconst c :=
  ValOk.vec_inv (cValOk_val.mp h)

theorem cvalOk_ref_inv {v : Val} {rt : RefType} (h : CValOk s v (.val (.ref rt))) :
    ∃ r : Ref, v = .ref r ∧ RefOk s r rt :=
  ValOk.ref_inv (cValOk_val.mp h)

/-- The topmost operand of every instruction whose last parameter is `I32`. -/
theorem ValsOk.snoc_i32 {vs : List Val} {ts : CResultType}
    (h : ValsOk s vs (ts ++ [.val .i32])) :
    ∃ (ws : List Val) (c : BitVec 32), vs = ws ++ [Val.num ⟨.int .i32, c⟩] ∧ ValsOk s ws ts := by
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := forall₂_split h
  obtain ⟨v, rfl, hv⟩ := ValsOk.one_inv h₂
  obtain ⟨c, rfl, -⟩ := cvalOk_i32_inv hv
  exact ⟨l₁, c, rfl, h₁⟩

/-- The redex form of `outN_redex` for an instruction whose only operand is the
topmost `I32`. -/
theorem outN_redex_i32 {ws : List Val} {c : BitVec 32} {a : Admin} {rest : List Admin}
    (h : ∃ c', Step P host ⟨s, f, [constI32 c, a]⟩ c') :
    OutN P host s f L R (vals (ws ++ [Val.num ⟨.int .i32, c⟩]) ++ a :: rest) :=
  outN_redex (vsR := ws) (vt := [Val.num ⟨.int .i32, c⟩]) rfl h

/-! ### Two more context-to-store bridges -/

/-- `C.MEMS[x]` resolves to a memory instance of the store. -/
theorem ModuleInstOk.mem_bridge {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) {x : MemIdx} {mt : MemoryType}
    (hx : C.mems[x.toNat]? = some mt) :
    ∃ a m, mi.memAddr? x = some a ∧ s.memInst? a = some m ∧ MemoryType.Sub m.type mt := by
  cases h with
  | mk _ _ _ _ hmems =>
    obtain ⟨a, ha, hok⟩ := forall₂_getElem? hmems _ _ hx
    obtain ⟨m, hm, hsub⟩ := hok.mem_inv
    exact ⟨a, m, ha, hm, hsub⟩

theorem FrameOk.mem_bridge {C : Context} (h : FrameOk s f C) {x : MemIdx} {mt : MemoryType}
    (hx : C.mems[x.toNat]? = some mt) :
    ∃ a m, f.module.memAddr? x = some a ∧ s.memInst? a = some m ∧
      (⟨s, f⟩ : State H).mem? x = some m ∧ MemoryType.Sub m.type mt := by
  obtain ⟨C₀, hm, -, -, -, -, he, -⟩ := h.module_ok
  obtain ⟨a, m, ha, hmi, hsub⟩ := hm.mem_bridge (by rw [← he]; exact hx)
  exact ⟨a, m, ha, hmi, by simp [State.mem?, ha, hmi], hsub⟩

/-- `C.DATAS[x]` resolves to a data instance of the store. -/
theorem ModuleInstOk.data_bridge {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) {x : DataIdx} (hx : C.datas[x.toNat]? = some ()) :
    ∃ a di, mi.dataAddr? x = some a ∧ s.dataInst? a = some di := by
  cases h with
  | mk _ _ _ _ _ _ hdatas =>
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hx
    simp only [List.length_map] at hlt
    obtain ⟨di, hdi⟩ := hdatas mi.datas[x.toNat] (List.getElem_mem hlt)
    exact ⟨_, di, List.getElem?_eq_getElem hlt, hdi⟩

theorem FrameOk.data_bridge {C : Context} (h : FrameOk s f C) {x : DataIdx}
    (hx : C.datas[x.toNat]? = some ()) :
    ∃ a di, f.module.dataAddr? x = some a ∧ s.dataInst? a = some di ∧
      (⟨s, f⟩ : State H).data? x = some di := by
  obtain ⟨C₀, hm, -, -, -, -, -, -, he, -⟩ := h.module_ok
  obtain ⟨a, di, ha, hdi⟩ := hm.data_bridge (by rw [← he]; exact hx)
  exact ⟨a, di, ha, hdi, by simp [State.data?, ha, hdi]⟩

/-! ### Context-to-store bridges through `CtxOk` -/

theorem CtxOk.func_bridge {C : Context} (h : CtxOk s f C) {x : FuncIdx} {ft : FuncType}
    (hx : C.funcs[x.toNat]? = some ft) :
    ∃ a fi, f.module.funcAddr? x = some a ∧ s.funcInst? a = some fi ∧ fi.type = ft := by
  obtain ⟨Cf, hf, hu⟩ := h.frame
  exact hf.func_bridge (by rw [← hu.funcs_eq]; exact hx)

theorem CtxOk.global_bridge {C : Context} (h : CtxOk s f C) {x : GlobalIdx} {gt : GlobalType}
    (hx : C.globals[x.toNat]? = some gt) :
    ∃ a gi, f.module.globalAddr? x = some a ∧ s.globalInst? a = some gi ∧
      (⟨s, f⟩ : State H).global? x = some gi ∧ gi.type = gt := by
  obtain ⟨Cf, hf, hu⟩ := h.frame
  exact hf.global_bridge (by rw [← hu.globals_eq]; exact hx)

theorem CtxOk.table_bridge {C : Context} (h : CtxOk s f C) (hs : StoreOk s) {x : TableIdx}
    {tt : TableType} (hx : C.tables[x.toNat]? = some tt) :
    ∃ a ti, f.module.tableAddr? x = some a ∧ s.tableInst? a = some ti ∧
      (⟨s, f⟩ : State H).table? x = some ti ∧ TableInstOk s ti := by
  obtain ⟨Cf, hf, hu⟩ := h.frame
  obtain ⟨a, ti, ha, hti, hst, -⟩ := hf.table_bridge (by rw [← hu.tables_eq]; exact hx)
  exact ⟨a, ti, ha, hti, hst, hs.tables ti (List.mem_of_getElem? hti)⟩

theorem CtxOk.mem0_bridge {C : Context} (h : CtxOk s f C) (hs : StoreOk s) {mt : MemoryType}
    (hm : C.mems[0]? = some mt) :
    ∃ a mi, f.module.memAddr? memIdx0 = some a ∧ s.memInst? a = some mi ∧
      (⟨s, f⟩ : State H).mem? memIdx0 = some mi ∧ MemInstOk mi := by
  obtain ⟨Cf, hf, hu⟩ := h.frame
  obtain ⟨a, mi, ha, hmi, hst, -⟩ :=
    hf.mem_bridge (x := memIdx0) (by rw [← hu.mems_eq]; exact hm)
  exact ⟨a, mi, ha, hmi, hst, hs.mems mi (List.mem_of_getElem? hmi)⟩

theorem CtxOk.elem_bridge {C : Context} (h : CtxOk s f C) {x : ElemIdx} {rt : ElemType}
    (hx : C.elems[x.toNat]? = some rt) :
    ∃ a ei, f.module.elemAddr? x = some a ∧ s.elemInst? a = some ei ∧
      (⟨s, f⟩ : State H).elem? x = some ei ∧ ei.type = rt := by
  obtain ⟨Cf, hf, hu⟩ := h.frame
  obtain ⟨C₀, hm, -, -, -, -, -, he, -⟩ := hf.module_ok
  obtain ⟨a, ei, ha, hei, -, hty⟩ :=
    hm.elem_bridge (by rw [← he, ← hu.elems_eq]; exact hx)
  exact ⟨a, ei, ha, hei, by simp [State.elem?, ha, hei], hty⟩

theorem CtxOk.data_bridge {C : Context} (h : CtxOk s f C) {x : DataIdx}
    (hx : C.datas[x.toNat]? = some ()) :
    ∃ a di, f.module.dataAddr? x = some a ∧ s.dataInst? a = some di ∧
      (⟨s, f⟩ : State H).data? x = some di := by
  obtain ⟨Cf, hf, hu⟩ := h.frame
  exact hf.data_bridge (by rw [← hu.datas_eq]; exact hx)

/-! ### Scalar conversion -/

/-- A `CVTOP` whose `$cvtop__` equation exists either converts or traps
(`Step_pure/cvtop-val`, `/cvtop-trap`). -/
theorem cvtop_step {target source : NumType} {op : CvtOp}
    (hdef : (op.toShared target source).isSome) (x : BitVec source.width) :
    ∃ c', Step P host
      ⟨s, f, [(Val.num ⟨source, x⟩).toAdmin, .plain (.cvtOp target source op)]⟩ c' := by
  obtain ⟨co, hco⟩ := Option.isSome_iff_exists.mp hdef
  have hsrc := cvtOp_toShared_source hco
  have htgt := cvtOp_toShared_target hco
  subst hsrc
  subst htgt
  rcases cvtOpResult_or_traps P op co hco x with ⟨z, hz⟩ | ht
  · exact ⟨_, .pure (.cvtOp hz)⟩
  · exact ⟨_, .pure (.cvtOpTrap ht)⟩

/-! ### `$blocktype` is defined on every valid block type -/

/-- A `Blocktype_ok` derivation in a context the frame realizes means
`$blocktype(z, bt)` (`8-reduction:63`) is defined. -/
theorem blockType_exists {Cf Ct : Context} {bt : BlockType} {it : InstrType}
    (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf) (hok : BlockTypeOk Ct bt it) :
    ∃ ft, f.module.blockType? bt = some ft := by
  have htypes : Ct.types = f.module.types := by rw [hu.types_eq, hf.types_eq]
  cases hok with
  | result t => cases t <;> exact ⟨_, rfl⟩
  | typeIdx hx =>
    rename_i x ft
    rw [htypes] at hx
    exact ⟨ft, hx⟩

/-! ### The grow dichotomy -/

/-- A grow that the profile does not allow to fail is one it allows to succeed:
`Profile.grow` is either `nondet` (both) or an oracle (exactly one). -/
theorem growMaySucceed_of_not_fail {k : Numerics.GrowKind} {a sz d : Nat}
    (h : ¬ P.growMayFail k a sz d) : P.growMaySucceed k a sz d := by
  unfold Profile.growMayFail at h
  unfold Profile.growMaySucceed
  cases hg : P.grow with
  | nondet => rw [hg] at h; exact absurd trivial h
  | oracle o =>
    rw [hg] at h
    show o k a sz d = false
    cases hb : o k a sz d
    · rfl
    · exact absurd hb h

/-! ### Loads and stores inside the bounds always apply -/

theorem width_dvd_int (t : IntType) : 8 ∣ t.width := by cases t <;> decide
theorem width_dvd_float (t : FloatType) : 8 ∣ t.width := by cases t <;> decide
theorem width_dvd_pack (sz : PackSize) : 8 ∣ sz.width := by cases sz <;> decide

theorem width_dvd_vecLoad (op : Option VecLoadOp) : 8 ∣ VecLoadOp.accessWidth op := by
  rcases op with _ | o
  · decide
  · cases o with
    | shape8x8 _ => show (8 : Nat) ∣ 64; decide
    | shape16x4 _ => show (8 : Nat) ∣ 64; decide
    | shape32x2 _ => show (8 : Nat) ∣ 64; decide
    | splat sz => exact width_dvd_pack sz
    | zero32 => decide
    | zero64 => decide

/-- Every in-bounds read of `N/8` bytes is the `$ibytes_` encoding of some
`N`-bit value, so the `-val` rule of every load applies. -/
theorem exists_ibytes_read {mem : Bytes} {start N : Nat} (hN : 8 ∣ N)
    (hb : start + N / 8 ≤ mem.size) :
    ∃ c : BitVec N, readBytes mem start (N / 8) = some (ibytes N c) := by
  have h : readBytes mem start (N / 8) = some (mem.extract start (start + N / 8)) := by
    simp [readBytes, hb]
  exact ⟨invIbytes N (mem.extract start (start + N / 8)), by
    rw [h, ibytes_invIbytes hN
      (Silmaril.Wasm.Execution.Memory.readBytes_size _ _ _ _ h)]⟩

/-- An in-bounds write of a byte string of the declared length succeeds. -/
theorem exists_writeBytes {mi : MemInst} {start j : Nat} {bs : Bytes}
    (hsize : bs.size = j) (hb : start + j ≤ mi.bytes.size) :
    ∃ mi', mi.writeBytes? start j bs = some mi' := by
  have hw : writeBytes mi.bytes start bs = some (bs.copySlice 0 mi.bytes start bs.size) := by
    simp [writeBytes, hsize, hb]
  refine ⟨{ mi with bytes := bs.copySlice 0 mi.bytes start bs.size }, ?_⟩
  simp [MemInst.writeBytes?, hsize, hw]

/-- A vector load either traps out of bounds or reads its `$vloadop` width
(`Step_read/vload-*`, one constructor for all four shapes). -/
theorem vecLoad_step {op : Option VecLoadOp} {arg : MemArg} {mi : MemInst} {idx : BitVec 32}
    (hmi : (⟨s, f⟩ : State H).mem? memIdx0 = some mi) :
    ∃ c', Step P host ⟨s, f, [constI32 idx, .plain (.vecLoad op arg)]⟩ c' := by
  by_cases hb : mi.bytes.size < effAddr idx.toNat arg + VecLoadOp.accessWidth op / 8
  · exact ⟨_, .read (.vecLoadOob hmi hb)⟩
  · obtain ⟨c, hc⟩ := exists_ibytes_read (mem := mi.bytes)
      (start := effAddr idx.toNat arg) (N := VecLoadOp.accessWidth op)
      (width_dvd_vecLoad op) (by omega)
    exact ⟨_, .read (.vecLoadVal hmi hc)⟩

end Helpers

/-! ## Per-family progress

One lemma per family of `Instr.family`, mirroring the preservation shards of
`Soundness/Preservation.lean`: a well-typed configuration whose code is
`val* (plain i) admininstr*` with `i` in that family either steps or is
terminal — where "terminal" is read through `OutN`, which also covers the two
exit forms `br l` and `return` that an enclosing `LABEL_`/`FRAME_` consumes
(`control_progress` is the only shard that can produce them). The hypothesis
`hnv` excludes the *value* instructions `CONST`, `VCONST` and `REF.NULL`, which
do not step and are handled by `value_out`. -/

section Families

variable {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame} {C : Context}
  {i : Instr} {it : InstrType} {vs₀ : List Val} {rest : List Admin}

/-- Progress for `NOP`, `UNREACHABLE`, `DROP` and `SELECT`
(`Step_pure/nop`, `/unreachable`, `/drop`, `/select-*`, `8-reduction:40-58`). -/
theorem parametric_progress (hs : StoreOk s) (hc : CtxOk s f C)
    (hfam : i.family = .parametric) (hi : InstrOk C i it)
    (hnv : (Admin.plain i).val? = none) (hv : ValsOk s vs₀ it.params) :
    OutN P host s f C.labels C.return_ (vals vs₀ ++ .plain i :: rest) := by
  have _ := hs
  have _ := hc
  cases hi <;> simp only [Instr.family, reduceCtorEq] at hfam
  case nop =>
    cases hv
    exact outN_redex' ⟨_, .pure .nop⟩
  case unreachable =>
    exact outN_redex (vsR := vs₀) (vt := []) (by simp) ⟨_, .pure .unreachable⟩
  case drop =>
    obtain ⟨v, rfl, -⟩ := hv.one_inv
    exact outN_redex' ⟨_, .pure (.drop v)⟩
  case selectExpl =>
    obtain ⟨v₁, v₂, v₃, rfl, -, -, h₃⟩ := hv.three_inv
    obtain ⟨c, rfl, -⟩ := cvalOk_i32_inv h₃
    by_cases hc0 : c = 0
    · subst hc0
      exact outN_redex' ⟨_, .pure (.selectFalse v₁ v₂ _)⟩
    · exact outN_redex' ⟨_, .pure (.selectTrue hc0)⟩
  case selectImpl =>
    obtain ⟨v₁, v₂, v₃, rfl, -, -, h₃⟩ := hv.three_inv
    obtain ⟨c, rfl, -⟩ := cvalOk_i32_inv h₃
    by_cases hc0 : c = 0
    · subst hc0
      exact outN_redex' ⟨_, .pure (.selectFalse v₁ v₂ _)⟩
    · exact outN_redex' ⟨_, .pure (.selectTrue hc0)⟩

/-- Progress for the numeric instructions
(`Step_pure/unop-*`, `/binop-*`, `/testop`, `/relop`, `/cvtop-*`,
`8-reduction:172-207`).

The `cvtop` case is the one that needs the definedness premise
`(CvtOp.toShared target source op).isSome` of `InstrOk.cvtOpConvert` (decided
deviation 16): without it the case is **false**, by `cvtop_badOp_stuck`. The
`reinterpret` case gets the same premise from
`CvtOp.toShared_reinterpret_isSome`, whose hypotheses are exactly the two
premises of `Instr_ok/cvtop-reinterpret`. -/
theorem numeric_progress (hs : StoreOk s) (hc : CtxOk s f C)
    (hfam : i.family = .numeric) (hi : InstrOk C i it)
    (hnv : (Admin.plain i).val? = none) (hv : ValsOk s vs₀ it.params) :
    OutN P host s f C.labels C.return_ (vals vs₀ ++ .plain i :: rest) := by
  have _ := hs
  have _ := hc
  cases hi <;> simp only [Instr.family, reduceCtorEq] at hfam
  case intConst => simp [Admin.val?] at hnv
  case floatConst => simp [Admin.val?] at hnv
  case intUnOp =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨x, rfl, -⟩ := cvalOk_int_inv h₁
    obtain ⟨z, hz⟩ := IntUnOpResult_nonempty _ _ x
    exact outN_redex' ⟨_, .pure (.intUnOp hz)⟩
  case floatUnOp =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨x, rfl, -⟩ := cvalOk_float_inv h₁
    obtain ⟨z, hz⟩ := FloatUnOpResult_nonempty P _ _ x
    exact outN_redex' ⟨_, .pure (.floatUnOp hz)⟩
  case intBinOp =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨x, rfl, -⟩ := cvalOk_int_inv h₁
    obtain ⟨y, rfl, -⟩ := cvalOk_int_inv h₂
    rcases IntBinOpResult_or_traps _ _ x y with ⟨z, hz⟩ | ht
    · exact outN_redex' ⟨_, .pure (.intBinOp hz)⟩
    · exact outN_redex' ⟨_, .pure (.intBinOpTrap ht)⟩
  case floatBinOp =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨x, rfl, -⟩ := cvalOk_float_inv h₁
    obtain ⟨y, rfl, -⟩ := cvalOk_float_inv h₂
    obtain ⟨z, hz⟩ := FloatBinOpResult_nonempty P _ _ x y
    exact outN_redex' ⟨_, .pure (.floatBinOp hz)⟩
  case intTestOp =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨x, rfl, -⟩ := cvalOk_int_inv h₁
    exact outN_redex' ⟨_, .pure .testOp⟩
  case intRelOp =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨x, rfl, -⟩ := cvalOk_int_inv h₁
    obtain ⟨y, rfl, -⟩ := cvalOk_int_inv h₂
    exact outN_redex' ⟨_, .pure .intRelOp⟩
  case floatRelOp =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨x, rfl, -⟩ := cvalOk_float_inv h₁
    obtain ⟨y, rfl, -⟩ := cvalOk_float_inv h₂
    exact outN_redex' ⟨_, .pure .floatRelOp⟩
  case cvtOpReinterpret _ _ hne hsize =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨x, rfl⟩ := cvalOk_num_inv h₁
    exact outN_redex' (cvtop_step (CvtOp.toShared_reinterpret_isSome hne hsize) x)
  case cvtOpConvert _ _ _ _ hdef =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨x, rfl⟩ := cvalOk_num_inv h₁
    exact outN_redex' (cvtop_step hdef x)

/-- Progress for the vector instructions (`Step_pure/vv*`, `/v*`, `8-reduction:227-372`).
This is the shard that needs the `VCVTOP` shape premise of `Instr_ok/vcvtop`;
without it the case `vcvtop` is **false**, by `vcvtop_badShape_stuck`. -/
theorem vector_progress (hs : StoreOk s) (hc : CtxOk s f C)
    (hfam : i.family = .vector) (hi : InstrOk C i it)
    (hnv : (Admin.plain i).val? = none) (hv : ValsOk s vs₀ it.params) :
    OutN P host s f C.labels C.return_ (vals vs₀ ++ .plain i :: rest) := by
  have _ := hs
  have _ := hc
  cases hi <;> simp only [Instr.family, reduceCtorEq] at hfam
  case vecConst => simp [Admin.val?] at hnv
  case vvUnOp =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨c, rfl, -⟩ := cvalOk_v128_inv h₁
    exact outN_redex' ⟨_, .pure (.vvUnOp _ c)⟩
  case vvBinOp =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨c₁, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨c₂, rfl, -⟩ := cvalOk_v128_inv h₂
    exact outN_redex' ⟨_, .pure (.vvBinOp _ c₁ c₂)⟩
  case vvTernOp =>
    obtain ⟨v₁, v₂, v₃, rfl, h₁, h₂, h₃⟩ := hv.three_inv
    obtain ⟨c₁, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨c₂, rfl, -⟩ := cvalOk_v128_inv h₂
    obtain ⟨c₃, rfl, -⟩ := cvalOk_v128_inv h₃
    exact outN_redex' ⟨_, .pure (.vvTernOp _ c₁ c₂ c₃)⟩
  case vvTestOp =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨c, rfl, -⟩ := cvalOk_v128_inv h₁
    exact outN_redex' ⟨_, .pure (.vvTestOp _ c)⟩
  case vecIntUnOp sh op _ =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨c, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨r, hr⟩ := VecIntUnOpResult_nonempty sh op c
    exact outN_redex' ⟨_, .pure (.vecIntUnOp hr)⟩
  case vecFloatUnOp sh op =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨c, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨r, hr⟩ := VecFloatUnOpResult_nonempty P sh op c
    exact outN_redex' ⟨_, .pure (.vecFloatUnOp hr)⟩
  case vecIntBinOp sh op _ =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨c₁, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨c₂, rfl, -⟩ := cvalOk_v128_inv h₂
    obtain ⟨r, hr⟩ := VecIntBinOpResult_nonempty P sh op c₁ c₂
    exact outN_redex' ⟨_, .pure (.vecIntBinOp hr)⟩
  case vecFloatBinOp sh op =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨c₁, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨c₂, rfl, -⟩ := cvalOk_v128_inv h₂
    obtain ⟨r, hr⟩ := VecFloatBinOpResult_nonempty P sh op c₁ c₂
    exact outN_redex' ⟨_, .pure (.vecFloatBinOp hr)⟩
  case vecAllTrue sh =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨c, rfl, -⟩ := cvalOk_v128_inv h₁
    by_cases hall : ∃ l ∈ sh.lanesOf c, l = 0
    · exact outN_redex' ⟨_, .pure (.vecAllTrueFalse hall)⟩
    · exact outN_redex' ⟨_, .pure (.vecAllTrueTrue (fun l hl hz => hall ⟨l, hl, hz⟩))⟩
  case vecIntRelOp =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨c₁, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨c₂, rfl, -⟩ := cvalOk_v128_inv h₂
    exact outN_redex' ⟨_, .pure .vecIntRelOp⟩
  case vecFloatRelOp =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨c₁, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨c₂, rfl, -⟩ := cvalOk_v128_inv h₂
    exact outN_redex' ⟨_, .pure .vecFloatRelOp⟩
  case vecShiftOp =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨c, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨n, rfl, -⟩ := cvalOk_i32_inv h₂
    exact outN_redex' ⟨_, .pure .vecShiftOp⟩
  case vecBitmask =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨c, rfl, -⟩ := cvalOk_v128_inv h₁
    exact outN_redex' ⟨_, .pure .vecBitmask⟩
  case vecSwizzle =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨c₁, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨c₂, rfl, -⟩ := cvalOk_v128_inv h₂
    exact outN_redex' ⟨_, .pure .vecSwizzle⟩
  case vecShuffle _ _ hlanes =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨c₁, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨c₂, rfl, -⟩ := cvalOk_v128_inv h₂
    exact outN_redex' ⟨_, .pure (.vecShuffle hlanes)⟩
  case vecSplat =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨x, rfl⟩ := cvalOk_num_inv h₁
    exact outN_redex' ⟨_, .pure .vecSplat⟩
  case vecExtractLane _ _ _ _ hlane =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨c, rfl, -⟩ := cvalOk_v128_inv h₁
    exact outN_redex' ⟨_, .pure (.vecExtractLane hlane)⟩
  case vecReplaceLane _ _ hlane =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨c, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨x, rfl⟩ := cvalOk_num_inv h₂
    exact outN_redex' ⟨_, .pure (.vecReplaceLane hlane)⟩
  case vecExtUnOp sh₁ sh₂ op _ =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨c, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨r, hr⟩ := VecExtUnOpResult_nonempty sh₁ sh₂ op c
    exact outN_redex' ⟨_, .pure (.vecExtUnOp hr)⟩
  case vecExtBinOp sh₁ sh₂ op _ =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨c₁, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨c₂, rfl, -⟩ := cvalOk_v128_inv h₂
    obtain ⟨r, hr⟩ := VecExtBinOpResult_nonempty P sh₁ sh₂ op c₁ c₂
    exact outN_redex' ⟨_, .pure (.vecExtBinOp hr)⟩
  case vecNarrow =>
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨c₁, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨c₂, rfl, -⟩ := cvalOk_v128_inv h₂
    exact outN_redex' ⟨_, .pure .vecNarrow⟩
  case vecCvtOp sh₁ sh₂ op hop =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨c, rfl, -⟩ := cvalOk_v128_inv h₁
    obtain ⟨r, hr⟩ := VecCvtOpResult_nonempty P sh₁ sh₂ op hop c
    exact outN_redex' ⟨_, .pure (.vecCvtOp hr)⟩

/-- Progress for `REF.FUNC` and `REF.IS_NULL`
(`Step_read/ref.func`, `Step_pure/ref.is_null-*`, `8-reduction:212-221`). -/
theorem reference_progress (hs : StoreOk s) (hc : CtxOk s f C)
    (hfam : i.family = .reference) (hi : InstrOk C i it)
    (hnv : (Admin.plain i).val? = none) (hv : ValsOk s vs₀ it.params) :
    OutN P host s f C.labels C.return_ (vals vs₀ ++ .plain i :: rest) := by
  have _ := hs
  cases hi <;> simp only [Instr.family, reduceCtorEq] at hfam
  case refNull => simp [Admin.val?] at hnv
  case refFunc _ _ hx _ =>
    cases hv
    obtain ⟨a, _, ha, _, _⟩ := hc.func_bridge hx
    exact outN_redex' ⟨_, .read (.refFunc ha)⟩
  case refIsNull =>
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨r, rfl, -⟩ := cvalOk_ref_inv h₁
    by_cases hn : ∃ t, r = .null t
    · obtain ⟨t, rfl⟩ := hn
      exact outN_redex' ⟨_, .pure .refIsNullTrue⟩
    · exact outN_redex' ⟨_, .pure (.refIsNullFalse (fun t ht => hn ⟨t, ht⟩))⟩

/-- Progress for `LOCAL.GET`, `LOCAL.SET` and `LOCAL.TEE`
(`Step_read/local.get`, `Step/local.set`, `Step_pure/local.tee`,
`8-reduction:377-383`). -/
theorem local_progress (hs : StoreOk s) (hc : CtxOk s f C)
    (hfam : i.family = .locals) (hi : InstrOk C i it)
    (hnv : (Admin.plain i).val? = none) (hv : ValsOk s vs₀ it.params) :
    OutN P host s f C.labels C.return_ (vals vs₀ ++ .plain i :: rest) := by
  have _ := hs
  cases hi <;> simp only [Instr.family, reduceCtorEq] at hfam
  case localGet _ _ hx =>
    cases hv
    obtain ⟨v, hvl, -⟩ := forall₂_getElem? hc.locals_forall₂ _ _ hx
    exact outN_redex' ⟨_, .read (.localGet hvl)⟩
  case localSet _ _ hx =>
    obtain ⟨v, rfl, -⟩ := hv.one_inv
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hx
    have hlen := hc.locals_forall₂.length_eq
    exact outN_redex' ⟨_, .localSet (by omega)⟩
  case localTee =>
    obtain ⟨v, rfl, -⟩ := hv.one_inv
    exact outN_redex' ⟨_, .pure .localTee⟩

/-- Progress for `GLOBAL.GET` and `GLOBAL.SET`
(`Step_read/global.get`, `Step/global.set`, `8-reduction:389-392`). -/
theorem global_progress (hs : StoreOk s) (hc : CtxOk s f C)
    (hfam : i.family = .global) (hi : InstrOk C i it)
    (hnv : (Admin.plain i).val? = none) (hv : ValsOk s vs₀ it.params) :
    OutN P host s f C.labels C.return_ (vals vs₀ ++ .plain i :: rest) := by
  have _ := hs
  cases i <;> simp only [Instr.family, reduceCtorEq] at hfam
  case globalGet x =>
    obtain ⟨_, hx, rfl⟩ := hi.globalGet_inv
    cases hv
    obtain ⟨_, _, _, _, hg, _⟩ := hc.global_bridge hx
    exact outN_redex' ⟨_, .read (.globalGet hg)⟩
  case globalSet x =>
    obtain ⟨_, hx, -, rfl⟩ := hi.globalSet_inv
    obtain ⟨v, rfl, -⟩ := hv.one_inv
    obtain ⟨_, _, ha, hgi, _, _⟩ := hc.global_bridge hx
    exact outN_redex' ⟨_, .globalSet ha hgi⟩

/-- Progress for the `TABLE.*` instructions (`8-reduction:398-480`), including
the one-element-at-a-time bulk loops of `table.fill`, `table.copy` and
`table.init`. -/
theorem table_progress (hs : StoreOk s) (hc : CtxOk s f C)
    (hfam : i.family = .table) (hi : InstrOk C i it)
    (hnv : (Admin.plain i).val? = none) (hv : ValsOk s vs₀ it.params) :
    OutN P host s f C.labels C.return_ (vals vs₀ ++ .plain i :: rest) := by
  cases i <;> simp only [Instr.family, reduceCtorEq] at hfam
  case tableGet x =>
    obtain ⟨_, hx, rfl⟩ := hi.tableGet_inv
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨idx, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨_, ti, _, _, ht, _⟩ := hc.table_bridge hs hx
    by_cases hb : idx.toNat < ti.refs.length
    · exact outN_redex' ⟨_, .read (.tableGetVal ht (List.getElem?_eq_getElem hb))⟩
    · exact outN_redex' ⟨_, .read (.tableGetTrap ht (by omega))⟩
  case tableSet x =>
    obtain ⟨_, hx, rfl⟩ := hi.tableSet_inv
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨idx, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨r, rfl, -⟩ := cvalOk_ref_inv h₂
    obtain ⟨_, ti, ha, hti, _, _⟩ := hc.table_bridge hs hx
    by_cases hb : idx.toNat < ti.refs.length
    · exact outN_redex' ⟨_, .tableSetVal ha hti hb⟩
    · exact outN_redex' ⟨_, .tableSetTrap ha hti (by omega)⟩
  case tableSize x =>
    obtain ⟨⟨_, hx⟩, rfl⟩ := hi.tableSize_inv
    cases hv
    obtain ⟨_, ti, _, _, ht, hok⟩ := hc.table_bridge hs hx
    refine outN_redex' ⟨_, .read (.tableSize (n := BitVec.ofNat 32 ti.refs.length) ht ?_)⟩
    have hlt : ti.refs.length < 2 ^ 32 := by
      rw [hok.2.1]; exact ti.type.limits.min.isLt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  case tableGrow x =>
    obtain ⟨_, hx, rfl⟩ := hi.tableGrow_inv
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨r, rfl, -⟩ := cvalOk_ref_inv h₁
    obtain ⟨n, rfl, -⟩ := cvalOk_i32_inv h₂
    obtain ⟨a, ti, ha, hti, _, _⟩ := hc.table_bridge hs hx
    cases hg : ti.grow? n.toNat r with
    | none => exact outN_redex' ⟨_, .tableGrowFail ha hti (Or.inr hg)⟩
    | some ti' =>
      by_cases hfail : P.growMayFail .table a ti.refs.length n.toNat
      · exact outN_redex' ⟨_, .tableGrowFail ha hti (Or.inl hfail)⟩
      · exact outN_redex' ⟨_, .tableGrowSucceed ha hti hg (growMaySucceed_of_not_fail hfail)⟩
  case tableFill x =>
    obtain ⟨_, hx, rfl⟩ := hi.tableFill_inv
    obtain ⟨v₁, v₂, v₃, rfl, h₁, _, h₃⟩ := hv.three_inv
    obtain ⟨idx, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨n, rfl, -⟩ := cvalOk_i32_inv h₃
    obtain ⟨_, ti, _, _, ht, _⟩ := hc.table_bridge hs hx
    by_cases hb : ti.refs.length < idx.toNat + n.toNat
    · exact outN_redex' ⟨_, .read (.tableFillTrap ht hb)⟩
    · by_cases hn : n = 0
      · subst hn
        have hz : (0 : BitVec 32).toNat = 0 := by simp
        exact outN_redex' ⟨_, .read (.tableFillZero ht (by omega))⟩
      · exact outN_redex' ⟨_, .read (.tableFillSucc ht (by omega) hn)⟩
  case tableCopy x₁ x₂ =>
    obtain ⟨_, _, hx₁, hx₂, -, rfl⟩ := hi.tableCopy_inv
    obtain ⟨v₁, v₂, v₃, rfl, h₁, h₂, h₃⟩ := hv.three_inv
    obtain ⟨jj, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨ii, rfl, -⟩ := cvalOk_i32_inv h₂
    obtain ⟨n, rfl, -⟩ := cvalOk_i32_inv h₃
    obtain ⟨_, tx, _, _, htx, _⟩ := hc.table_bridge hs hx₁
    obtain ⟨_, ty, _, _, hty, _⟩ := hc.table_bridge hs hx₂
    by_cases hb : ty.refs.length < ii.toNat + n.toNat ∨ tx.refs.length < jj.toNat + n.toNat
    · exact outN_redex' ⟨_, .read (.tableCopyTrap htx hty hb)⟩
    · by_cases hn : n = 0
      · subst hn
        have hz : (0 : BitVec 32).toNat = 0 := by simp
        exact outN_redex' ⟨_, .read (.tableCopyZero htx hty ⟨by omega, by omega⟩)⟩
      · by_cases hle : jj.toNat ≤ ii.toNat
        · exact outN_redex' ⟨_, .read (.tableCopyLe htx hty ⟨by omega, by omega⟩ hn hle)⟩
        · exact outN_redex' ⟨_, .read (.tableCopyGt htx hty ⟨by omega, by omega⟩ hn (by omega))⟩
  case tableInit x₁ x₂ =>
    obtain ⟨_, _, hx₁, hx₂, -, rfl⟩ := hi.tableInit_inv
    obtain ⟨v₁, v₂, v₃, rfl, h₁, h₂, h₃⟩ := hv.three_inv
    obtain ⟨jj, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨ii, rfl, -⟩ := cvalOk_i32_inv h₂
    obtain ⟨n, rfl, -⟩ := cvalOk_i32_inv h₃
    obtain ⟨_, ti, _, _, ht, _⟩ := hc.table_bridge hs hx₁
    obtain ⟨_, ei, _, _, he, _⟩ := hc.elem_bridge hx₂
    by_cases hb : ei.refs.length < ii.toNat + n.toNat ∨ ti.refs.length < jj.toNat + n.toNat
    · exact outN_redex' ⟨_, .read (.tableInitTrap ht he hb)⟩
    · by_cases hn : n = 0
      · subst hn
        have hz : (0 : BitVec 32).toNat = 0 := by simp
        exact outN_redex' ⟨_, .read (.tableInitZero ht he ⟨by omega, by omega⟩)⟩
      · have hnz : n.toNat ≠ 0 := fun h0 => hn (BitVec.eq_of_toNat_eq (by simpa using h0))
        have hlt : ii.toNat < ei.refs.length := by omega
        exact outN_redex' ⟨_, .read (.tableInitSucc ht he ⟨by omega, by omega⟩ hn
          (List.getElem?_eq_getElem hlt))⟩

/-- Progress for the loads, the stores and the `MEMORY.*` instructions
(`8-reduction:489-660`), including the one-byte-at-a-time bulk loops of
`memory.fill`, `memory.copy` and `memory.init`. -/
theorem memory_progress (hs : StoreOk s) (hc : CtxOk s f C)
    (hfam : i.family = .memory) (hi : InstrOk C i it)
    (hnv : (Admin.plain i).val? = none) (hv : ValsOk s vs₀ it.params) :
    OutN P host s f C.labels C.return_ (vals vs₀ ++ .plain i :: rest) := by
  cases i <;> simp only [Instr.family, reduceCtorEq] at hfam
  case intLoad t pk arg =>
    obtain ⟨⟨_, hm⟩, -, -, rfl⟩ := hi.intLoad_inv
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨idx, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨_, mi, _, _, hmi, _⟩ := hc.mem0_bridge hs hm
    cases pk with
    | none =>
      by_cases hb : mi.bytes.size < effAddr idx.toNat arg + t.width / 8
      · exact outN_redex' ⟨_, .read (.loadIntTrap hmi hb)⟩
      · obtain ⟨cc, hcc⟩ := exists_ibytes_read (mem := mi.bytes)
          (start := effAddr idx.toNat arg) (N := t.width) (width_dvd_int t) (by omega)
        exact outN_redex' ⟨_, .read (.loadIntVal hmi hcc)⟩
    | some pp =>
      obtain ⟨sz, sx⟩ := pp
      by_cases hb : mi.bytes.size < effAddr idx.toNat arg + sz.width / 8
      · exact outN_redex' ⟨_, .read (.loadPackTrap (sx := sx) hmi hb)⟩
      · obtain ⟨cc, hcc⟩ := exists_ibytes_read (mem := mi.bytes)
          (start := effAddr idx.toNat arg) (N := sz.width) (width_dvd_pack sz) (by omega)
        exact outN_redex' ⟨_, .read (.loadPackVal (sx := sx) hmi hcc)⟩
  case floatLoad t arg =>
    obtain ⟨⟨_, hm⟩, -, rfl⟩ := hi.floatLoad_inv
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨idx, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨_, mi, _, _, hmi, _⟩ := hc.mem0_bridge hs hm
    by_cases hb : mi.bytes.size < effAddr idx.toNat arg + t.width / 8
    · exact outN_redex' ⟨_, .read (.loadFloatTrap hmi hb)⟩
    · obtain ⟨cc, hcc⟩ := exists_ibytes_read (mem := mi.bytes)
        (start := effAddr idx.toNat arg) (N := t.width) (width_dvd_float t) (by omega)
      exact outN_redex' ⟨_, .read (.loadFloatVal hmi hcc)⟩
  case intStore t pk arg =>
    obtain ⟨⟨_, hm⟩, -, -, rfl⟩ := hi.intStore_inv
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨idx, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨xx, rfl, -⟩ := cvalOk_int_inv h₂
    obtain ⟨_, mi, ha, hmi, _, _⟩ := hc.mem0_bridge hs hm
    cases pk with
    | none =>
      by_cases hb : mi.bytes.size < effAddr idx.toNat arg + t.width / 8
      · exact outN_redex' ⟨_, .storeIntTrap ha hmi hb⟩
      · obtain ⟨mi', hw⟩ := exists_writeBytes (mi := mi) (start := effAddr idx.toNat arg)
          (j := t.width / 8) (bs := nbytes (.int t) xx) (nbytes_size (.int t) xx) (by omega)
        exact outN_redex' ⟨_, .storeIntVal ha hmi hw⟩
    | some sz =>
      by_cases hb : mi.bytes.size < effAddr idx.toNat arg + sz.width / 8
      · exact outN_redex' ⟨_, .storePackTrap ha hmi hb⟩
      · obtain ⟨mi', hw⟩ := exists_writeBytes (mi := mi) (start := effAddr idx.toNat arg)
          (j := sz.width / 8) (bs := ibytes sz.width (xx.setWidth sz.width))
          (ibytes_size _ _) (by omega)
        exact outN_redex' ⟨_, .storePackVal ha hmi hw⟩
  case floatStore t arg =>
    obtain ⟨⟨_, hm⟩, -, rfl⟩ := hi.floatStore_inv
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨idx, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨xx, rfl, -⟩ := cvalOk_float_inv h₂
    obtain ⟨_, mi, ha, hmi, _, _⟩ := hc.mem0_bridge hs hm
    by_cases hb : mi.bytes.size < effAddr idx.toNat arg + t.width / 8
    · exact outN_redex' ⟨_, .storeFloatTrap ha hmi hb⟩
    · obtain ⟨mi', hw⟩ := exists_writeBytes (mi := mi) (start := effAddr idx.toNat arg)
        (j := t.width / 8) (bs := fbytes t xx) (fbytes_size t xx) (by omega)
      exact outN_redex' ⟨_, .storeFloatVal ha hmi hw⟩
  case vecLoad op arg =>
    obtain ⟨⟨_, hm⟩, -, rfl⟩ := hi.vecLoad_inv
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨idx, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨_, mi, _, _, hmi, _⟩ := hc.mem0_bridge hs hm
    exact outN_redex' (vecLoad_step (op := op) (arg := arg) (idx := idx) hmi)
  case vecLoadLane sz arg lane =>
    obtain ⟨⟨_, hm⟩, -, hlane, rfl⟩ := hi.vecLoadLane_inv
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨idx, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨cv, rfl, -⟩ := cvalOk_v128_inv h₂
    obtain ⟨_, mi, _, _, hmi, _⟩ := hc.mem0_bridge hs hm
    by_cases hb : mi.bytes.size < effAddr idx.toNat arg + sz.width / 8
    · exact outN_redex' ⟨_, .read (.vecLoadLaneOob (j := lane) hmi hb)⟩
    · obtain ⟨k, hk⟩ := exists_ibytes_read (mem := mi.bytes)
        (start := effAddr idx.toNat arg) (N := sz.width) (width_dvd_pack sz) (by omega)
      exact outN_redex' ⟨_, .read (.vecLoadLaneVal hmi hlane hk)⟩
  case vecStore arg =>
    obtain ⟨⟨_, hm⟩, -, rfl⟩ := hi.vecStore_inv
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨idx, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨cv, rfl, -⟩ := cvalOk_v128_inv h₂
    obtain ⟨_, mi, ha, hmi, _, _⟩ := hc.mem0_bridge hs hm
    by_cases hb : mi.bytes.size < effAddr idx.toNat arg + 16
    · exact outN_redex' ⟨_, .vecStoreOob ha hmi hb⟩
    · obtain ⟨mi', hw⟩ := exists_writeBytes (mi := mi) (start := effAddr idx.toNat arg)
        (j := 16) (bs := vbytes cv) (vbytes_size cv) (by omega)
      exact outN_redex' ⟨_, .vecStoreVal ha hmi hw⟩
  case vecStoreLane sz arg lane =>
    obtain ⟨⟨_, hm⟩, -, hlane, rfl⟩ := hi.vecStoreLane_inv
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv.two_inv
    obtain ⟨idx, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨cv, rfl, -⟩ := cvalOk_v128_inv h₂
    obtain ⟨_, mi, ha, hmi, _, _⟩ := hc.mem0_bridge hs hm
    by_cases hb : mi.bytes.size < effAddr idx.toNat arg + sz.width / 8
    · exact outN_redex' ⟨_, .vecStoreLaneOob (j := lane) ha hmi hb⟩
    · obtain ⟨mi', hw⟩ := exists_writeBytes (mi := mi) (start := effAddr idx.toNat arg)
        (j := sz.width / 8)
        (bs := ibytes sz.width
          ((Numerics.lanes sz.width (128 / sz.width) cv).getD lane.val 0))
        (ibytes_size _ _) (by omega)
      exact outN_redex' ⟨_, .vecStoreLaneVal ha hmi hlane hw⟩
  case memorySize =>
    obtain ⟨⟨_, hm⟩, rfl⟩ := hi.memorySize_inv
    cases hv
    obtain ⟨_, mi, _, _, hmi, hok⟩ := hc.mem0_bridge hs hm
    refine outN_redex' ⟨_, .read (.memorySize
      (n := BitVec.ofNat 32 mi.type.limits.min.val) hmi ?_)⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt mi.type.limits.min.isLt, hok.2]
  case memoryGrow =>
    obtain ⟨⟨_, hm⟩, rfl⟩ := hi.memoryGrow_inv
    obtain ⟨v, rfl, h₁⟩ := hv.one_inv
    obtain ⟨n, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨a, mi, ha, hmi, _, _⟩ := hc.mem0_bridge hs hm
    cases hg : mi.grow? n.toNat with
    | none => exact outN_redex' ⟨_, .memoryGrowFail ha hmi (Or.inr hg)⟩
    | some mi' =>
      by_cases hfail : P.growMayFail .memory a mi.pages n.toNat
      · exact outN_redex' ⟨_, .memoryGrowFail ha hmi (Or.inl hfail)⟩
      · exact outN_redex' ⟨_, .memoryGrowSucceed ha hmi hg (growMaySucceed_of_not_fail hfail)⟩
  case memoryFill =>
    obtain ⟨⟨_, hm⟩, rfl⟩ := hi.memoryFill_inv
    obtain ⟨v₁, v₂, v₃, rfl, h₁, _, h₃⟩ := hv.three_inv
    obtain ⟨idx, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨n, rfl, -⟩ := cvalOk_i32_inv h₃
    obtain ⟨_, mi, _, _, hmi, _⟩ := hc.mem0_bridge hs hm
    by_cases hb : mi.bytes.size < idx.toNat + n.toNat
    · exact outN_redex' ⟨_, .read (.memoryFillTrap hmi hb)⟩
    · by_cases hn : n = 0
      · subst hn
        have hz : (0 : BitVec 32).toNat = 0 := by simp
        exact outN_redex' ⟨_, .read (.memoryFillZero hmi (by omega))⟩
      · exact outN_redex' ⟨_, .read (.memoryFillSucc hmi (by omega) hn)⟩
  case memoryCopy =>
    obtain ⟨⟨_, hm⟩, rfl⟩ := hi.memoryCopy_inv
    obtain ⟨v₁, v₂, v₃, rfl, h₁, h₂, h₃⟩ := hv.three_inv
    obtain ⟨jj, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨ii, rfl, -⟩ := cvalOk_i32_inv h₂
    obtain ⟨n, rfl, -⟩ := cvalOk_i32_inv h₃
    obtain ⟨_, mi, _, _, hmi, _⟩ := hc.mem0_bridge hs hm
    by_cases hb : mi.bytes.size < ii.toNat + n.toNat ∨ mi.bytes.size < jj.toNat + n.toNat
    · exact outN_redex' ⟨_, .read (.memoryCopyTrap hmi hb)⟩
    · by_cases hn : n = 0
      · subst hn
        have hz : (0 : BitVec 32).toNat = 0 := by simp
        exact outN_redex' ⟨_, .read (.memoryCopyZero hmi ⟨by omega, by omega⟩)⟩
      · by_cases hle : jj.toNat ≤ ii.toNat
        · exact outN_redex' ⟨_, .read (.memoryCopyLe hmi ⟨by omega, by omega⟩ hn hle)⟩
        · exact outN_redex' ⟨_, .read (.memoryCopyGt hmi ⟨by omega, by omega⟩ hn (by omega))⟩
  case memoryInit x =>
    obtain ⟨⟨_, hm⟩, hx, rfl⟩ := hi.memoryInit_inv
    obtain ⟨v₁, v₂, v₃, rfl, h₁, h₂, h₃⟩ := hv.three_inv
    obtain ⟨jj, rfl, -⟩ := cvalOk_i32_inv h₁
    obtain ⟨ii, rfl, -⟩ := cvalOk_i32_inv h₂
    obtain ⟨n, rfl, -⟩ := cvalOk_i32_inv h₃
    obtain ⟨_, mi, _, _, hmi, _⟩ := hc.mem0_bridge hs hm
    obtain ⟨_, di, _, _, hdi⟩ := hc.data_bridge hx
    by_cases hb : di.bytes.size < ii.toNat + n.toNat ∨ mi.bytes.size < jj.toNat + n.toNat
    · exact outN_redex' ⟨_, .read (.memoryInitTrap hmi hdi hb)⟩
    · by_cases hn : n = 0
      · subst hn
        have hz : (0 : BitVec 32).toNat = 0 := by simp
        exact outN_redex' ⟨_, .read (.memoryInitZero hmi hdi ⟨by omega, by omega⟩)⟩
      · have hnz : n.toNat ≠ 0 := fun h0 => hn (BitVec.eq_of_toNat_eq (by simpa using h0))
        have hsz : di.bytes.size = di.bytes.data.size := rfl
        have hlt : ii.toNat < di.bytes.data.size := by omega
        exact outN_redex' ⟨_, .read (.memoryInitSucc hmi hdi ⟨by omega, by omega⟩ hn
          (Array.getElem?_eq_getElem hlt))⟩

/-- Progress for `ELEM.DROP` and `DATA.DROP`
(`Step/elem.drop`, `8-reduction:483`; `Step/data.drop`, `8-reduction:663`). -/
theorem data_progress (hs : StoreOk s) (hc : CtxOk s f C)
    (hfam : i.family = .data) (hi : InstrOk C i it)
    (hnv : (Admin.plain i).val? = none) (hv : ValsOk s vs₀ it.params) :
    OutN P host s f C.labels C.return_ (vals vs₀ ++ .plain i :: rest) := by
  have _ := hs
  cases hi <;> simp only [Instr.family, reduceCtorEq] at hfam
  case elemDrop _ _ hx =>
    cases hv
    obtain ⟨_, _, ha, hei, _, _⟩ := hc.elem_bridge hx
    exact outN_redex' ⟨_, .elemDrop ha hei⟩
  case dataDrop _ hx =>
    cases hv
    obtain ⟨_, _, ha, hdi, _⟩ := hc.data_bridge hx
    exact outN_redex' ⟨_, .dataDrop ha hdi⟩

/-- Progress for `BLOCK`, `LOOP`, `IF`, `BR`, `BR_IF`, `BR_TABLE` and `RETURN`
(`Step_read/block`, `/loop`, `Step_pure/if-*`, `/br_if-*`, `/br_table-*`,
`8-reduction:61-114`). `BR` and `RETURN` do not step on their own: they are the
two exit forms of `OutN`, consumed by the enclosing `LABEL_`/`FRAME_`, and the
`CtxOk` invariant is what guarantees the label (resp. the return type) and the
operands are there. -/
theorem control_progress (hs : StoreOk s) (hc : CtxOk s f C)
    (hfam : i.family = .control) (hi : InstrOk C i it)
    (hnv : (Admin.plain i).val? = none) (hv : ValsOk s vs₀ it.params) :
    OutN P host s f C.labels C.return_ (vals vs₀ ++ .plain i :: rest) := by
  have _ := hs
  cases hi <;> simp only [Instr.family, reduceCtorEq] at hfam
  case block _ _ t₁ _ hbt _ =>
    obtain ⟨Cf, hf, hu⟩ := hc.frame
    obtain ⟨ft, hft⟩ := blockType_exists hf hu hbt
    have hp : t₁ = liftResult ft.params :=
      congrArg InstrType.params (blockTypeOk_eq hf hu hft hbt)
    have hk : vs₀.length = ft.params.length := by
      rw [hv.length_eq, hp]; simp [liftResult]
    exact outN_redex' ⟨_, .read (.block hft hk)⟩
  case loop _ _ t₁ _ hbt _ =>
    obtain ⟨Cf, hf, hu⟩ := hc.frame
    obtain ⟨ft, hft⟩ := blockType_exists hf hu hbt
    have hp : t₁ = liftResult ft.params :=
      congrArg InstrType.params (blockTypeOk_eq hf hu hft hbt)
    have hk : vs₀.length = ft.params.length := by
      rw [hv.length_eq, hp]; simp [liftResult]
    exact outN_redex' ⟨_, .read (.loop hft hk)⟩
  case if_ =>
    obtain ⟨ws, c, rfl, -⟩ := hv.snoc_i32
    by_cases hc0 : c = 0
    · subst hc0
      exact outN_redex_i32 ⟨_, .pure .ifFalse⟩
    · exact outN_redex_i32 ⟨_, .pure (.ifTrue hc0)⟩
  case br l ts _ _ hl =>
    refine Or.inr (Or.inr (Or.inl ⟨vs₀, l, rest, ts, by simp, hl, ?_⟩))
    have hlen := hv.length_eq
    simp only [List.length_append] at hlen
    omega
  case brIf _ _ hl =>
    obtain ⟨ws, c, rfl, -⟩ := hv.snoc_i32
    by_cases hc0 : c = 0
    · subst hc0
      exact outN_redex_i32 ⟨_, .pure .brIfFalse⟩
    · exact outN_redex_i32 ⟨_, .pure (.brIfTrue hc0)⟩
  case brTable ls _ _ _ _ _ _ =>
    obtain ⟨ws, idx, rfl, -⟩ := hv.snoc_i32
    by_cases hlt : idx.toNat < ls.length
    · exact outN_redex_i32 ⟨_, .pure (.brTableLt (List.getElem?_eq_getElem hlt))⟩
    · exact outN_redex_i32 ⟨_, .pure (.brTableGe (by omega))⟩
  case return_ ts _ _ hr =>
    refine Or.inr (Or.inr (Or.inr ⟨vs₀, rest, ts, by simp, hr, ?_⟩))
    have hlen := hv.length_eq
    simp only [List.length_append] at hlen
    omega

/-- Progress for `CALL` and `CALL_INDIRECT`
(`Step_read/call`, `/call_indirect-call`, `/call_indirect-trap`,
`8-reduction:119-129`). -/
theorem call_progress (hs : StoreOk s) (hc : CtxOk s f C)
    (hfam : i.family = .call) (hi : InstrOk C i it)
    (hnv : (Admin.plain i).val? = none) (hv : ValsOk s vs₀ it.params) :
    OutN P host s f C.labels C.return_ (vals vs₀ ++ .plain i :: rest) := by
  cases i <;> simp only [Instr.family, reduceCtorEq] at hfam
  case call x =>
    obtain ⟨_, hx, rfl⟩ := hi.call_inv
    obtain ⟨a, _, ha, _, _⟩ := hc.func_bridge hx
    exact outN_redex (vsR := vs₀) (vt := []) (by simp) ⟨_, .read (.call ha)⟩
  case callIndirect x y =>
    obtain ⟨_, _, hxt, -, -, rfl⟩ := hi.callIndirect_inv
    obtain ⟨ws, idx, rfl, -⟩ := hv.snoc_i32
    obtain ⟨_, ti, _, _, ht, _⟩ := hc.table_bridge hs hxt
    by_cases hcall : ∃ (b : FuncAddr) (fj : FuncInst H),
        ti.refs[idx.toNat]? = some (.funcAddr b) ∧ s.funcInst? b = some fj ∧
          (⟨s, f⟩ : State H).type? y = some fj.type
    · obtain ⟨b, fj, h₁, h₂, h₃⟩ := hcall
      exact outN_redex_i32 ⟨_, .read (.callIndirectCall ht h₁ h₂ h₃)⟩
    · exact outN_redex_i32 ⟨_, .read (.callIndirectTrap ht hcall)⟩

/-- Progress for the administrative `CALL_ADDR a` (`4-runtime:132`): a Wasm
function enters a `FRAME_` (`Step_read/call_addr`, `8-reduction:131`) and a host
function uses `HostOk`'s existence clause (`Step/call_addr` host rules,
deviation 3 of `Execution/Step.lean`). -/
theorem callAddr_progress {L : List CResultType} {R : Option CResultType} {a : FuncAddr}
    {fi : FuncInst H} (hhost : HostOk host) (hs : StoreOk s)
    (hf : s.funcInst? a = some fi) (hv : ValsOk s vs₀ (liftResult fi.type.params)) :
    OutN P host s f L R (vals vs₀ ++ .callAddr a :: rest) := by
  have hvs : List.Forall₂ (ValOk s) vs₀ fi.type.params := valsOk_liftResult.mp hv
  have hk : vs₀.length = fi.type.params.length := hvs.length_eq
  cases hcode : fi.code with
  | wasm fn => exact outN_redex' ⟨_, .read (.callAddr hf hcode hk)⟩
  | host hh =>
    obtain ⟨out, hout⟩ := hhost.exists_outcome hs
      (List.mem_of_getElem? (show s.funcs[a]? = some fi from hf)) hcode hvs
    cases out with
    | returned s' r => exact outN_redex' ⟨_, .callAddrHost hf hcode hk hout⟩
    | diverged => exact outN_redex' ⟨_, .callAddrHostDiv hf hcode hk hout⟩

/-- The dispatch: every plain instruction that is not a value has an outcome. -/
theorem plain_progress (hs : StoreOk s) (hc : CtxOk s f C) (hi : InstrOk C i it)
    (hnv : (Admin.plain i).val? = none) (hv : ValsOk s vs₀ it.params) :
    OutN P host s f C.labels C.return_ (vals vs₀ ++ .plain i :: rest) := by
  cases hfam : i.family with
  | parametric => exact parametric_progress hs hc hfam hi hnv hv
  | control => exact control_progress hs hc hfam hi hnv hv
  | call => exact call_progress hs hc hfam hi hnv hv
  | numeric => exact numeric_progress hs hc hfam hi hnv hv
  | vector => exact vector_progress hs hc hfam hi hnv hv
  | reference => exact reference_progress hs hc hfam hi hnv hv
  | locals => exact local_progress hs hc hfam hi hnv hv
  | global => exact global_progress hs hc hfam hi hnv hv
  | table => exact table_progress hs hc hfam hi hnv hv
  | memory => exact memory_progress hs hc hfam hi hnv hv
  | data => exact data_progress hs hc hfam hi hnv hv

end Families

/-! ## The code induction -/

/-- **Progress, generalised.** Typed administrative code under a typed prefix of
values has an outcome: it is a value stack of the result types, it steps, or it
is one of the three exit forms `TRAP`, `br l` and `return`. -/
theorem progress_aux {P : Profile} {host : HostSemantics H} {s : Store H}
    (hhost : HostOk host) (hs : StoreOk s) {C : Context} {as : List Admin} {it : InstrType}
    (h : AdminsOk s C as it) :
    ∀ (f : Frame) (vs₀ : List Val), CtxOk s f C → ValsOk s vs₀ it.params →
      Out P host s f C.labels C.return_ (vals vs₀ ++ as) it.results := by
  refine AdminsOk.rec
    (motive_1 := fun C a it _ => ∀ (f : Frame) (vs₀ : List Val), CtxOk s f C →
      ValsOk s vs₀ it.params →
      Out P host s f C.labels C.return_ (vals vs₀ ++ [a]) it.results)
    (motive_2 := fun C as it _ => ∀ (f : Frame) (vs₀ : List Val), CtxOk s f C →
      ValsOk s vs₀ it.params →
      Out P host s f C.labels C.return_ (vals vs₀ ++ as) it.results)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  -- `Instr_ok2/plain`
  · intro C i it hi f vs₀ hcx hv
    cases hnv : (Admin.plain i).val? with
    | none => exact .inr (plain_progress (rest := []) hs hcx hi hnv hv)
    | some v => exact value_out (.plain hi) hnv hv
  -- `Instr_ok2/ref` at `REF.FUNC_ADDR`
  · intro C a fi hfa f vs₀ hcx hv
    exact value_out (C := C) (.refFuncAddr hfa) rfl hv
  -- `Instr_ok2/ref` at `REF.HOST_ADDR`
  · intro C a f vs₀ hcx hv
    exact value_out (C := C) (.refHostAddr a) rfl hv
  -- `CALL_ADDR`
  · intro C a fi hfa f vs₀ hcx hv
    exact .inr (callAddr_progress (rest := []) hhost hs hfa hv)
  -- `Instr_ok2/label`
  · intro C n cont body t' ts hn hcont hb ihcont ihb f vs₀ hcx hv
    cases hv
    refine .inr (.inl ?_)
    have hout := ihb f [] (hcx.withLabel t') .nil
    simp only [Context.withLabel, vals_nil, List.nil_append] at hout
    exact label_step hn hout
  -- `Instr_ok2/frame`
  · intro C C' n fr body ts hfr hn hb ihb f vs₀ hcx hv
    cases hv
    refine .inr (.inl ?_)
    have hout := ihb fr [] ((CtxOk.ofFrame hfr).setReturn (some ts)) .nil
    simp only [vals_nil, List.nil_append] at hout
    exact frame_step hfr.labels_nil hn hout
  -- `Instr_ok2/trap`
  · intro C it f vs₀ hcx hv
    exact .inr (.inr (.inl ⟨vs₀, [], by simp⟩))
  -- `Instrs_ok/empty`
  · intro C f vs₀ hcx hv
    cases hv
    exact .inl ⟨[], rfl, .nil⟩
  -- `Instrs_ok/instr`
  · intro C a it ha iha f vs₀ hcx hv
    exact iha f vs₀ hcx hv
  -- `Instrs_ok/seq`
  · intro C as₁ as₂ t₁ t₂ t₃ h₁ h₂ ih₁ ih₂ f vs₀ hcx hv
    rcases ih₁ f vs₀ hcx hv with ⟨vs₁, e, hv₁⟩ | hn
    · rw [← List.append_assoc, e]
      exact ih₂ f vs₁ hcx hv₁
    · rw [← List.append_assoc]
      exact .inr (hn.append as₂)
  -- `Instrs_ok/sub`
  · intro C as it it' hb hsub ih f vs₀ hcx hv
    exact (ih f vs₀ hcx (hv.sub hsub.1)).sub hsub.2
  -- `Instrs_ok/frame`
  · intro C as ts t₁ t₂ hb ih f vs₀ hcx hv
    obtain ⟨va, vb, rfl, hva, hvb⟩ := forall₂_split hv
    have hout := (ih f vb hcx hvb).prepend hva
    rw [vals_append, List.append_assoc]
    exact hout

/-! ## Progress -/

/-- **Progress.** A well-typed configuration is terminal — a value stack or
`TRAP` (`4-runtime:46`) — or it steps. See the module docstring for why this is
*false* for the literal SpecTec 2.0 rules (`vcvtop_badShape_stuck`). -/
theorem Config.progress {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {c : Config H} {ts : List CValType} (hc : ConfigOk c ts) :
    c.Terminal ∨ ∃ c', Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨C, ⟨hs, hf⟩, hcode⟩ := hc
  have h := progress_aux (P := P) hhost hs hcode f [] (CtxOk.ofFrame hf) .nil
  simp only [vals_nil, List.nil_append, hf.labels_nil, hf.return_none] at h
  rcases h with ⟨vs, rfl, -⟩ | ⟨c', hc'⟩ | ⟨vs, rest, rfl⟩ | ⟨vs, l, rest, tl, -, h1, -⟩ |
    ⟨vs, rest, rt, -, h1, -⟩
  · exact .inl ⟨.values vs, rfl⟩
  · exact .inr ⟨c', hc'⟩
  · rcases trap_or_step (P := P) (host := host) (s := s) (f := f) vs rest with
      ⟨rfl, rfl⟩ | hst
    · exact .inl ⟨.trap, rfl⟩
    · exact .inr hst
  · simp at h1
  · simp at h1

end Silmaril.Wasm.V2.Execution
