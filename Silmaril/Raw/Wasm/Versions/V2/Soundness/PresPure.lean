module

public import Silmaril.Raw.Wasm.Versions.V2.Soundness.Config
public import Silmaril.Raw.Wasm.Versions.V2.Validation.Inversion

/-!
# WebAssembly 2.0 soundness: preservation for `Step_pure`

The proof toolkit for `Silmaril/Wasm/V2/Soundness/Preservation.lean`, and the
whole of `PureStep.preservation`: the rules of `8-reduction` that read neither
the store nor the frame.

**Deviation (no SpecTec source).** As recorded in
`Silmaril/Wasm/V2/Soundness/Store.lean`, the pinned SpecTec wasm-2.0 sources
(WebAssembly/spec `608711107b7f1edb13efd57b7d79b49477462d36`, see
`specs/wasm/core-2.0.json`) contain **no `7-soundness` file**, so 2.0 states no
preservation theorem at all. Everything here is the W3C WebAssembly 2.0
appendix *Soundness*, cross-checked against the Core 3.0 development
(`Silmaril/Wasm/Execution/Core/Soundness/**`).

## Proof toolkit

Everything rests on three small lemmas, all unconditional (2.0 has no
`Instrtype_ok`/`Resulttype_ok`, so there is no regularity plumbing to carry):

* `AdminsOk.rebuild` — one `Instrs_ok/frame` (`6-typing:175`) followed by one
  `Instrs_ok/sub` (`6-typing:168`), which is the normal form of any chain of
  the two, and the *only* way typing is built below;
* `AdminsOk.flat_inv` — inversion of a *flat redex* `val* instr` (the shape of
  every non-control rule of `8-reduction`), producing the operands' types, the
  frame `us`, and the instruction's own `Instr_ok` type;
* `AdminsOk.flat0`/`flat1`/`flat2`/`flat3` and their `_const`/`_nil`/`_val`
  specialisations — the fixed-arity forms, where a length argument forces the
  instruction's parameter types to be *exactly* the lift of the operands'
  types (2.0 values never have type `BOT`, so no `BOT` can hide there).

Together they reduce every flat rule to: invert `Instr_ok`, read off the
operand types, retype the reduct. The control rules (`LABEL_`, `FRAME_`, `BR`,
`RETURN`) additionally use `AdminOk.label_inv`/`AdminOk.frame_inv` and the two
splitting lemmas `sub_split_left`/`sub_split_right`.

## What is proved here

`PureStep.preservation` is complete: all eight families of `Step_pure` — the
parametric rules (`8-reduction:40-58`), the block and branch rules
(`:61-114`), the pure function rules (`:138-145`), the trap rules (`:148-158`),
the numeric rules (`:172-207`), the reference rules (`:210-222`), the vector
rules (`:225-372`) and the pure local rule (`:383`). `Step_pure` reads neither
the store nor the frame, so the statement mentions neither `Store_ok` nor
`Frame_ok`: it is a fact about typing alone.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## Result-type algebra

The two splitting lemmas `CResultType.sub_append_left_inv`
(`Validation/Inversion.lean`) does not provide. -/

/-- Splitting a `Resulttype_sub` (`6-typing:80`) along a concatenation on the
*right*: the mirror image of `CResultType.sub_append_left_inv`. -/
theorem sub_append_right_inv : ∀ {a b c : CResultType},
    CResultType.Sub a (b ++ c) →
      ∃ a₁ a₂, a = a₁ ++ a₂ ∧ CResultType.Sub a₁ b ∧ CResultType.Sub a₂ c
  | a, [], _, h => ⟨[], a, rfl, List.Forall₂.nil, h⟩
  | _, x :: b, _, h => by
      rw [List.cons_append] at h
      obtain ⟨y, a', hxy, hrest, rfl⟩ := List.forall₂_cons_right_iff.mp h
      obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := sub_append_right_inv (b := b) hrest
      exact ⟨y :: a₁, a₂, rfl, List.Forall₂.cons hxy h₁, h₂⟩

/-- Two concatenations related by `Resulttype_sub` split where the *left*
components have equal length. -/
theorem sub_split_left {a b c d : CResultType} (hlen : a.length = c.length)
    (h : CResultType.Sub (a ++ b) (c ++ d)) :
    CResultType.Sub a c ∧ CResultType.Sub b d := by
  obtain ⟨c₁, c₂, he, h₁, h₂⟩ := CResultType.sub_append_left_inv h
  have hl : c.length = c₁.length := by
    rw [← hlen]; exact CResultType.sub_length h₁
  obtain ⟨rfl, rfl⟩ := List.append_inj he hl
  exact ⟨h₁, h₂⟩

/-- Two concatenations related by `Resulttype_sub` split where the *right*
components have equal length. -/
theorem sub_split_right {a b c d : CResultType} (hlen : b.length = d.length)
    (h : CResultType.Sub (a ++ b) (c ++ d)) :
    CResultType.Sub a c ∧ CResultType.Sub b d := by
  have htot := CResultType.sub_length h
  simp only [List.length_append] at htot
  exact sub_split_left (by omega) h

/-- `liftResult` is injective: a 2.0 value type is recovered from its lifting. -/
theorem liftResult_inj : ∀ {a b : ResultType}, liftResult a = liftResult b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [liftResult, List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    injection h1 with h1
    rw [h1, liftResult_inj (a := a) (b := b) h2]

/-! ## Retyping a reduct

`AdminsOk.rebuild` is the only way typing is ever *built* below: every reduct is
typed at its own natural type and then framed and subsumed into the type the
redex had. -/

/-- One `Instrs_ok/frame` (`6-typing:175`) followed by one `Instrs_ok/sub`
(`6-typing:168`). Every chain of the two normalises to this. -/
theorem AdminsOk.rebuild {s : Store H} {C : Context} {us ps rs : CResultType}
    {it : InstrType} {as : List Admin}
    (hp : CResultType.Sub it.params (us ++ ps))
    (hr : CResultType.Sub (us ++ rs) it.results)
    (h : AdminsOk s C as ⟨ps, rs⟩) : AdminsOk s C as it :=
  (AdminsOk.frame (ts := us) h).sub ⟨hp, hr⟩

/-- `AdminsOk.single_inv` with the `InstrType.Sub` premise already unfolded. -/
theorem AdminsOk.single_inv' {s : Store H} {C : Context} {a : Admin} {it : InstrType}
    (h : AdminsOk s C [a] it) :
    ∃ (us : CResultType) (it₀ : InstrType), AdminOk s C a it₀ ∧
      CResultType.Sub it.params (us ++ it₀.params) ∧
      CResultType.Sub (us ++ it₀.results) it.results := by
  obtain ⟨us, it₀, ha, hs⟩ := AdminsOk.single_inv h
  exact ⟨us, it₀, ha, hs.1, hs.2⟩

/-! ## Flat redexes

A *flat redex* is `val* instr`: the shape of every non-control rule of
`8-reduction`. -/

/-- **Inversion of a flat redex.** The values are typed, the instruction has an
`Instr_ok` type `it₀`, and the redex's type is `it₀` framed by `us` and
subsumed. -/
theorem AdminsOk.flat_inv {s : Store H} {C : Context} {vs : List Val} {i : Instr}
    {it : InstrType} (h : AdminsOk s C (vals vs ++ [.plain i]) it) :
    ∃ (ts : ResultType) (us : CResultType) (it₀ : InstrType),
      List.Forall₂ (ValOk s) vs ts ∧ InstrOk C i it₀ ∧
      CResultType.Sub (it.params ++ liftResult ts) (us ++ it₀.params) ∧
      CResultType.Sub (us ++ it₀.results) it.results := by
  obtain ⟨t₁, t₂⟩ := it
  obtain ⟨tm, h₁, h₂⟩ := AdminsOk.append_inv h
  obtain ⟨ts, hvs, hsub⟩ := AdminsOk.vals_inv h₁
  obtain ⟨us, it₀, ha, hp, hr⟩ := AdminsOk.single_inv' h₂
  exact ⟨ts, us, it₀, hvs, ha.plain_inv, CResultType.sub_trans hsub hp, hr⟩

/-- **Flat redex of fixed arity.** When the instruction's parameter count is
exactly the number of operands in the redex, its parameter types are *exactly*
the lift of the operands' types (2.0 values never have type `BOT`), the frame
`us` carries the whole incoming stack, and the reduct need only be typed at
`eps -> it₀.results`. -/
theorem AdminsOk.flat_pres {s : Store H} {C : Context} {vs : List Val} {i : Instr}
    {it : InstrType} {as : List Admin}
    (harity : ∀ it₀, InstrOk C i it₀ → it₀.params.length = vs.length)
    (hout : ∀ (ts : ResultType) (it₀ : InstrType), List.Forall₂ (ValOk s) vs ts →
      InstrOk C i it₀ → it₀.params = liftResult ts →
      AdminsOk s C as ⟨[], it₀.results⟩)
    (h : AdminsOk s C (vals vs ++ [.plain i]) it) : AdminsOk s C as it := by
  obtain ⟨ts, us, it₀, hvs, hi, hp, hr⟩ := AdminsOk.flat_inv h
  have hlen : (liftResult ts).length = it₀.params.length := by
    rw [length_liftResult, harity it₀ hi, hvs.length_eq]
  obtain ⟨hp1, hp2⟩ := sub_split_right hlen hp
  have hps : it₀.params = liftResult ts := CResultType.sub_liftResult_iff.mp hp2
  exact AdminsOk.rebuild (us := us) (ps := []) (by simpa using hp1) hr
    (hout ts it₀ hvs hi hps)

/-- Arity-zero flat redex. -/
theorem AdminsOk.flat0 {s : Store H} {C : Context} {i : Instr} {it : InstrType}
    {as : List Admin}
    (harity : ∀ it₀, InstrOk C i it₀ → it₀.params = [])
    (hout : ∀ it₀ : InstrType, InstrOk C i it₀ → AdminsOk s C as ⟨[], it₀.results⟩)
    (h : AdminsOk s C [.plain i] it) : AdminsOk s C as it := by
  refine AdminsOk.flat_pres (vs := []) (fun it₀ hi => by rw [harity it₀ hi]; rfl)
    (fun ts it₀ hvs hi _ => ?_) h
  cases hvs
  exact hout it₀ hi

/-- Arity-one flat redex. -/
theorem AdminsOk.flat1 {s : Store H} {C : Context} {v : Val} {i : Instr} {it : InstrType}
    {as : List Admin}
    (harity : ∀ it₀, InstrOk C i it₀ → it₀.params.length = 1)
    (hout : ∀ (t : ValType) (it₀ : InstrType), ValOk s v t → InstrOk C i it₀ →
      it₀.params = [.val t] → AdminsOk s C as ⟨[], it₀.results⟩)
    (h : AdminsOk s C [v.toAdmin, .plain i] it) : AdminsOk s C as it := by
  refine AdminsOk.flat_pres (vs := [v]) harity (fun ts it₀ hvs hi hps => ?_) h
  obtain ⟨t, ts', hv, hts, rfl⟩ := List.forall₂_cons_left_iff.mp hvs
  cases hts
  exact hout t it₀ hv hi (by simpa using hps)

/-- Arity-two flat redex. -/
theorem AdminsOk.flat2 {s : Store H} {C : Context} {v₁ v₂ : Val} {i : Instr} {it : InstrType}
    {as : List Admin}
    (harity : ∀ it₀, InstrOk C i it₀ → it₀.params.length = 2)
    (hout : ∀ (t₁ t₂ : ValType) (it₀ : InstrType), ValOk s v₁ t₁ → ValOk s v₂ t₂ →
      InstrOk C i it₀ → it₀.params = [.val t₁, .val t₂] →
      AdminsOk s C as ⟨[], it₀.results⟩)
    (h : AdminsOk s C [v₁.toAdmin, v₂.toAdmin, .plain i] it) : AdminsOk s C as it := by
  refine AdminsOk.flat_pres (vs := [v₁, v₂]) harity (fun ts it₀ hvs hi hps => ?_) h
  obtain ⟨t₁, ts₁, hv₁, hts₁, rfl⟩ := List.forall₂_cons_left_iff.mp hvs
  obtain ⟨t₂, ts₂, hv₂, hts₂, rfl⟩ := List.forall₂_cons_left_iff.mp hts₁
  cases hts₂
  exact hout t₁ t₂ it₀ hv₁ hv₂ hi (by simpa using hps)

/-- Arity-three flat redex. -/
theorem AdminsOk.flat3 {s : Store H} {C : Context} {v₁ v₂ v₃ : Val} {i : Instr}
    {it : InstrType} {as : List Admin}
    (harity : ∀ it₀, InstrOk C i it₀ → it₀.params.length = 3)
    (hout : ∀ (t₁ t₂ t₃ : ValType) (it₀ : InstrType), ValOk s v₁ t₁ → ValOk s v₂ t₂ →
      ValOk s v₃ t₃ → InstrOk C i it₀ → it₀.params = [.val t₁, .val t₂, .val t₃] →
      AdminsOk s C as ⟨[], it₀.results⟩)
    (h : AdminsOk s C [v₁.toAdmin, v₂.toAdmin, v₃.toAdmin, .plain i] it) :
    AdminsOk s C as it := by
  refine AdminsOk.flat_pres (vs := [v₁, v₂, v₃]) harity (fun ts it₀ hvs hi hps => ?_) h
  obtain ⟨t₁, ts₁, hv₁, hts₁, rfl⟩ := List.forall₂_cons_left_iff.mp hvs
  obtain ⟨t₂, ts₂, hv₂, hts₂, rfl⟩ := List.forall₂_cons_left_iff.mp hts₁
  obtain ⟨t₃, ts₃, hv₃, hts₃, rfl⟩ := List.forall₂_cons_left_iff.mp hts₂
  cases hts₃
  exact hout t₁ t₂ t₃ it₀ hv₁ hv₂ hv₃ hi (by simpa using hps)

/-! ## Inversion for the two control forms -/

/-- Inversion of `Instr_ok2/label` (`7.1-soundness:32`). -/
theorem AdminOk.label_inv {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {body : List Admin} {it : InstrType} (h : AdminOk s C (.label n cont body) it) :
    ∃ t' ts : CResultType, t'.length = n ∧ it = ⟨[], ts⟩ ∧
      AdminsOk s C (expression cont) ⟨t', ts⟩ ∧ AdminsOk s (C.withLabel t') body ⟨[], ts⟩ := by
  cases h with
  | label hn hc hb => exact ⟨_, _, hn, rfl, hc, hb⟩

/-- Inversion of `Instr_ok2/frame` (`7.1-soundness:37`). -/
theorem AdminOk.frame_inv {s : Store H} {C : Context} {n : Nat} {fr : Frame}
    {body : List Admin} {it : InstrType} (h : AdminOk s C (.frame n fr body) it) :
    ∃ (C' : Context) (ts : CResultType), FrameOk s fr C' ∧ ts.length = n ∧ it = ⟨[], ts⟩ ∧
      AdminsOk s { C' with return_ := some ts } body ⟨[], ts⟩ := by
  cases h with
  | frame hf hn hb => exact ⟨_, _, hf, hn, rfl, hb⟩

/-- The only type an `I32` value has is `I32`. -/
theorem ValOk.i32_eq {s : Store H} {c : BitVec 32} {t : ValType} (h : ValOk s (Val.i32 c) t) :
    t = .i32 := by cases h; rfl

/-! ## Parametric instructions (`8-reduction:40-58`)

`Step_pure/unreachable` (`8-reduction:42`) reduces to `TRAP`, which has every
instruction type (`AdminsOk.trap_it`), so it needs no lemma of its own; the same
goes for every `-trap` and `-oob` rule below. -/

/-- `Step_pure/nop` (`8-reduction:45`). -/
theorem pres_nop {s : Store H} {C : Context} {it : InstrType}
    (h : AdminsOk s C [.plain .nop] it) : AdminsOk s C [] it :=
  AdminsOk.flat0 (fun _ hi => by cases hi; rfl) (fun _ hi => by cases hi; exact .nil) h

/-- `Step_pure/drop` (`8-reduction:48`). -/
theorem pres_drop {s : Store H} {C : Context} {v : Val} {it : InstrType}
    (h : AdminsOk s C [v.toAdmin, .plain .drop] it) : AdminsOk s C [] it :=
  AdminsOk.flat1 (fun _ hi => by cases hi; rfl)
    (fun _ _ _ hi _ => by cases hi; exact .nil) h

/-- `Instr_ok/select-expl` and `/select-impl` (`6-typing:192`, `195`) both give
`SELECT` the type `t t i32 -> t`, with the *same* `t` for the two data
operands. -/
theorem select_inv {C : Context} {ts? : Option (List ValType)} {it₀ : InstrType}
    {t₁ t₂ t₃ : ValType} (hi : InstrOk C (.select ts?) it₀)
    (hps : it₀.params = [.val t₁, .val t₂, .val t₃]) :
    it₀.results = [.val t₁] ∧ t₁ = t₂ := by
  cases hi <;>
    · simp only [List.cons.injEq, and_true] at hps
      exact ⟨by rw [hps.1], by simpa using hps.1.symm.trans hps.2.1⟩

/-- `Step_pure/select-true` (`8-reduction:52`). -/
theorem pres_selectTrue {s : Store H} {C : Context} {v₁ v₂ : Val} {c : BitVec 32}
    {ts? : Option (List ValType)} {it : InstrType}
    (h : AdminsOk s C [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts?)] it) :
    AdminsOk s C [v₁.toAdmin] it := by
  refine AdminsOk.flat3 (v₃ := Val.i32 c) (fun _ hi => by cases hi <;> rfl)
    (fun _ _ _ _ h₁ _ _ hi hps => ?_) h
  rw [(select_inv hi hps).1]
  exact .single (AdminOk.toAdmin_ok h₁)

/-- `Step_pure/select-false` (`8-reduction:56`). -/
theorem pres_selectFalse {s : Store H} {C : Context} {v₁ v₂ : Val} {c : BitVec 32}
    {ts? : Option (List ValType)} {it : InstrType}
    (h : AdminsOk s C [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts?)] it) :
    AdminsOk s C [v₂.toAdmin] it := by
  refine AdminsOk.flat3 (v₃ := Val.i32 c) (fun _ hi => by cases hi <;> rfl)
    (fun _ _ _ _ _ h₂ _ hi hps => ?_) h
  obtain ⟨hres, rfl⟩ := select_inv hi hps
  rw [hres]
  exact .single (AdminOk.toAdmin_ok h₂)

/-! ## Block instructions (`8-reduction:61-86`) -/

/-- `Step_pure/if-true` and `/if-false` (`8-reduction:76`, `80`): the chosen
branch becomes a `BLOCK` of the same block type. -/
theorem pres_if {s : Store H} {C : Context} {c : BitVec 32} {bt : BlockType}
    {b₁ b₂ body : List Instr} {it : InstrType} (hb : body = b₁ ∨ body = b₂)
    (h : AdminsOk s C [constI32 c, .plain (.if_ bt b₁ b₂)] it) :
    AdminsOk s C [.plain (.block bt body)] it := by
  obtain ⟨ts, us, it₀, hvs, hi, hp, hr⟩ := AdminsOk.flat_inv (vs := [Val.i32 c]) h
  obtain ⟨t, ts', hv, hts, rfl⟩ := List.forall₂_cons_left_iff.mp hvs
  cases hts
  obtain rfl := ValOk.i32_eq hv
  cases hi with
  | @if_ _ _ _ _ t₁ t₂ hbt hthen helse =>
    have hp' : CResultType.Sub (it.params ++ liftResult [ValType.i32])
        ((us ++ t₁) ++ [CValType.val ValType.i32]) := by
      simpa [List.append_assoc] using hp
    obtain ⟨hp1, -⟩ := sub_split_right (by simp) hp'
    refine AdminsOk.rebuild (us := us) (ps := t₁) (rs := t₂) hp1 hr ?_
    refine .single (.plain (.block hbt ?_))
    rcases hb with rfl | rfl
    · exact hthen
    · exact helse

/-- `Step_pure/label-vals` (`8-reduction:85`). -/
theorem pres_labelVals {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {vs : List Val} {it : InstrType} (h : AdminsOk s C [.label n cont (vals vs)] it) :
    AdminsOk s C (vals vs) it := by
  obtain ⟨us, it₀, ha, hp, hr⟩ := AdminsOk.single_inv' h
  obtain ⟨t', ts, -, rfl, -, hb⟩ := ha.label_inv
  refine AdminsOk.rebuild (ps := []) hp hr ?_
  obtain ⟨vts, hvs, hsub⟩ := AdminsOk.vals_inv hb
  exact (AdminsOk.of_vals hvs).sub ⟨CResultType.sub_refl [], by simpa using hsub⟩

/-! ## Branch instructions (`8-reduction:89-114`) -/

/-- `Step_pure/br-zero` (`8-reduction:92`): the label's own arity of operands is
kept, the rest of the stack inside the label is discarded, and the label's
continuation runs. -/
theorem pres_brZero {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {vs' vs : List Val} {l : LabelIdx} {rest : List Admin} {it : InstrType}
    (hl : l.toNat = 0) (hvn : vs.length = n)
    (h : AdminsOk s C [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)] it) :
    AdminsOk s C (vals vs ++ expression cont) it := by
  obtain ⟨us, it₀, ha, hp, hr⟩ := AdminsOk.single_inv' h
  obtain ⟨t', ts, hn, rfl, hc, hb⟩ := ha.label_inv
  refine AdminsOk.rebuild (ps := []) hp hr ?_
  obtain ⟨m₁, h1, -⟩ := AdminsOk.append_inv hb
  obtain ⟨m₂, h2, h3⟩ := AdminsOk.append_inv h1
  obtain ⟨m₃, -, h4⟩ := AdminsOk.append_inv h2
  obtain ⟨vts, hvs, hsub⟩ := AdminsOk.vals_inv h4
  obtain ⟨us', it₁, ha', hp', -⟩ := AdminsOk.single_inv' h3
  cases ha'.plain_inv with
  | @br _ _ lts a b hlbl =>
    rw [hl] at hlbl
    simp only [Context.withLabel, List.getElem?_cons_zero, Option.some.injEq] at hlbl
    rw [← hlbl] at hp'
    have hcomb : CResultType.Sub (m₃ ++ liftResult vts) ((us' ++ a) ++ t') := by
      rw [List.append_assoc]
      exact CResultType.sub_trans hsub hp'
    obtain ⟨-, h2'⟩ := sub_split_right (by simp [← hvs.length_eq, hvn, hn]) hcomb
    obtain rfl : t' = liftResult vts := CResultType.sub_liftResult_iff.mp h2'
    exact (AdminsOk.of_vals hvs).append hc

/-- `Step_pure/br-succ` (`8-reduction:95`): the branch bubbles out of the label
with its index decremented, carrying the whole stack above it. -/
theorem pres_brSucc {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {vs : List Val} {l : LabelIdx} {rest : List Admin} {it : InstrType} (hl : 0 < l.toNat)
    (h : AdminsOk s C [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)] it) :
    AdminsOk s C (vals vs ++ [.plain (.br (labelPred l))]) it := by
  obtain ⟨us, it₀, ha, hp, hr⟩ := AdminsOk.single_inv' h
  obtain ⟨t', ts, -, rfl, -, hb⟩ := ha.label_inv
  refine AdminsOk.rebuild (ps := []) hp hr ?_
  obtain ⟨m₁, h1, -⟩ := AdminsOk.append_inv hb
  obtain ⟨m₂, h2, h3⟩ := AdminsOk.append_inv h1
  obtain ⟨vts, hvs, hsub⟩ := AdminsOk.vals_inv h2
  obtain ⟨us', it₁, ha', hp', -⟩ := AdminsOk.single_inv' h3
  cases ha'.plain_inv with
  | @br _ _ lts a b hlbl =>
    have hk : l.toNat = (l.toNat - 1) + 1 := (Nat.succ_pred_eq_of_pos hl).symm
    have hlbl' : C.labels[(labelPred l).toNat]? = some lts := by
      rw [hk] at hlbl
      simpa [Context.withLabel, labelPred, Idx.toNat] using hlbl
    have hcomb : CResultType.Sub (liftResult vts) ((us' ++ a) ++ lts) := by
      rw [List.append_assoc]
      exact CResultType.sub_trans (by simpa using hsub) hp'
    obtain ⟨A, B, hAB, -, hBl⟩ := sub_append_right_inv hcomb
    have hbr : AdminsOk s C [.plain (.br (labelPred l))] ⟨A ++ B, ts⟩ := by
      refine (AdminsOk.single (.plain (InstrOk.br (t₁ := A) (t₂ := ts) hlbl'))).sub ?_
      exact ⟨CResultType.sub_append (CResultType.sub_refl A) hBl, CResultType.sub_refl ts⟩
    have hv : AdminsOk s C (vals vs) ⟨[], A ++ B⟩ := by
      rw [← hAB]; exact AdminsOk.of_vals hvs
    exact hv.append hbr

/-- `Step_pure/br_if-true` (`8-reduction:99`). -/
theorem pres_brIfTrue {s : Store H} {C : Context} {c : BitVec 32} {l : LabelIdx}
    {it : InstrType} (h : AdminsOk s C [constI32 c, .plain (.brIf l)] it) :
    AdminsOk s C [.plain (.br l)] it := by
  obtain ⟨ts, us, it₀, hvs, hi, hp, hr⟩ := AdminsOk.flat_inv (vs := [Val.i32 c]) h
  obtain ⟨t, ts', hv, hts, rfl⟩ := List.forall₂_cons_left_iff.mp hvs
  cases hts
  obtain rfl := ValOk.i32_eq hv
  cases hi with
  | @brIf _ _ lts hlbl =>
    have hp' : CResultType.Sub (it.params ++ liftResult [ValType.i32])
        (us ++ lts ++ [CValType.val ValType.i32]) := by
      simpa [List.append_assoc] using hp
    obtain ⟨hp1, -⟩ := sub_split_right (by simp) hp'
    exact AdminsOk.rebuild hp1 hr
      (.single (.plain (InstrOk.br (t₁ := []) (t₂ := lts) hlbl)))

/-- `Step_pure/br_if-false` (`8-reduction:103`). -/
theorem pres_brIfFalse {s : Store H} {C : Context} {c : BitVec 32} {l : LabelIdx}
    {it : InstrType} (h : AdminsOk s C [constI32 c, .plain (.brIf l)] it) :
    AdminsOk s C [] it := by
  obtain ⟨ts, us, it₀, hvs, hi, hp, hr⟩ := AdminsOk.flat_inv (vs := [Val.i32 c]) h
  obtain ⟨t, ts', hv, hts, rfl⟩ := List.forall₂_cons_left_iff.mp hvs
  cases hts
  obtain rfl := ValOk.i32_eq hv
  cases hi with
  | @brIf _ _ lts hlbl =>
    have hp' : CResultType.Sub (it.params ++ liftResult [ValType.i32])
        (us ++ lts ++ [CValType.val ValType.i32]) := by
      simpa [List.append_assoc] using hp
    obtain ⟨hp1, -⟩ := sub_split_right (by simp) hp'
    exact AdminsOk.rebuild hp1 hr (AdminsOk.id lts)

/-- `Step_pure/br_table-lt` and `/br_table-ge` (`8-reduction:108`, `112`): both
kinds of target have a result type above the common `t*` of
`Instr_ok/br_table`, which is what `hpick` records. -/
theorem pres_brTable {s : Store H} {C : Context} {c : BitVec 32} {ls : List LabelIdx}
    {l' l : LabelIdx} {it : InstrType}
    (hpick : ∀ ts' : CResultType,
      (∀ k ∈ ls, ∃ lt, C.labels[k.toNat]? = some lt ∧ CResultType.Sub ts' lt) →
      (∃ lt, C.labels[l'.toNat]? = some lt ∧ CResultType.Sub ts' lt) →
      ∃ lt, C.labels[l.toNat]? = some lt ∧ CResultType.Sub ts' lt)
    (h : AdminsOk s C [constI32 c, .plain (.brTable ls l')] it) :
    AdminsOk s C [.plain (.br l)] it := by
  obtain ⟨ts, us, it₀, hvs, hi, hp, hr⟩ := AdminsOk.flat_inv (vs := [Val.i32 c]) h
  obtain ⟨t, ts', hv, hts, rfl⟩ := List.forall₂_cons_left_iff.mp hvs
  cases hts
  obtain rfl := ValOk.i32_eq hv
  cases hi with
  | @brTable _ _ _ bts t₁ t₂ hls hl' =>
    obtain ⟨lt, hlbl, hsub⟩ := hpick bts hls hl'
    have hp' : CResultType.Sub (it.params ++ liftResult [ValType.i32])
        ((us ++ t₁ ++ bts) ++ [CValType.val ValType.i32]) := by
      simpa [List.append_assoc] using hp
    obtain ⟨hp1, -⟩ := sub_split_right (by simp) hp'
    refine AdminsOk.rebuild (us := us) (ps := t₁ ++ bts) (rs := t₂)
      (by simpa [List.append_assoc] using hp1) hr ?_
    refine (AdminsOk.single (.plain (InstrOk.br (t₁ := t₁) (t₂ := t₂) hlbl))).sub ?_
    exact ⟨CResultType.sub_append (CResultType.sub_refl t₁) hsub, CResultType.sub_refl t₂⟩

/-! ## Function instructions (`8-reduction:117-145`), the pure rules -/

/-- `Step_pure/frame-vals` (`8-reduction:138`). -/
theorem pres_frameVals {s : Store H} {C : Context} {n : Nat} {fr : Frame} {vs : List Val}
    {it : InstrType} (h : AdminsOk s C [.frame n fr (vals vs)] it) :
    AdminsOk s C (vals vs) it := by
  obtain ⟨us, it₀, ha, hp, hr⟩ := AdminsOk.single_inv' h
  obtain ⟨C', ts, -, -, rfl, hb⟩ := ha.frame_inv
  refine AdminsOk.rebuild (ps := []) hp hr ?_
  obtain ⟨vts, hvs, hsub⟩ := AdminsOk.vals_inv hb
  exact (AdminsOk.of_vals hvs).sub ⟨CResultType.sub_refl [], by simpa using hsub⟩

/-- `Step_pure/return-frame` (`8-reduction:141`). -/
theorem pres_returnFrame {s : Store H} {C : Context} {n : Nat} {fr : Frame}
    {vs' vs : List Val} {rest : List Admin} {it : InstrType} (hvn : vs.length = n)
    (h : AdminsOk s C [.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)] it) :
    AdminsOk s C (vals vs) it := by
  obtain ⟨us, it₀, ha, hp, hr⟩ := AdminsOk.single_inv' h
  obtain ⟨C', ts, -, hn, rfl, hb⟩ := ha.frame_inv
  refine AdminsOk.rebuild (ps := []) hp hr ?_
  obtain ⟨m₁, h1, -⟩ := AdminsOk.append_inv hb
  obtain ⟨m₂, h2, h3⟩ := AdminsOk.append_inv h1
  obtain ⟨m₃, -, h4⟩ := AdminsOk.append_inv h2
  obtain ⟨vts, hvs, hsub⟩ := AdminsOk.vals_inv h4
  obtain ⟨us', it₁, ha', hp', -⟩ := AdminsOk.single_inv' h3
  cases ha'.plain_inv with
  | @return_ _ rts a b hret =>
    simp only [Option.some.injEq] at hret
    rw [← hret] at hp'
    have hcomb : CResultType.Sub (m₃ ++ liftResult vts) ((us' ++ a) ++ ts) := by
      rw [List.append_assoc]
      exact CResultType.sub_trans hsub hp'
    obtain ⟨-, h2'⟩ := sub_split_right (by simp [← hvs.length_eq, hvn, hn]) hcomb
    obtain rfl : ts = liftResult vts := CResultType.sub_liftResult_iff.mp h2'
    exact AdminsOk.of_vals hvs

/-- `Step_pure/return-label` (`8-reduction:144`): the `RETURN` bubbles out of the
label, carrying the stack above it. -/
theorem pres_returnLabel {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {vs : List Val} {rest : List Admin} {it : InstrType}
    (h : AdminsOk s C [.label n cont (vals vs ++ [.plain .return_] ++ rest)] it) :
    AdminsOk s C (vals vs ++ [.plain .return_]) it := by
  obtain ⟨us, it₀, ha, hp, hr⟩ := AdminsOk.single_inv' h
  obtain ⟨t', ts, -, rfl, -, hb⟩ := ha.label_inv
  refine AdminsOk.rebuild (ps := []) hp hr ?_
  obtain ⟨m₁, h1, -⟩ := AdminsOk.append_inv hb
  obtain ⟨m₂, h2, h3⟩ := AdminsOk.append_inv h1
  obtain ⟨vts, hvs, hsub⟩ := AdminsOk.vals_inv h2
  obtain ⟨us', it₁, ha', hp', -⟩ := AdminsOk.single_inv' h3
  cases ha'.plain_inv with
  | @return_ _ rts a b hret =>
    have hret' : C.return_ = some rts := by simpa [Context.withLabel] using hret
    have hcomb : CResultType.Sub (liftResult vts) ((us' ++ a) ++ rts) := by
      rw [List.append_assoc]
      exact CResultType.sub_trans (by simpa using hsub) hp'
    obtain ⟨A, B, hAB, -, hBl⟩ := sub_append_right_inv hcomb
    have hret2 : AdminsOk s C [.plain .return_] ⟨A ++ B, ts⟩ := by
      refine (AdminsOk.single (.plain (InstrOk.return_ (t₁ := A) (t₂ := ts) hret'))).sub ?_
      exact ⟨CResultType.sub_append (CResultType.sub_refl A) hBl, CResultType.sub_refl ts⟩
    have hv : AdminsOk s C (vals vs) ⟨[], A ++ B⟩ := by
      rw [← hAB]; exact AdminsOk.of_vals hvs
    exact hv.append hret2

/-! ## Local instructions, the pure rule (`8-reduction:383`) -/

/-- `Step_pure/local.tee` (`8-reduction:383`). -/
theorem pres_localTee {s : Store H} {C : Context} {v : Val} {x : LocalIdx} {it : InstrType}
    (h : AdminsOk s C [v.toAdmin, .plain (.localTee x)] it) :
    AdminsOk s C [v.toAdmin, v.toAdmin, .plain (.localSet x)] it := by
  refine AdminsOk.flat1 (fun _ hi => by cases hi; rfl) (fun t it₀ hv hi hps => ?_) h
  cases hi with
  | @localTee _ _ t' hx =>
    obtain rfl : t' = t := by simpa using hps
    have h1 : AdminsOk s C [v.toAdmin] ⟨[], [CValType.val t']⟩ :=
      .single (AdminOk.toAdmin_ok hv)
    have h2 : AdminsOk s C [v.toAdmin] ⟨[CValType.val t'], [.val t', .val t']⟩ := by
      simpa using AdminsOk.frame (ts := [CValType.val t']) h1
    have h3 : AdminsOk s C [.plain (.localSet x)] ⟨[CValType.val t', .val t'], [.val t']⟩ := by
      simpa using AdminsOk.frame (s := s) (ts := [CValType.val t'])
        (AdminsOk.single (.plain (InstrOk.localSet hx)))
    exact (h1.append h2).append h3

/-! ## Flat redexes whose operands are given as administrative instructions

The reduction rules write their operands as `(CONST nt c)` or `(VCONST c)`
rather than as `val.toAdmin`, so these variants take the operands as `Admin`s
with an `isVal` side condition, which is `rfl` or `simp` at every use site. -/

/-- An arity-one flat redex whose reduct is a single *constant* instruction. -/
theorem AdminsOk.flat1_const {s : Store H} {C : Context} {a : Admin} {i j : Instr}
    {it : InstrType} (h : AdminsOk s C [a, .plain i] it) (hv : a.isVal)
    (harity : ∀ it₀, InstrOk C i it₀ → it₀.params.length = 1)
    (hj : ∀ it₀, InstrOk C i it₀ → InstrOk C j ⟨[], it₀.results⟩) :
    AdminsOk s C [.plain j] it := by
  obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
  obtain rfl := Admin.toAdmin_of_val? hv'
  exact AdminsOk.flat1 harity (fun _ it₀ _ hi _ => .single (.plain (hj it₀ hi))) h

/-- An arity-two flat redex whose reduct is a single *constant* instruction. -/
theorem AdminsOk.flat2_const {s : Store H} {C : Context} {a₁ a₂ : Admin} {i j : Instr}
    {it : InstrType} (h : AdminsOk s C [a₁, a₂, .plain i] it)
    (hv₁ : a₁.isVal) (hv₂ : a₂.isVal)
    (harity : ∀ it₀, InstrOk C i it₀ → it₀.params.length = 2)
    (hj : ∀ it₀, InstrOk C i it₀ → InstrOk C j ⟨[], it₀.results⟩) :
    AdminsOk s C [.plain j] it := by
  obtain ⟨v₁, hv₁'⟩ := Option.isSome_iff_exists.mp hv₁
  obtain ⟨v₂, hv₂'⟩ := Option.isSome_iff_exists.mp hv₂
  obtain rfl := Admin.toAdmin_of_val? hv₁'
  obtain rfl := Admin.toAdmin_of_val? hv₂'
  exact AdminsOk.flat2 harity (fun _ _ it₀ _ _ hi _ => .single (.plain (hj it₀ hi))) h

/-- An arity-three flat redex whose reduct is a single *constant* instruction. -/
theorem AdminsOk.flat3_const {s : Store H} {C : Context} {a₁ a₂ a₃ : Admin} {i j : Instr}
    {it : InstrType} (h : AdminsOk s C [a₁, a₂, a₃, .plain i] it)
    (hv₁ : a₁.isVal) (hv₂ : a₂.isVal) (hv₃ : a₃.isVal)
    (harity : ∀ it₀, InstrOk C i it₀ → it₀.params.length = 3)
    (hj : ∀ it₀, InstrOk C i it₀ → InstrOk C j ⟨[], it₀.results⟩) :
    AdminsOk s C [.plain j] it := by
  obtain ⟨v₁, hv₁'⟩ := Option.isSome_iff_exists.mp hv₁
  obtain ⟨v₂, hv₂'⟩ := Option.isSome_iff_exists.mp hv₂
  obtain ⟨v₃, hv₃'⟩ := Option.isSome_iff_exists.mp hv₃
  obtain rfl := Admin.toAdmin_of_val? hv₁'
  obtain rfl := Admin.toAdmin_of_val? hv₂'
  obtain rfl := Admin.toAdmin_of_val? hv₃'
  exact AdminsOk.flat3 harity (fun _ _ _ it₀ _ _ _ hi _ => .single (.plain (hj it₀ hi))) h

/-- An arity-one flat redex whose reduct is a runtime *value* of the
instruction's (single) result type. -/
theorem AdminsOk.flat1_val {s : Store H} {C : Context} {a : Admin} {w : Val} {i : Instr}
    {it : InstrType} (h : AdminsOk s C [a, .plain i] it) (hv : a.isVal)
    (harity : ∀ it₀, InstrOk C i it₀ → it₀.params.length = 1)
    (hw : ∀ it₀, InstrOk C i it₀ → ∃ t : ValType, it₀.results = [.val t] ∧ ValOk s w t) :
    AdminsOk s C [w.toAdmin] it := by
  obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
  obtain rfl := Admin.toAdmin_of_val? hv'
  refine AdminsOk.flat1 harity (fun _ it₀ _ hi _ => ?_) h
  obtain ⟨t, hres, hval⟩ := hw it₀ hi
  rw [hres]
  exact .single (AdminOk.toAdmin_ok hval)

/-- A list index that resolves names a member. -/
theorem getElem?_mem {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) : x ∈ l := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.getElem_mem hi

/-! ## Preservation for `Step_pure` (`8-reduction:6`)

Every family of `Step_pure` at once: the *parametric* rules
(`8-reduction:40-58`), the *block* and *branch* rules (`:61-114`), the pure
*function* rules (`:138-145`), the *trap* rules (`:148-158`), the *numeric*
rules (`:172-207`), the *reference* rules (`:210-222`), the *vector* rules
(`:225-372`) and the pure *local* rule (`:383`).

`Step_pure` reads neither the store nor the frame, so neither `StoreOk` nor
`FrameOk` is needed: this is a statement about typing alone. -/

theorem PureStep.preservation {P : Profile} {s : Store H} {C : Context}
    {is is' : List Admin} {it : InstrType} (hty : AdminsOk s C is it)
    (h : PureStep P is is') : AdminsOk s C is' it := by
  cases h with
  | brTableLt hi => exact pres_brTable (fun _ hls _ => hls _ (getElem?_mem hi)) hty
  | brTableGe _ => exact pres_brTable (fun _ _ hl' => hl') hty
  | brZero hl hn => exact pres_brZero hl hn hty
  | brSucc hl => exact pres_brSucc hl hty
  | returnFrame hn => exact pres_returnFrame hn hty
  | ifTrue _ => exact pres_if (.inl rfl) hty
  | ifFalse => exact pres_if (.inr rfl) hty
  | _ =>
    first
    | exact AdminsOk.trap_it _
    | exact pres_nop hty
    | exact pres_drop hty
    | exact pres_selectTrue hty
    | exact pres_selectFalse hty
    | exact pres_labelVals hty
    | exact pres_brIfTrue hty
    | exact pres_brIfFalse hty
    | exact pres_frameVals hty
    | exact pres_returnLabel hty
    | exact pres_localTee hty
    | exact AdminsOk.flat1_const hty (by first | rfl | simp)
        (fun _ hi => by cases hi <;> rfl)
        (fun _ hi => by
          cases hi <;> first | exact .intConst | exact .floatConst | exact .vecConst)
    | exact AdminsOk.flat2_const hty (by rfl) (by first | rfl | simp)
        (fun _ hi => by cases hi; rfl)
        (fun _ hi => by
          cases hi; first | exact .intConst | exact .floatConst | exact .vecConst)
    | exact AdminsOk.flat3_const hty (by rfl) (by rfl)
        (by rfl) (fun _ hi => by cases hi; rfl)
        (fun _ hi => by
          cases hi; exact .vecConst)
    | exact AdminsOk.flat1_val hty (by first | rfl | simp)
        (fun _ hi => by cases hi <;> rfl)
        (fun _ hi => by cases hi <;> exact ⟨_, rfl, .num _⟩)

end Silmaril.Wasm.V2.Execution
