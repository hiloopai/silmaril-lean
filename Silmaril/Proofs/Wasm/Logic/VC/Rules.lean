module

public import Silmaril.Wasm.Logic.VC.Defs
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Logic.Instr.Thms

/-!
# The verification-condition generator: the rules behind each case

Each case of `Silmaril.Wasm.Logic.VC.wpc` as a rule of the every-run logic `HWP`, with the
continuation after the construct given by a predicate `K` that implies `HWP` of the rest
(`hK`): `hwp_block` (`HWP.block`), `hwp_loop` (`HWP.seq` and `HWP.loop` with the invariant
strengthened by "same module instance, right number of parameters"), the inversion lemmas
for `ctl`, `popI32` and `popSelect`; `wp_brTable` (`Wp.brTable_lt`/`_ge`, either reading),
`wp_cvt` (`Wp.convert`: the integer conversions have one result and no trap in every profile)
and **`hwp_call`** (`Safe.callIdx`: a call of a function whose specification is in a valid
spec context).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.VC

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP Wp labelPost seqPost loopPost)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Inversions -/

theorem ctl_block {i : Instr} {bt : BlockType} {b : List Instr} (h : ctl i = .block bt b) :
    i = .block bt b := by
  cases i <;> simp only [ctl, reduceCtorEq, Ctl.block.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem ctl_loop {i : Instr} {bt : BlockType} {b : List Instr} (h : ctl i = .loop bt b) :
    i = .loop bt b := by
  cases i <;> simp only [ctl, reduceCtorEq, Ctl.loop.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem ctl_if {i : Instr} {bt : BlockType} {b₁ b₂ : List Instr} (h : ctl i = .if_ bt b₁ b₂) :
    i = .if_ bt b₁ b₂ := by
  cases i <;> simp only [ctl, reduceCtorEq, Ctl.if_.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem ctl_br {i : Instr} {l : LabelIdx} (h : ctl i = .br l) : i = .br l := by
  cases i <;> simp only [ctl, reduceCtorEq, Ctl.br.injEq] at h
  rw [h]

theorem ctl_brIf {i : Instr} {l : LabelIdx} (h : ctl i = .brIf l) : i = .brIf l := by
  cases i <;> simp only [ctl, reduceCtorEq, Ctl.brIf.injEq] at h
  rw [h]

theorem ctl_select {i : Instr} (h : ctl i = .select) : ∃ ts, i = .select ts := by
  cases i <;> simp only [ctl, reduceCtorEq] at h
  exact ⟨_, rfl⟩

theorem ctl_ret {i : Instr} (h : ctl i = .ret) : i = .return_ := by
  cases i <;> simp only [ctl, reduceCtorEq] at h
  rfl

theorem ctl_brTable {i : Instr} {ls : List LabelIdx} {d : LabelIdx} (h : ctl i = .brTable ls d) :
    i = .brTable ls d := by
  cases i <;> simp only [ctl, reduceCtorEq, Ctl.brTable.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem ctl_call {i : Instr} {x : FuncIdx} (h : ctl i = .call x) : i = .call x := by
  cases i <;> simp only [ctl, reduceCtorEq, Ctl.call.injEq] at h
  rw [h]

theorem ctl_cvt {i : Instr} {op : ConvertOp} (h : ctl i = .cvt op) : i = .convert op := by
  cases i <;> simp only [ctl, reduceCtorEq, Ctl.cvt.injEq] at h
  rw [h]

theorem ctl_trap {i : Instr} (h : ctl i = .trap) : i = .unreachable := by
  cases i <;> simp only [ctl, reduceCtorEq] at h
  rfl

theorem popI32_eq {vs us : List Val} {c : BitVec 32} (h : popI32 vs = some (us, c)) :
    vs = us ++ [Val.i32 c] := by
  unfold popI32 at h
  split at h
  next c' rus hr =>
    simp only [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [← List.reverse_reverse vs, hr]
    simp [Val.i32]
  next => cases h

theorem popSelect_eq {vs us : List Val} {v₁ v₂ : Val} {c : BitVec 32}
    (h : popSelect vs = some (us, v₁, v₂, c)) : vs = us ++ [v₁, v₂, Val.i32 c] := by
  unfold popSelect at h
  split at h
  next c' w₂ w₁ rus hr =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rw [← List.reverse_reverse vs, hr]
    simp [Val.i32]
  next => cases h

/-! ## Entering a block or loop -/

theorem enterVC.mono {f : Frame} {bt : BlockType} {vs : List Val}
    {B B' : List Val → List Val → Nat → Nat → Prop}
    (hB : ∀ us args n₁ n₂, B us args n₁ n₂ → B' us args n₁ n₂) (h : enterVC f bt vs B) :
    enterVC f bt vs B' := by
  unfold enterVC at h ⊢
  split at h
  next => exact ⟨h.1, hB _ _ _ _ h.2⟩
  next => exact h.elim

/-- The outcome of a block body, from `labelQ` to `labelPost`. -/
theorem labelQ_post {n : Nat} {us : List Val} {K : Store H → Frame → List Val → Prop}
    {Q : Post H} {rest : List Admin}
    (hK : ∀ s f vs, K s f vs → HWP P host s f (vals vs ++ rest) Q) {s : Store H} {f : Frame}
    {o : Outcome} (h : labelQ n us K Q s f o) :
    labelPost P host n [] us (seqPost P host rest Q) s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  · exact hK s f _ h
  · obtain ⟨hn, hk⟩ := h
    refine ⟨vs.take (vs.length - n), vs.drop (vs.length - n), (List.take_append_drop _ _).symm,
      by simp only [List.length_drop]; omega, ?_⟩
    have hv := HWP.of_vals (P := P) (host := host) (s := s) (f := f)
      (vs := us ++ vs.drop (vs.length - n)) (Q := seqPost P host rest Q) (hK s f _ hk)
    simpa [expression, vals] using hv
  all_goals exact h

/-- **The `block` case.** -/
theorem hwp_block {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType} {b : List Instr}
    {rest : List Admin} {Q : Post H} {K : Store H → Frame → List Val → Prop}
    (hK : ∀ s f vs, K s f vs → HWP P host s f (vals vs ++ rest) Q)
    (h : enterVC f bt vs fun us args _ n₂ =>
      HWP P host s f (vals args ++ expression b) (labelQ n₂ us K Q)) :
    HWP P host s f (vals vs ++ .plain (.block bt b) :: rest) Q := by
  unfold enterVC at h
  split at h
  next t₁ t₂ hbt =>
    obtain ⟨hle, hb⟩ := h
    have hvs : vs = vs.take (vs.length - t₁.length) ++ vs.drop (vs.length - t₁.length) :=
      (List.take_append_drop _ _).symm
    rw [hvs]
    exact HWP.block hbt (by simp only [List.length_drop]; omega)
      (hb.mono fun _ _ _ hq => labelQ_post hK hq)
  next => exact h.elim

/-- The outcome of a loop body, from `loopQ` to `loopPost` (with the invariant strengthened by
the module instance and the number of parameters). -/
theorem loopQ_post {n : Nat} {us : List Val} {I : Store H → Frame → List Val → Prop}
    {mi : ModuleInst} {K : Store H → Frame → List Val → Prop} {Q : Post H} {rest : List Admin}
    (hK : ∀ s f vs, K s f vs → HWP P host s f (vals vs ++ rest) Q) {s : Store H} {f : Frame}
    {o : Outcome}
    (h : loopQ n us (fun s f a => I s f a ∧ f.module = mi) K Q s f o) :
    loopPost n us (fun s f a => I s f a ∧ f.module = mi ∧ a.length = n) (seqPost P host rest Q)
      s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  · exact hK s f _ h
  · obtain ⟨hn, hi, hm⟩ := h
    exact ⟨vs.take (vs.length - n), vs.drop (vs.length - n), (List.take_append_drop _ _).symm,
      by simp only [List.length_drop]; omega, hi, hm, by simp only [List.length_drop]; omega⟩
  all_goals exact h

/-- **The `loop` case.** -/
theorem hwp_loop {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType} {b : List Instr}
    {rest : List Admin} {Q : Post H} {K : Store H → Frame → List Val → Prop}
    {I : Store H → Frame → List Val → Prop}
    (hK : ∀ s f vs, K s f vs → HWP P host s f (vals vs ++ rest) Q)
    (h : enterVC f bt vs fun us args n₁ _ => I s f args ∧
      ∀ s' f' a', I s' f' a' → f'.module = f.module → a'.length = n₁ →
        HWP P host s' f' (vals a' ++ expression b)
          (loopQ n₁ us (fun s'' f'' a'' => I s'' f'' a'' ∧ f''.module = f.module) K Q)) :
    HWP P host s f (vals vs ++ .plain (.loop bt b) :: rest) Q := by
  unfold enterVC at h
  split at h
  next t₁ t₂ hbt =>
    show HWP P host s f (vals vs ++ .plain (.loop bt b) :: rest) Q
    obtain ⟨hle, hi, hb⟩ := h
    have hvs : vs = vs.take (vs.length - t₁.length) ++ vs.drop (vs.length - t₁.length) :=
      (List.take_append_drop _ _).symm
    have hcode : vals vs ++ Admin.plain (.loop bt b) :: rest =
        (vals (vs.take (vs.length - t₁.length) ++ vs.drop (vs.length - t₁.length)) ++
          [Admin.plain (.loop bt b)]) ++ rest := by
      rw [← hvs, List.append_assoc, List.singleton_append]
    rw [hcode]
    refine HWP.seq (HWP.loop (Inv := fun s' f' a => I s' f' a ∧ f'.module = f.module ∧
      a.length = t₁.length) (t₁ := t₁) (t₂ := t₂) ?_ ?_ ?_ ⟨hi, rfl, ?_⟩)
    · intro _ f' _ hinv
      rw [hinv.2.1]
      exact hbt
    · exact fun _ _ _ hinv => hinv.2.2
    · intro s' f' a' hinv
      exact (hb s' f' a' hinv.1 hinv.2.1 hinv.2.2).mono fun _ _ _ hq => loopQ_post hK hq
    · simp only [List.length_drop]
      omega
  next => exact h.elim

/-! ## `br_table` -/

theorem tableVC_spec {K : LabelIdx → Prop} {c : Nat} :
    ∀ {j : Nat} {ls : List LabelIdx} {d : LabelIdx}, tableVC K c j ls d →
      (∀ i l, ls[i]? = some l → c = j + i → K l) ∧ (j + ls.length ≤ c → K d)
  | j, [], d, h => ⟨fun _ _ hl => by simp at hl, fun hc => h (by simpa using hc)⟩
  | j, l :: ls, d, h => by
    obtain ⟨h₀, h₁⟩ := h
    obtain ⟨ih₁, ih₂⟩ := tableVC_spec h₁
    refine ⟨fun i l' hl hc => ?_, fun hc => ih₂ (by simp at hc; omega)⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
      exact hl ▸ h₀ (by omega)
    | succ i =>
      simp only [List.getElem?_cons_succ] at hl
      exact ih₁ i l' hl (by omega)

section Wp

variable {m : Silmaril.Wasm.Logic.Hoare.Corr} {s : Store H} {f : Frame} {rest : List Admin}
  {Q : Post H}

/-- **The `br_table` case**, in either reading. -/
theorem wp_brTable {us : List Val} {c : BitVec 32} {ls : List LabelIdx} {d : LabelIdx}
    (h : tableVC (fun l => Q s f (.br l.toNat us)) c.toNat 0 ls d) :
    Wp m P host s f (vals (us ++ [Val.i32 c]) ++ .plain (.brTable ls d) :: rest) Q := by
  obtain ⟨h₁, h₂⟩ := tableVC_spec h
  by_cases hlt : c.toNat < ls.length
  · have hi : ls[c.toNat]? = some ls[c.toNat] := List.getElem?_eq_getElem hlt
    exact Silmaril.Wasm.Logic.Hoare.Wp.brTable_lt hi
      (Silmaril.Wasm.Logic.Hoare.Wp.br (h₁ _ _ hi (by omega)))
  · exact Silmaril.Wasm.Logic.Hoare.Wp.brTable_ge (by omega)
      (Silmaril.Wasm.Logic.Hoare.Wp.br (h₂ (by omega)))

/-! ## Integer conversions -/

theorem convertP_wrap {x : BitVec 64} {r : Except FloatTrap (BitVec 32)}
    (h : convertP P .wrap x r) : r = .ok (x.setWidth 32) := by
  unfold convertP at h
  split at h <;> simp only [convertRel, convert] at h <;> exact h

theorem convertP_extendU {x : BitVec 32} {r : Except FloatTrap (BitVec 64)}
    (h : convertP P (.extend .unsigned) x r) : r = .ok (x.setWidth 64) := by
  unfold convertP at h
  split at h <;> simp only [convertRel, convert] at h <;> exact h

theorem convertP_extendS {x : BitVec 32} {r : Except FloatTrap (BitVec 64)}
    (h : convertP P (.extend .signed) x r) : r = .ok (x.signExtend 64) := by
  unfold convertP at h
  split at h <;> simp only [convertRel, convert] at h <;> exact h

theorem cvt1_vs {vs rus : List Val} {v : Val} (h : vs.reverse = v :: rus) :
    vs = rus.reverse ++ [v] := by
  rw [← List.reverse_reverse vs, h]
  simp

/-- A conversion with a single possible result `y`: the continuation at `y` suffices. -/
private theorem wp_convert_det {op : ConvertOp} {x : BitVec op.source.width}
    {y : BitVec op.target.width} {us : List Val}
    (hdet : ∀ r, convertP P op x r → r = .ok y)
    (hk : Wp m P host s f (vals (us ++ [.num ⟨op.target, y⟩]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.num ⟨op.source, x⟩]) ++ .plain (.convert op) :: rest) Q :=
  Silmaril.Wasm.Logic.Hoare.Wp.convert (fun z hz => by rw [Except.ok.inj (hdet _ hz)]; exact hk)
    (fun e he => by simpa using hdet _ he)

/-- **The conversion case**, in either reading: the result `cvt1` computes is the only one, in
every profile. -/
theorem wp_cvt {op : ConvertOp} {vs vs' : List Val} (h : cvt1 op vs = some vs')
    (hk : Wp m P host s f (vals vs' ++ rest) Q) :
    Wp m P host s f (vals vs ++ .plain (.convert op) :: rest) Q := by
  unfold cvt1 at h
  split at h
  next x rus hr =>
    have hv : rus.reverse ++ [.num ⟨.int .i32, x.setWidth 32⟩] = vs' := Option.some.inj h
    rw [cvt1_vs hr]
    exact wp_convert_det (op := .wrap) (fun _ => convertP_wrap) (by exact hv ▸ hk)
  next x rus hr =>
    have hv : rus.reverse ++ [.num ⟨.int .i64, x.setWidth 64⟩] = vs' := Option.some.inj h
    rw [cvt1_vs hr]
    exact wp_convert_det (op := .extend .unsigned) (fun _ => convertP_extendU) (by exact hv ▸ hk)
  next x rus hr =>
    have hv : rus.reverse ++ [.num ⟨.int .i64, x.signExtend 64⟩] = vs' := Option.some.inj h
    rw [cvt1_vs hr]
    exact wp_convert_det (op := .extend .signed) (fun _ => convertP_extendS) (by exact hv ▸ hk)
  next => cases h

end Wp

/-! ## Calls -/

/-- The `call` case once the callee `a` and its specification `(n, S)` are resolved. -/
private theorem hwp_call_of {Γ : VCSpecs H} (hΓ : Γ.Valid P host) {s : Store H} {f : Frame}
    {vs : List Val} {x : FuncIdx} {rest : List Admin} {Q : Post H}
    {K : Store H → List Val → Prop} {a n : Nat} {S : Silmaril.Wasm.Logic.Hoare.FSpec H}
    (hK : ∀ s' vs', K s' vs' → HWP P host s' f (vals vs' ++ rest) Q)
    (hx : f.module.funcs[x.toNat]? = some a) (hS : Γ.specs a = some (n, S))
    (h : n ≤ vs.length ∧ S.pre s (vs.drop (vs.length - n)) ∧
      ∀ s' o, S.post s (vs.drop (vs.length - n)) s' o →
        callK f (vs.take (vs.length - n)) K Q s' o) :
    HWP P host s f (vals vs ++ .plain (.call x) :: rest) Q := by
  obtain ⟨-, hpre, hpost⟩ := h
  obtain ⟨fi, hf⟩ := Option.isSome_iff_exists.mp ((hΓ a n S hS).2 _ _ hpre)
  have hvs : vs = vs.take (vs.length - n) ++ vs.drop (vs.length - n) :=
    (List.take_append_drop _ _).symm
  intro N
  cases N with
  | zero => trivial
  | succ N =>
    rw [hvs]
    refine Silmaril.Wasm.Logic.Hoare.Safe.callIdx hx hf ((hΓ a n S hS).1 N) hpre ?_
    rintro s' o ⟨-, ⟨res, rfl, hR⟩ | ⟨rfl, hR⟩ | ⟨b, rfl, hR⟩⟩
    · exact hK s' _ (hpost s' _ hR) N
    · exact hpost s' _ hR
    · exact hpost s' _ hR

/-- **The `call` case**: a call of a function whose specification is in a valid spec context,
with the continuation `K` implying `HWP` of the rest. -/
theorem hwp_call {Γ : VCSpecs H} (hΓ : Γ.Valid P host) {s : Store H} {f : Frame}
    {vs : List Val} {x : FuncIdx} {rest : List Admin} {Q : Post H}
    {K : Store H → List Val → Prop}
    (hK : ∀ s' vs', K s' vs' → HWP P host s' f (vals vs' ++ rest) Q)
    (h : callVC s f vs x K Q) :
    HWP P host s f (vals vs ++ .plain (.call x) :: rest) Q := by
  unfold callVC at h
  split at h
  next a hx =>
    split at h
    next n S hS => exact hwp_call_of hΓ hK hx hS h
    next => exact h.elim
  next => exact h.elim

end Silmaril.Wasm.Logic.VC
