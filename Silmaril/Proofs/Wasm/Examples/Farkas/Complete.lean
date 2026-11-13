module

public import Silmaril.Proofs.Wasm.Examples.Farkas.Tests

@[expose] public section

/-!
# The Farkas checker: completeness over sessions (partial correctness)

The flag `bad` stays `0` exactly while every `row`/`entry` passes the bounds (`CmdOk`):
`bad_rowM`, `bad_entryM` (with the exact representation `Exact`, and `hr ≠ 0 ↔ rs ≠ []`).
`RepC (rs, ok) s`: the store holds a machine state with the invariant for `rs`, `hr` records
whether a row was started, and `ok` (every command since the last `check` passed the bounds)
implies `bad = 0`. `farkas_specC`: every export call meets `callSpec farkasI RepC okNext GoodC`,
where `GoodC` says that a `check` after in-bounds commands loading a valid certificate answers
`1` (`check_complete`). `farkas_complete`: in every session, such a `check` answers `1`.
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Logic.Hoare (FSpecValid)
open Silmaril.Wasm.Spec.Multi (Call Session)
open Silmaril.Wasm.Examples.Common (callSpec outcomeResult? FSpecValid.of_body_hwp session_allGood
  allGood_append after)
open Silmaril.Logic.LinArith (WRows Cmd)

/-! ## The flag under the bounds -/

/-- **A `row` within the bounds keeps the flag clear.** -/
theorem bad_rowM {m : Mach} {rs : WRows} {y b : BitVec 64} (hE : Exact m rs) (hb : m.bad = 0)
    (hok : CmdOk rs (.row y.toInt b.toInt)) : (rowM m y b).bad = 0 := by
  obtain ⟨hy, hbd, ht⟩ := hok
  have hv : -aB ≤ m.vb.toInt ∧ m.vb.toInt ≤ aB := hE.accB ▸ hE.accB_le
  have hy' : -cB ≤ y.toInt ∧ y.toInt ≤ cB := ⟨by simp only [cB] at hy ⊢; omega, hy.2⟩
  have hsum : (m.vb + y * b).toInt = WRows.combB ((Cmd.row y.toInt b.toInt).apply rs) := by
    rw [macc_toInt hv hy' hbd, hE.accB, Cmd.combB_row]
    ring
  simp only [rowM, or_eq_zero]
  refine ⟨⟨⟨⟨⟨⟨hb, (ltS_eq_zero ?_ ?_).2 hy.1⟩, (gtS_eq_zero ?_ ?_).2 hy.2⟩,
    (ltS_eq_zero ?_ ?_).2 hbd.1⟩, (gtS_eq_zero ?_ ?_).2 hbd.2⟩, (ltS_eq_zero ?_ ?_).2 (hsum ▸ ht.1)⟩,
    (gtS_eq_zero ?_ ?_).2 (hsum ▸ ht.2)⟩ <;> norm_num [cB, aB]

/-- **An `entry` within the bounds keeps the flag clear.** -/
theorem bad_entryM {m : Mach} {rs : WRows} {j : BitVec 32} {a : BitVec 64} (hI : Inv m rs)
    (hb : m.bad = 0) (hhr : m.hr ≠ 0 ↔ rs ≠ []) (hok : CmdOk rs (.entry j.toNat a.toInt)) :
    (entryM m j a).bad = 0 := by
  obtain ⟨hne, hj, ha, ht⟩ := hok
  have hE : Exact m rs := hI.2 hb
  have hhr' : m.hr ≠ 0 := hhr.2 hne
  obtain ⟨r, rs', hrs⟩ := hE.cur hhr'
  subst hrs
  have hmod : j.toNat % nVars = j.toNat := Nat.mod_eq_of_lt hj
  have hy₀ := hE.mults _ List.mem_cons_self
  have hy : -cB ≤ m.y.toInt ∧ m.y.toInt ≤ cB := ⟨by simp only [cB] at hy₀ ⊢; omega, hy₀.2⟩
  have hacc := entry_acc hI.1 hE hj hy ha j.toNat hj
  rw [slot_setSlot_same hI.1 hj] at hacc
  simp only [entryM, or_eq_zero, hmod]
  refine ⟨⟨⟨⟨⟨⟨hb, eqz_eq_zero.2 hhr'⟩, geU_eq_zero.2 hj⟩, (ltS_eq_zero ?_ ?_).2 ha.1⟩,
    (gtS_eq_zero ?_ ?_).2 ha.2⟩, (ltS_eq_zero ?_ ?_).2 (hacc ▸ ht.1)⟩,
    (gtS_eq_zero ?_ ?_).2 (hacc ▸ ht.2)⟩ <;> norm_num [cB, aB]

theorem apply_entry_ne_nil {rs : WRows} {j : Nat} {a : Int} :
    (Cmd.entry j a).apply rs ≠ [] ↔ rs ≠ [] := by
  rcases rs with _ | ⟨⟨y, r⟩, rs⟩
  · exact Iff.rfl
  · exact ⟨fun _ => List.cons_ne_nil _ _, fun _ => List.cons_ne_nil _ _⟩

/-! ## The representation for completeness -/

/-- The store holds a machine state with the invariant for the rows, `hr` records whether a row
was started, and `ok` implies that no check failed. -/
def RepC (a : WRows × Prop) (s : Store Nat) : Prop :=
  ∃ m, Holds s m ∧ Inv m a.1 ∧ (m.hr ≠ 0 ↔ a.1 ≠ []) ∧ (a.2 → m.bad = 0)

/-- **Completeness of a call**: a `check` after in-bounds commands loading a valid certificate
answers `1`. -/
def GoodC {I : ScalarInstance} (a : WRows × Prop) (c : Call I) : Prop :=
  c.1.1.val = 2 → a.2 → a.1.IsCert →
    Answer.toResult (ft := I.exports.get c.1.1) c.2 = .values [Val.i32 1]

theorem repC_unique {s₀ : Store Nat} {m : Mach} (hs₀ : s₀.funcs = farkasStore.funcs)
    {a : WRows × Prop} (h : RepC a (withMach s₀ m)) :
    Inv m a.1 ∧ (m.hr ≠ 0 ↔ a.1 ≠ []) ∧ (a.2 → m.bad = 0) := by
  obtain ⟨m', hH, hI⟩ := h
  have he : m' = m := Holds.unique hH (holds_withMach hs₀ m)
  exact he ▸ hI

theorem pre_funcsC {f : farkasI.F.Op} {s : Store Nat} {args : List Val}
    (h : (callSpec farkasI RepC okNext GoodC f).pre s args) : s.funcs = farkasStore.funcs := by
  obtain ⟨-, _, m, hH, -⟩ := h
  exact hH.funcs

theorem pre_lenC {f : farkasI.F.Op} {s : Store Nat} {args : List Val}
    (h : (callSpec farkasI RepC okNext GoodC f).pre s args) :
    args.length = (Ty.ofList ((farkasExports.get f.1).params.map ScalarType.toC)).length := by
  rw [h.1, Ty.length_ofList, List.length_map]
  exact f.2.2.length_eq.symm

variable {P : Profile} {host : HostSemantics Nat}

/-- **`row` meets its completeness specification.** -/
theorem specC_row (args : Typed (farkasExports.get ⟨0, by decide⟩).params) :
    FSpecValid P host (farkasI.addr ⟨0, by decide⟩)
      (callSpec farkasI RepC okNext GoodC ⟨⟨0, by decide⟩, args⟩) := by
  obtain ⟨fi₀, fi₁, fi₂, hfs, hm₀, -, -, hc₀, -, -, ht₀, -, -⟩ := farkasStore_funcs
  obtain ⟨y, b, hargs⟩ := typed_row args.2
  refine FSpecValid.of_body_hwp (fi := fi₀) (code := ⟨⟨0⟩, [.i64], rowBody⟩)
    (fun s _ h => by rw [pre_funcsC h, hfs]; rfl) hc₀ (FnType.expand_of_ofDefType? ht₀)
    (fun _ _ h => pre_lenC h) (fun s args' hpre => ?_)
  obtain ⟨rfl, rs, m, ⟨s₀, hs₀, rfl⟩, -⟩ := hpre
  rw [hm₀, hargs]
  refine row_hwp y b fun f' => ⟨rfl, fun a' ha' r _ w _ =>
    ⟨fun h => absurd (h : (0 : Nat) = 2) (by decide : ¬ (0 : Nat) = 2), ?_⟩⟩
  have hn : okNext a' (I := farkasI) ⟨⟨⟨0, by decide⟩, args⟩, w⟩ =
      ((Cmd.row y.toInt b.toInt).apply a'.1, a'.2 ∧ CmdOk a'.1 (.row y.toInt b.toInt)) := by
    simp only [okNext, hargs, cmdOf, Val.i64]
    rfl
  rw [hn]
  obtain ⟨hI, -, hb⟩ := repC_unique hs₀ ha'
  refine ⟨rowM m y b, holds_withMach hs₀ _, inv_row hI y b,
    ⟨fun _ => List.cons_ne_nil _ _, fun _ => (by decide : (1 : BitVec 32) ≠ 0)⟩, fun hok => ?_⟩
  exact bad_rowM (hI.2 (hb hok.1)) (hb hok.1) hok.2

/-- **`entry` meets its completeness specification.** -/
theorem specC_entry (args : Typed (farkasExports.get ⟨1, by decide⟩).params) :
    FSpecValid P host (farkasI.addr ⟨1, by decide⟩)
      (callSpec farkasI RepC okNext GoodC ⟨⟨1, by decide⟩, args⟩) := by
  obtain ⟨fi₀, fi₁, fi₂, hfs, -, hm₁, -, -, hc₁, -, -, ht₁, -⟩ := farkasStore_funcs
  obtain ⟨j, a, hargs⟩ := typed_entry args.2
  refine FSpecValid.of_body_hwp (fi := fi₁) (code := ⟨⟨1⟩, [.i32, .i64], entryBody⟩)
    (fun s _ h => by rw [pre_funcsC h, hfs]; rfl) hc₁ (FnType.expand_of_ofDefType? ht₁)
    (fun _ _ h => pre_lenC h) (fun s args' hpre => ?_)
  obtain ⟨rfl, rs, m, ⟨s₀, hs₀, rfl⟩, hI₀, -⟩ := hpre
  rw [hm₁, hargs]
  refine entry_hwp hI₀.1 j a fun f' =>
    ⟨rfl, fun a' ha' r _ w _ => ⟨fun h => absurd (h : (1 : Nat) = 2) (by decide : ¬ (1 : Nat) = 2), ?_⟩⟩
  have hn : okNext a' (I := farkasI) ⟨⟨⟨1, by decide⟩, args⟩, w⟩ =
      ((Cmd.entry j.toNat a.toInt).apply a'.1, a'.2 ∧ CmdOk a'.1 (.entry j.toNat a.toInt)) := by
    simp only [okNext, hargs, cmdOf, Val.i64, Val.i32]
    rfl
  rw [hn]
  obtain ⟨hI, hhr, hb⟩ := repC_unique hs₀ ha'
  exact ⟨entryM m j a, holds_withMach hs₀ _, inv_entry hI j a,
    hhr.trans apply_entry_ne_nil.symm, fun hok => bad_entryM hI (hb hok.1) hhr hok.2⟩

/-- **`check` meets its completeness specification.** -/
theorem specC_check (args : Typed (farkasExports.get ⟨2, by decide⟩).params) :
    FSpecValid P host (farkasI.addr ⟨2, by decide⟩)
      (callSpec farkasI RepC okNext GoodC ⟨⟨2, by decide⟩, args⟩) := by
  obtain ⟨fi₀, fi₁, fi₂, hfs, -, -, hm₂, -, -, hc₂, -, -, ht₂⟩ := farkasStore_funcs
  have hargs := typed_nil args.2
  refine FSpecValid.of_body_hwp (fi := fi₂) (code := ⟨⟨2⟩, [.i32, .i32], checkBody⟩)
    (fun s _ h => by rw [pre_funcsC h, hfs]; rfl) hc₂ (FnType.expand_of_ofDefType? ht₂)
    (fun _ _ h => pre_lenC h) (fun s args' hpre => ?_)
  obtain ⟨rfl, rs, m, ⟨s₀, hs₀, rfl⟩, hI₀, -⟩ := hpre
  rw [hm₂, hargs]
  refine check_hwp hI₀.1 fun B nz f' hd => ⟨rfl, fun a' ha' r hr w hw => ⟨fun _ hok hc => ?_, ?_⟩⟩
  · obtain ⟨hI, -, hb⟩ := repC_unique hs₀ ha'
    have h1 : checkRes m nz = 1 := check_complete hI (hb hok) hc hd
    have hr' : r = .values [Val.i32 (checkRes m nz)] := (Option.some.inj hr).symm
    rw [Answer.toResult_of_ofResult? hw, hr', h1]
  · exact ⟨checkEnd B, holds_withMach hs₀ _, inv_check hd, ⟨fun h => absurd rfl h, fun h => absurd rfl h⟩,
      fun _ => rfl⟩

/-- **Every export call meets its completeness specification.** -/
theorem farkas_specC (f : farkasI.F.Op) :
    FSpecValid P host (farkasI.addr f.1) (callSpec farkasI RepC okNext GoodC f) := by
  obtain ⟨⟨j, hj⟩, args⟩ := f
  have hj' : j < 3 := hj
  match j, hj, hj', args with
  | 0, _, _, args => exact specC_row args
  | 1, _, _, args => exact specC_entry args
  | 2, _, _, args => exact specC_check args

/-! ## Sessions -/

theorem repC_init : RepC ([], True) farkasI.store :=
  ⟨Mach.init, farkasStore_holds, inv_init, ⟨fun h => absurd rfl h, fun h => absurd rfl h⟩, fun _ => rfl⟩

/-- The rows tracked by `okNext` are those `next` loads. -/
theorem after_okNext_fst {I : ScalarInstance} :
    ∀ (l : List (Call I)) (a : WRows × Prop), (after okNext a l).1 = after next a.1 l
  | [], _ => rfl
  | c :: l, a => by
    have h : (okNext a c).1 = next a.1 c := by
      unfold okNext next
      split
      · rfl
      · split <;> rfl
    exact (after_okNext_fst l (okNext a c)).trans (h ▸ rfl)

/-- **Completeness of the Wasm checker over sessions** (partial correctness): in every session,
a `check` after `row`/`entry` calls that passed the bounds (`LoadsOk`) and loaded a valid Farkas
certificate answers `1`. -/
theorem farkas_complete {K : Env farkasI.E} {l₁ l₂ : List (Call farkasI)} {c : Call farkasI}
    (h : Session P farkasI K farkasI.store (l₁ ++ c :: l₂)) (hc : c.1.1.val = 2)
    (hok : LoadsOk l₁) (hcert : WRows.IsCert (loaded l₁)) :
    Answer.toResult (ft := farkasI.exports.get c.1.1) c.2 = .values [Val.i32 1] := by
  have hg := allGood_append (session_allGood (fun f => farkas_specC f) repC_init h)
  have hl : (after okNext (([] : WRows), True) l₁).1 = loaded l₁ := after_okNext_fst l₁ ([], True)
  exact hg hc hok (hl ▸ hcert)

/-! ## A positive test -/

/-- The calls loading `x₀ ≤ 1` and `-x₀ ≤ -2` with the multipliers `1, 1`. -/
def certCalls (w₁ : farkasI.F.Ar (rowOp 1 1)) (w₂ : farkasI.F.Ar (entryOp 0 1))
    (w₃ : farkasI.F.Ar (rowOp 1 (-2))) (w₄ : farkasI.F.Ar (entryOp 0 (-1))) : List (Call farkasI) :=
  [⟨rowOp 1 1, w₁⟩, ⟨entryOp 0 1, w₂⟩, ⟨rowOp 1 (-2), w₃⟩, ⟨entryOp 0 (-1), w₄⟩]

theorem certCalls_loaded {w₁ w₂ w₃ w₄} :
    loaded (certCalls w₁ w₂ w₃ w₄) = [(1, ⟨[(0, -1)], -2⟩), (1, ⟨[(0, 1)], 1⟩)] := rfl

theorem certCalls_ok {w₁ w₂ w₃ w₄} : LoadsOk (certCalls w₁ w₂ w₃ w₄) := by
  show ((((True ∧ CmdOk [] (.row 1 1)) ∧ CmdOk [(1, ⟨[], 1⟩)] (.entry 0 1)) ∧
    CmdOk [(1, ⟨[(0, 1)], 1⟩)] (.row 1 (-2))) ∧
    CmdOk [(1, ⟨[], -2⟩), (1, ⟨[(0, 1)], 1⟩)] (.entry 0 (-1)))
  simp only [CmdOk, cB, aB, nVars]
  decide

/-- **A valid certificate is accepted**: in every session (every profile and environment) that
loads `x₀ ≤ 1, -x₀ ≤ -2` with the multipliers `1, 1`, the following `check` answers `1`. -/
theorem cert_accepted {K : Env farkasI.E} {l₂ : List (Call farkasI)}
    (w₁ : farkasI.F.Ar (rowOp 1 1)) (w₂ : farkasI.F.Ar (entryOp 0 1))
    (w₃ : farkasI.F.Ar (rowOp 1 (-2))) (w₄ : farkasI.F.Ar (entryOp 0 (-1)))
    (w : farkasI.F.Ar checkOp)
    (h : Session P farkasI K farkasI.store (certCalls w₁ w₂ w₃ w₄ ++ ⟨checkOp, w⟩ :: l₂)) :
    Answer.toResult (ft := farkasI.exports.get checkOp.1) w = .values [Val.i32 1] :=
  farkas_complete h rfl certCalls_ok (certCalls_loaded ▸ WRows.check_sound (by decide))

end Silmaril.Wasm.Examples.Farkas
