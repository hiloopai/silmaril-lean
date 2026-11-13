module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim.Lift
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core.Glob
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core.Mem

/-!
# Straight-line instructions inside a level

For each non-branching instruction accepted by the checker (`InsOk`, calls excepted), from the
operands of level 0 (`ops`) with any operands of the enclosing levels below them (`Y`): the
machine's `segCore` acts on `ops` only, Core runs the instruction from `stackA ops`, and the
store invariants (`SInv`) and the flags (`AbsOk`) are kept (`SegStep`). Division traps and
accesses past the memory trap in Core too (`bin_trap`, `load_oob`, `store_oob`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.FX.Asyncify.Tool
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core

variable {H : Type}

/-- The store holds the program, the globals and the memory; the globals are those of the
asyncified program. -/
def SInv (cap : Nat) (E : Env) (mi : ModuleInst) (s : Store H) (gs : List W) (mem : Nat → W) :
    Prop :=
  HoldsProg s mi E ∧ GlobalsAre s ⟨[], mi⟩ gs ∧ MemAre s ⟨[], mi⟩ mem cap ∧ GInv gs

/-- A straight-line instruction `i` from locals `ls`, level-0 operands `ops`, globals `gs` and
memory `mem`: the machine's result with any operands `Y` below, and the Core run before `rest`
to a store with the invariants, with flags `a'` for the new operands. -/
def SegStep (Pf : Profile) (host : HostSemantics H) (cap : Nat) (E : Env) (mi : ModuleInst)
    (s : Store H) (ls ops gs : List W) (mem : Nat → W) (i : Instr) (a' : List Bool)
    (rest : List Admin) : Prop :=
  ∃ ls' ops' gs' mem' s', (∀ Y, segCore i ⟨ls, ops ++ Y, gs, mem⟩ = some ⟨ls', ops' ++ Y, gs', mem'⟩) ∧
    Execution.Core.Steps Pf host ⟨s, localsF ⟨[], mi⟩ ls, stackA ops ++ .plain i :: rest⟩
      ⟨s', localsF ⟨[], mi⟩ ls', stackA ops' ++ rest⟩ ∧
    SInv cap E mi s' gs' mem' ∧ AbsOk a' ops' ∧ ls'.length = ls.length

variable {Pf : Profile} {host : HostSemantics H} {cap : Nat} {E : Env} {mi : ModuleInst}
  {s : Store H} {ls ops gs : List W} {mem : Nat → W} {a : List Bool} (rest : List Admin)

theorem absOk_false {a : List Bool} {ops : List W} (w : W) (h : AbsOk a ops) :
    AbsOk (false :: a) (w :: ops) :=
  .cons (fun hf => absurd hf Bool.false_ne_true) h

theorem absOk_replicate {a : List Bool} {ops vs : List W} (h : AbsOk a ops) :
    AbsOk (List.replicate vs.length false ++ a) (vs ++ ops) := by
  induction vs with
  | nil => exact h
  | cons v vs ih => exact absOk_false v ih

theorem absOk_length {a : List Bool} {ops : List W} (h : AbsOk a ops) : a.length = ops.length :=
  List.Forall₂.length_eq h

/-- A pure instruction. -/
theorem seg_pure {i : Instr} {ls' ops' : List W} {a' : List Bool}
    (hp : pexec i ls ops = some (ls', ops'))
    (hseg : ∀ Y, segCore i ⟨ls, ops ++ Y, gs, mem⟩ = some ⟨ls', ops' ++ Y, gs, mem⟩)
    (hI : SInv cap E mi s gs mem) (ha : AbsOk a' ops') (hl : ls'.length = ls.length) :
    SegStep Pf host cap E mi s ls ops gs mem i a' rest :=
  ⟨ls', ops', gs, mem, s, hseg, pexec_core s _ hp rest, hI, ha, hl⟩

theorem seg_nop (hI : SInv cap E mi s gs mem) (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls ops gs mem .nop a rest :=
  seg_pure rest rfl (fun _ => rfl) hI ha rfl

theorem seg_drop (w : W) (hI : SInv cap E mi s gs mem) (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls (w :: ops) gs mem .drop a rest :=
  seg_pure rest rfl (fun _ => rfl) hI ha rfl

theorem seg_get {i : LocalIdx} (hi : i.value.val < ls.length) (hI : SInv cap E mi s gs mem)
    (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls ops gs mem (.localGet i) (false :: a) rest := by
  have hv : ls[i.value.val]? = some ls[i.value.val] := List.getElem?_eq_getElem hi
  exact seg_pure (ls' := ls) (ops' := ls[i.value.val] :: ops) rest
    (by simp only [pexec, hv, Option.map_some])
    (fun _ => by simp only [segCore, pexec, hv, Option.map_some, List.cons_append])
    hI (absOk_false _ ha) rfl

theorem seg_set {i : LocalIdx} (hi : i.value.val < ls.length) (w : W)
    (hI : SInv cap E mi s gs mem) (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls (w :: ops) gs mem (.localSet i) a rest :=
  seg_pure (ls' := ls.set i.value.val w) (ops' := ops) rest (by simp only [pexec, hi, ite_true])
    (fun _ => by simp only [segCore, pexec, List.cons_append, hi, ite_true]) hI ha
    (List.length_set ..)

theorem seg_tee {i : LocalIdx} (hi : i.value.val < ls.length) (w : W)
    (hI : SInv cap E mi s gs mem) (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls (w :: ops) gs mem (.localTee i) (false :: a) rest :=
  seg_pure (ls' := ls.set i.value.val w) (ops' := w :: ops) rest (by simp only [pexec, hi, ite_true])
    (fun _ => by simp only [segCore, pexec, List.cons_append, hi, ite_true]) hI
    (absOk_false _ ha) (List.length_set ..)

theorem seg_const (c : W) (hI : SInv cap E mi s gs mem) (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls ops gs mem (.intConst .i32 c)
      (decide (c.toNat % 4 = 0) :: a) rest :=
  seg_pure rest rfl (fun _ => rfl) hI (.cons (fun h => of_decide_eq_true h) ha) rfl

theorem seg_un (op : IntUnOp) (w : W) (hI : SInv cap E mi s gs mem) (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls (w :: ops) gs mem (.intUnOp .i32 op) (false :: a) rest :=
  seg_pure rest rfl (fun _ => rfl) hI (absOk_false _ ha) rfl

theorem seg_test (op : IntTestOp) (w : W) (hI : SInv cap E mi s gs mem) (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls (w :: ops) gs mem (.intTestOp .i32 op) (false :: a) rest :=
  seg_pure rest rfl (fun _ => rfl) hI (absOk_false _ ha) rfl

theorem seg_rel (op : IntRelOp) (y x : W) (hI : SInv cap E mi s gs mem) (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls (y :: x :: ops) gs mem (.intRelOp .i32 op) (false :: a) rest :=
  seg_pure rest rfl (fun _ => rfl) hI (absOk_false _ ha) rfl

theorem toNat_add_al {x y : W} (hx : x.toNat % 4 = 0) (hy : y.toNat % 4 = 0) :
    (x + y).toNat % 4 = 0 := by
  rw [BitVec.toNat_add]
  omega

theorem toNat_sub_al {x y : W} (hx : x.toNat % 4 = 0) (hy : y.toNat % 4 = 0) :
    (x - y).toNat % 4 = 0 := by
  rw [BitVec.toNat_sub]
  have := y.isLt
  omega

/-- The alignment flag of a binary operator is sound. -/
theorem binAl_ok {op : IntBinOp} {fy fx : Bool} {y x r : W} (hy : fy = true → y.toNat % 4 = 0)
    (hx : fx = true → x.toNat % 4 = 0) (hr : Numerics.intBinOp .i32 op x y = .ok r) :
    binAl op fx fy = true → r.toNat % 4 = 0 := by
  intro h
  cases op with
  | add =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    rw [← Except.ok.inj hr]; exact toNat_add_al (hx h1) (hy h2)
  | sub =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    rw [← Except.ok.inj hr]; exact toNat_sub_al (hx h1) (hy h2)
  | _ => cases h

theorem seg_bin (op : IntBinOp) {fy fx : Bool} (y x : W) {r : W}
    (hr : Numerics.intBinOp .i32 op x y = .ok r) (hy : fy = true → y.toNat % 4 = 0)
    (hx : fx = true → x.toNat % 4 = 0) (hI : SInv cap E mi s gs mem) (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls (y :: x :: ops) gs mem (.intBinOp .i32 op)
      (binAl op fx fy :: a) rest :=
  seg_pure rest (by simp only [pexec, hr])
    (fun _ => by simp only [segCore, pexec, List.cons_append, hr]) hI
    (.cons (binAl_ok hy hx hr) ha) rfl

/-- A division the machine traps on traps in Core. -/
theorem bin_trap (op : IntBinOp) (y x : W) {e : Numerics.IntTrap}
    (hr : Numerics.intBinOp .i32 op x y = .error e) (Y : List W) :
    segCore (.intBinOp .i32 op) ⟨ls, (y :: x :: ops) ++ Y, gs, mem⟩ = none ∧
      Execution.Core.Steps Pf host
        ⟨s, localsF ⟨[], mi⟩ ls, stackA (y :: x :: ops) ++ .plain (.intBinOp .i32 op) :: rest⟩
        ⟨s, localsF ⟨[], mi⟩ ls, stackA ops ++ .trap :: rest⟩ :=
  ⟨by simp only [segCore, pexec, List.cons_append, hr],
    .single (pexec_div_trap s _ ls ops op y x hr rest)⟩

theorem seg_gget {g : GlobalIdx} (hg : g.value.val < 2) (hI : SInv cap E mi s gs mem)
    (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls ops gs mem (.globalGet g) (decide (g.value.val = 1) :: a)
      rest := by
  have hlt : g.value.val < gs.length := by rw [hI.2.2.2.1]; exact hg
  have hv : gs[g.value.val]? = some gs[g.value.val] := List.getElem?_eq_getElem hlt
  have hal : decide (g.value.val = 1) = true → gs[g.value.val].toNat % 4 = 0 := fun h1 =>
    hI.2.2.2.2 _ (by rw [← of_decide_eq_true h1]; exact hv)
  exact ⟨ls, gs[g.value.val] :: ops, gs, mem, s,
    fun _ => by simp only [segCore, hv, List.cons_append],
    run_gget s _ rest hI.2.1 g hv, hI, .cons hal ha, rfl⟩

theorem ginv_set {gs : List W} (hG : GInv gs) {g : Nat} {w : W}
    (hw : g = 1 → w.toNat % 4 = 0) : GInv (gs.set g w) := by
  refine ⟨by rw [List.length_set]; exact hG.1, fun v hv => ?_⟩
  by_cases h1 : g = 1
  · have hl : 1 < gs.length := by rw [hG.1]; omega
    rw [h1, List.getElem?_set_self hl] at hv
    rw [← Option.some.inj hv]; exact hw h1
  · rw [List.getElem?_set_ne h1] at hv
    exact hG.2 v hv

theorem seg_gset {g : GlobalIdx} {b : Bool} (hg : g.value.val < 2)
    (hb : g.value.val = 1 → b = true) (w : W) (hw : b = true → w.toNat % 4 = 0)
    (hI : SInv cap E mi s gs mem) (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls (w :: ops) gs mem (.globalSet g) a rest := by
  have hlt : g.value.val < gs.length := by rw [hI.2.2.2.1]; exact hg
  obtain ⟨ga, gi, -, hG', hrun⟩ := run_gset (Pf := Pf) (host := host) s _ rest (ls := ls) (ops := ops)
    hI.2.1 g w hlt
  exact ⟨ls, ops, gs.set g.value.val w, mem, s.setGlobal ga (Val.i32 w),
    fun _ => by simp only [segCore, List.cons_append, hlt, ite_true],
    hrun, ⟨hI.1, hG', hI.2.2.1, ginv_set hI.2.2.2 fun h => hw (hb h)⟩, ha, rfl⟩

theorem seg_load {arg : MemArg} (x : W) (hx : x.toNat % 4 = 0) (hoff : arg.offset.val % 4 = 0)
    (hcap : x.toNat + arg.offset.val + 4 ≤ cap) (hI : SInv cap E mi s gs mem)
    (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls (x :: ops) gs mem (.intLoad .i32 none ⟨0⟩ arg) (false :: a)
      rest :=
  ⟨ls, mem (x.toNat + arg.offset.val) :: ops, gs, mem, s,
    fun _ => by simp [segCore],
    run_load s _ rest hI.2.2.1 x arg (by omega) hcap, hI, absOk_false _ ha, rfl⟩

theorem holdsProg_of_funcs {s s' : Store H} (h : s'.funcs = s.funcs) (hH : HoldsProg s mi E) :
    HoldsProg s' mi E := by
  intro j fd hj
  rw [h]
  exact hH j fd hj

theorem globalsAre_of_eq {s s' : Store H} {f : Silmaril.Wasm.Execution.Core.Frame}
    (h : ∀ g, s'.global? f g = s.global? f g) (hg : GlobalsAre s f gs) : GlobalsAre s' f gs := by
  unfold GlobalsAre
  simp only [h]
  exact hg

theorem seg_store {arg : MemArg} (v x : W) (hx : x.toNat % 4 = 0)
    (hoff : arg.offset.val % 4 = 0) (hcap : x.toNat + arg.offset.val + 4 ≤ cap)
    (hI : SInv cap E mi s gs mem) (ha : AbsOk a ops) :
    SegStep Pf host cap E mi s ls (v :: x :: ops) gs mem (.intStore .i32 none ⟨0⟩ arg) a rest := by
  obtain ⟨s', hM, hg, hf, hrun⟩ := run_store (Pf := Pf) (host := host) s _ rest (ls := ls) (ops := ops)
    hI.2.2.1 v x arg (by omega) hcap
  exact ⟨ls, ops, gs, upd mem (x.toNat + arg.offset.val) v, s',
    fun _ => by simp [segCore], hrun,
    ⟨holdsProg_of_funcs hf hI.1, globalsAre_of_eq hg hI.2.1, hM, hI.2.2.2⟩, ha, rfl⟩

theorem load_oob {arg : MemArg} (x : W) (hcap : cap < x.toNat + arg.offset.val + 4)
    (hI : SInv cap E mi s gs mem) :
    Execution.Core.Steps Pf host
      ⟨s, localsF ⟨[], mi⟩ ls, stackA (x :: ops) ++ .plain (.intLoad .i32 none ⟨0⟩ arg) :: rest⟩
      ⟨s, localsF ⟨[], mi⟩ ls, stackA ops ++ .trap :: rest⟩ :=
  .single (run_load_oob s _ rest hI.2.2.1 x arg hcap)

theorem store_oob {arg : MemArg} (v x : W) (hcap : cap < x.toNat + arg.offset.val + 4)
    (hI : SInv cap E mi s gs mem) :
    Execution.Core.Steps Pf host
      ⟨s, localsF ⟨[], mi⟩ ls,
        stackA (v :: x :: ops) ++ .plain (.intStore .i32 none ⟨0⟩ arg) :: rest⟩
      ⟨s, localsF ⟨[], mi⟩ ls, stackA ops ++ .trap :: rest⟩ :=
  .single (run_store_oob s _ rest hI.2.2.1 v x arg hcap)

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim
