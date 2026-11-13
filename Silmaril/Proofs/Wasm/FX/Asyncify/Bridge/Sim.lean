module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.Steps

/-!
# The tool in the kernel: the simulation

`bridge_sim`: on programs without `return` and `if` (`Straight`), the relation `BR` is a
stuttering simulation from the tool's source system (the frame machine closed by a host,
`Tool.srcStep`) to the translated kernel closed by the same host (`hsstep` on `trP E` with
`kHost E H`), host states observed, both read as machines over tool observations.

`BR`: equal host states; the tool's top frame is the kernel's top frame running the translated
rest of its code (`topF`: one value with its locals, operands and the current globals and
memory); every waiting tool frame is a kernel frame before its `mergeOp` (`WaitF`); the kernel
stack ends with the root frame of `sInit`.

One tool step is matched by:

* a straight-line instruction: 1 kernel step (`prim 1 (segOp i)`); a trap: 2 (the next
  `prim 1` finds no value);
* falling off the end of a body: 3 (`finOp`, the return, `mergeOp`), or 3 to the result at the
  root;
* a call of a defined function: 3 (`splitOp`, `call`, `enterOp`); a call of an import: 3
  (`splitOp`, the blocking `suspend` answered by the host, `mergeOp`); a trapping call: 2.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Bridge

open Silmaril.Wasm
open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify
open Silmaril.Wasm.FX.Asyncify.Host
open Silmaril.Wasm.FX.Asyncify.Bridge

variable {σ : Type} (E : Tool.Env) (H : Tool.Host σ)

/-- The top kernel frame of a tool frame `fr` of configuration `c`. -/
def topF (c : Tool.Cfg) (fr : Tool.Frame) : SFrame KV :=
  ⟨trCode E fr.code ++ [.prim 1 finOp], [.val (fr.ls c)], none⟩

/-- A waiting tool frame in the kernel: before the merge of the callee's results (its value has
the globals and memory of the time of the call, which the merge drops). -/
def WaitF (fr : Tool.Frame) (b : SFrame KV) : Prop :=
  ∃ g m, b = ⟨.prim 2 mergeOp :: (trCode E fr.code ++ [.prim 1 finOp]),
    [.val ⟨fr.locals, fr.ops, g, m⟩], none⟩

/-- The root frame of `sInit` after its call. -/
def root : SFrame KV := ⟨[], [], none⟩

/-- **The relation** between the tool's source system and the translated kernel. -/
def BR (x : Tool.Cfg × σ) (y : SCfg KV × σ) : Prop :=
  x.2 = y.2 ∧ ∃ top rest bs, x.1.frames = top :: rest ∧
    y.1.stack = topF E x.1 top :: (bs ++ [root]) ∧ List.Forall₂ (WaitF E) rest bs ∧
    NoCtl top.code ∧ ∀ fr ∈ rest, NoCtl fr.code

/-- The one-step obligation. -/
def Ok (x : Tool.Cfg × σ) (y : SCfg KV × σ) : Prop :=
  ∃ n, 0 < n ∧ ResRel (BR E) (src E H x) (runN (tgt E H) n y)

theorem waits_none {rest : List Tool.Frame} {bs : List (SFrame KV)}
    (hw : List.Forall₂ (WaitF E) rest bs) : ∀ b ∈ bs ++ [root], b.wait = none := by
  induction hw with
  | nil =>
    intro b hb
    have hb' : b = root := by simpa only [List.nil_append, List.mem_singleton] using hb
    rw [hb']
    rfl
  | @cons fr b' rs bs' h _ ih =>
    intro b hb
    have hb' : b = b' ∨ b ∈ bs' ++ [root] := by simpa only [List.cons_append, List.mem_cons] using hb
    rcases hb' with rfl | hb'
    · obtain ⟨g, m, rfl⟩ := h
      rfl
    · exact ih b hb'

/-! ## Falling off the end -/

variable (K : List (Option (List (SFrame KV)))) (s : σ) (fid : Nat) (ls ops : List Tool.W)
  (nres : Nat) (g : List Tool.W) (m : Nat → Tool.W)

/-- The bottom frame returns: the result at the root. -/
theorem sim_done : Ok E H (⟨[⟨fid, ls, ops, [], nres⟩], g, m⟩, s)
    (⟨K, topF E ⟨[⟨fid, ls, ops, [], nres⟩], g, m⟩ ⟨fid, ls, ops, [], nres⟩ :: ([] ++ [root])⟩, s) :=
  ⟨3, by omega, rfl⟩

/-- A frame returns to its caller. -/
theorem sim_ret (cl : Tool.Frame) (rest : List Tool.Frame) (b : SFrame KV) (bs : List (SFrame KV))
    (hb : WaitF E cl b) (hw : List.Forall₂ (WaitF E) rest bs) (hcl : NoCtl cl.code)
    (hr : ∀ fr ∈ rest, NoCtl fr.code) :
    Ok E H (⟨⟨fid, ls, ops, [], nres⟩ :: cl :: rest, g, m⟩, s)
      (⟨K, topF E ⟨⟨fid, ls, ops, [], nres⟩ :: cl :: rest, g, m⟩ ⟨fid, ls, ops, [], nres⟩ ::
        (b :: bs ++ [root])⟩, s) := by
  obtain ⟨g', m', rfl⟩ := hb
  refine ⟨3, by omega, ?_⟩
  exact ⟨rfl, { cl with ops := ops ++ cl.ops }, rest, bs, rfl, rfl, hw, hcl, hr⟩

/-! ## Straight-line instructions -/

variable {E} in
theorem topF_seg {c : Tool.Cfg} {i : Instr} {code : List Instr} (hctl : Tool.ctlOf i = none) :
    topF E c ⟨fid, ls, ops, i :: code, nres⟩ =
      ⟨.prim 1 (segOp i) :: (trCode E code ++ [.prim 1 finOp]), [.val ⟨ls, ops, c.globals, c.mem⟩],
        none⟩ := by
  simp only [topF, trCode_cons, trI_seg E hctl, List.cons_append]
  rfl

/-- A straight-line instruction. -/
theorem sim_seg (i : Instr) (code : List Instr) (rest : List Tool.Frame) (bs : List (SFrame KV))
    (hctl : Tool.ctlOf i = none) (v' : KV) (hseg : Tool.segCore i ⟨ls, ops, g, m⟩ = some v')
    (hw : List.Forall₂ (WaitF E) rest bs) (hc : NoCtl (i :: code))
    (hr : ∀ fr ∈ rest, NoCtl fr.code) :
    Ok E H (⟨⟨fid, ls, ops, i :: code, nres⟩ :: rest, g, m⟩, s)
      (⟨K, topF E ⟨⟨fid, ls, ops, i :: code, nres⟩ :: rest, g, m⟩ ⟨fid, ls, ops, i :: code, nres⟩ ::
        (bs ++ [root])⟩, s) := by
  have hsrc : src E H (⟨⟨fid, ls, ops, i :: code, nres⟩ :: rest, g, m⟩, s) =
      .next (⟨⟨fid, v'.locals, v'.ops, code, nres⟩ :: rest, v'.globals, v'.mem⟩, s) := by
    have hseg' : Tool.segCore i (Tool.Frame.ls ⟨fid, ls, ops, i :: code, nres⟩
        ⟨⟨fid, ls, ops, i :: code, nres⟩ :: rest, g, m⟩) = some v' := hseg
    simp only [src, asRes, Tool.srcStep, Tool.step, Tool.exec, hctl, hseg']
  have htgt : runN (tgt E H) 1 (⟨K, topF E ⟨⟨fid, ls, ops, i :: code, nres⟩ :: rest, g, m⟩
      ⟨fid, ls, ops, i :: code, nres⟩ :: (bs ++ [root])⟩, s) =
      .next (⟨K, topF E ⟨⟨fid, v'.locals, v'.ops, code, nres⟩ :: rest, v'.globals, v'.mem⟩
        ⟨fid, v'.locals, v'.ops, code, nres⟩ :: (bs ++ [root])⟩, s) := by
    rw [topF_seg fid ls ops nres hctl]
    refine runN_one' ((tgt_prim1 E H K s _ _ _ _).trans ?_)
    rw [segOp_some hseg]
    rfl
  refine ⟨1, Nat.one_pos, ?_⟩
  rw [hsrc, htgt]
  exact ⟨rfl, _, rest, bs, rfl, rfl, hw, fun j hj => hc j (List.mem_cons_of_mem _ hj), hr⟩

/-- A trapping straight-line instruction. -/
theorem sim_seg_trap (i : Instr) (code : List Instr) (rest : List Tool.Frame)
    (bs : List (SFrame KV)) (hctl : Tool.ctlOf i = none)
    (hseg : Tool.segCore i ⟨ls, ops, g, m⟩ = none) :
    Ok E H (⟨⟨fid, ls, ops, i :: code, nres⟩ :: rest, g, m⟩, s)
      (⟨K, topF E ⟨⟨fid, ls, ops, i :: code, nres⟩ :: rest, g, m⟩ ⟨fid, ls, ops, i :: code, nres⟩ ::
        (bs ++ [root])⟩, s) := by
  have hsrc : src E H (⟨⟨fid, ls, ops, i :: code, nres⟩ :: rest, g, m⟩, s) =
      .stop (.done [.val (.trap s)]) := by
    have hseg' : Tool.segCore i (Tool.Frame.ls ⟨fid, ls, ops, i :: code, nres⟩
        ⟨⟨fid, ls, ops, i :: code, nres⟩ :: rest, g, m⟩) = none := hseg
    simp only [src, asRes, Tool.srcStep, Tool.step, Tool.exec, hctl, hseg']
  obtain ⟨op, r, hh⟩ := trCode_head E code
  have h1 : tgt E H (⟨K, topF E ⟨⟨fid, ls, ops, i :: code, nres⟩ :: rest, g, m⟩
      ⟨fid, ls, ops, i :: code, nres⟩ :: (bs ++ [root])⟩, s) =
      .next (⟨K, ⟨.prim 1 op :: r, [], none⟩ :: (bs ++ [root])⟩, s) := by
    rw [topF_seg fid ls ops nres hctl, tgt_prim1, segOp_none hseg, hh]
    rfl
  refine ⟨2, by omega, ?_⟩
  rw [hsrc, runN_two h1 (tgt_prim_nil E H K s 0 op r none _)]
  rfl

/-! ## Calls of imports: blocking calls -/

variable {E} in
theorem topF_imp {c : Tool.Cfg} {f : FuncIdx} {code : List Instr}
    (hf : f.value.val < E.imps.length) :
    topF E c ⟨fid, ls, ops, .call f :: code, nres⟩ =
      ⟨.prim 1 (splitOp (E.imps[f.value.val]'hf).1) :: .suspend f.value.val 1 :: .prim 2 mergeOp ::
        (trCode E code ++ [.prim 1 finOp]), [.val ⟨ls, ops, c.globals, c.mem⟩], none⟩ := by
  simp only [topF, trCode_cons, trI_imp E hf, impArity_eq E hf, List.cons_append, List.nil_append]
  rfl

/-- A blocking call: split the arguments off, the host answers the unhandled `suspend`, merge. -/
theorem sim_imp (f : FuncIdx) (code : List Instr) (rest : List Tool.Frame) (bs : List (SFrame KV))
    (hf : f.value.val < E.imps.length) (hn : (E.imps[f.value.val]'hf).1 ≤ ops.length)
    (hw : List.Forall₂ (WaitF E) rest bs) (hc : NoCtl (.call f :: code))
    (hr : ∀ fr ∈ rest, NoCtl fr.code) :
    Ok E H (⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩, s)
      (⟨K, topF E ⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩
        ⟨fid, ls, ops, .call f :: code, nres⟩ :: (bs ++ [root])⟩, s) := by
  let n := (E.imps[f.value.val]'hf).1
  let r := H.answer s f.value.val (ops.take n).reverse
  let ans := (Tool.fit (impRes E f.value.val) r.2).reverse
  let X := trCode E code ++ [.prim 1 finOp]
  let L := bs ++ [root]
  let a : KV := ⟨(ops.take n).reverse, [], g, m⟩
  let v : KV := ⟨ls, ops.drop n, g, m⟩
  have hsrc : src E H (⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩, s) =
      .next (⟨⟨fid, ls, ans ++ ops.drop n, code, nres⟩ :: rest, g, m⟩, r.1) := by
    simp only [src, asRes, Tool.srcStep, Tool.step, Tool.exec, Tool.ctlOf, dite_eq_left hf, ite_eq_left hn]
    rfl
  have h1 : tgt E H (⟨K, topF E ⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩
      ⟨fid, ls, ops, .call f :: code, nres⟩ :: L⟩, s) =
      .next (⟨K, ⟨.suspend f.value.val 1 :: .prim 2 mergeOp :: X, [.val a, .val v], none⟩ :: L⟩,
        s) := by
    rw [topF_imp fid ls ops nres hf, tgt_prim1, splitOp_ok (v := ⟨ls, ops, g, m⟩) hn]
    rfl
  have h2 : tgt E H (⟨K, ⟨.suspend f.value.val 1 :: .prim 2 mergeOp :: X, [.val a, .val v], none⟩
      :: L⟩, s) =
      .next (⟨K, ⟨.prim 2 mergeOp :: X, [.val ⟨[], ans, g, m⟩, .val v], none⟩ :: L⟩, r.1) :=
    tgt_susp E H K s (split_none (waits_none E hw)) _ a v
  have h3 : tgt E H (⟨K, ⟨.prim 2 mergeOp :: X, [.val ⟨[], ans, g, m⟩, .val v], none⟩ :: L⟩, r.1) =
      .next (⟨K, topF E ⟨⟨fid, ls, ans ++ ops.drop n, code, nres⟩ :: rest, g, m⟩
        ⟨fid, ls, ans ++ ops.drop n, code, nres⟩ :: L⟩, r.1) :=
    tgt_prim2 E H K r.1 _ _ _ _ _
  refine ⟨3, by omega, ?_⟩
  rw [hsrc, runN_three h1 h2 h3]
  exact ⟨rfl, _, rest, bs, rfl, rfl, hw, fun j hj => hc j (List.mem_cons_of_mem _ hj), hr⟩

/-- A blocking call without enough operands traps. -/
theorem sim_imp_trap (f : FuncIdx) (code : List Instr) (rest : List Tool.Frame)
    (bs : List (SFrame KV)) (hf : f.value.val < E.imps.length)
    (hn : ¬ (E.imps[f.value.val]'hf).1 ≤ ops.length) :
    Ok E H (⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩, s)
      (⟨K, topF E ⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩
        ⟨fid, ls, ops, .call f :: code, nres⟩ :: (bs ++ [root])⟩, s) := by
  have hsrc : src E H (⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩, s) =
      .stop (.done [.val (.trap s)]) := by
    simp only [src, asRes, Tool.srcStep, Tool.step, Tool.exec, Tool.ctlOf, dite_eq_left hf, ite_eq_right hn]
  have h1 : tgt E H (⟨K, topF E ⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩
      ⟨fid, ls, ops, .call f :: code, nres⟩ :: (bs ++ [root])⟩, s) =
      .next (⟨K, ⟨.suspend f.value.val 1 :: .prim 2 mergeOp :: (trCode E code ++ [.prim 1 finOp]),
        [], none⟩ :: (bs ++ [root])⟩, s) := by
    rw [topF_imp fid ls ops nres hf, tgt_prim1, splitOp_short (v := ⟨ls, ops, g, m⟩) hn]
    rfl
  refine ⟨2, by omega, ?_⟩
  rw [hsrc, runN_two h1 (tgt_susp_nil E H K s _ _ none _)]
  rfl

/-! ## Calls of defined functions -/

variable {E} in
theorem topF_fn {c : Tool.Cfg} {f : FuncIdx} {code : List Instr}
    (hf : ¬ f.value.val < E.imps.length) :
    topF E c ⟨fid, ls, ops, .call f :: code, nres⟩ =
      ⟨.prim 1 (splitOp (fnArity E f.value.val)) :: .call f.value.val :: .prim 2 mergeOp ::
        (trCode E code ++ [.prim 1 finOp]), [.val ⟨ls, ops, c.globals, c.mem⟩], none⟩ := by
  simp only [topF, trCode_cons, trI_fn E hf, List.cons_append, List.nil_append]
  rfl

/-- A call of a defined function: split the arguments off, call, enter. -/
theorem sim_fn (hE : Straight E) (f : FuncIdx) (code : List Instr) (rest : List Tool.Frame)
    (bs : List (SFrame KV)) (hf : ¬ f.value.val < E.imps.length) {fn : Tool.FnDef}
    (hfn : E.fns[f.value.val - E.imps.length]? = some fn) (hn : fn.nparams ≤ ops.length)
    (hw : List.Forall₂ (WaitF E) rest bs) (hc : NoCtl (.call f :: code))
    (hr : ∀ fr ∈ rest, NoCtl fr.code) :
    Ok E H (⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩, s)
      (⟨K, topF E ⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩
        ⟨fid, ls, ops, .call f :: code, nres⟩ :: (bs ++ [root])⟩, s) := by
  let args := (ops.take fn.nparams).reverse
  let X := trCode E code ++ [.prim 1 finOp]
  let L := bs ++ [root]
  let a : KV := ⟨args, [], g, m⟩
  let v : KV := ⟨ls, ops.drop fn.nparams, g, m⟩
  let cl : Tool.Frame := ⟨fid, ls, ops.drop fn.nparams, code, nres⟩
  let c' : Tool.Cfg := ⟨Tool.entry f.value.val fn args :: cl :: rest, g, m⟩
  have hsrc : src E H (⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩, s) =
      .next (c', s) := by
    simp only [src, asRes, Tool.srcStep, Tool.step, Tool.exec, Tool.ctlOf, dite_eq_right hf, hfn,
      ite_eq_left hn]
    rfl
  have h1 : tgt E H (⟨K, topF E ⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩
      ⟨fid, ls, ops, .call f :: code, nres⟩ :: L⟩, s) =
      .next (⟨K, ⟨.call f.value.val :: .prim 2 mergeOp :: X, [.val a, .val v], none⟩ :: L⟩, s) := by
    rw [topF_fn fid ls ops nres hf, fnArity_eq E hfn, tgt_prim1,
      splitOp_ok (v := ⟨ls, ops, g, m⟩) hn]
    rfl
  have h2 : tgt E H (⟨K, ⟨.call f.value.val :: .prim 2 mergeOp :: X, [.val a, .val v], none⟩ :: L⟩,
      s) = .next (⟨K, ⟨trFn E fn, [.val a], none⟩ :: ⟨.prim 2 mergeOp :: X, [.val v], none⟩ :: L⟩,
        s) :=
    tgt_call E H K s (trP_some E hf hfn) _ a v L
  have h3 : tgt E H (⟨K, ⟨trFn E fn, [.val a], none⟩ :: ⟨.prim 2 mergeOp :: X, [.val v], none⟩ :: L⟩,
      s) = .next (⟨K, topF E c' (Tool.entry f.value.val fn args) ::
        (⟨.prim 2 mergeOp :: X, [.val v], none⟩ :: bs ++ [root])⟩, s) :=
    tgt_prim1 E H K s _ _ a _
  have hmem : fn ∈ E.fns := List.mem_of_getElem? hfn
  refine ⟨3, by omega, ?_⟩
  rw [hsrc, runN_three h1 h2 h3]
  exact ⟨rfl, _, cl :: rest, _ :: bs, rfl, rfl, .cons ⟨g, m, rfl⟩ hw, hE fn hmem,
    fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ fun i hi => hc i (List.mem_cons_of_mem _ hi))
      (hr j)⟩

/-- A call of a missing function traps. -/
theorem sim_fn_none (f : FuncIdx) (code : List Instr) (rest : List Tool.Frame)
    (bs : List (SFrame KV)) (hf : ¬ f.value.val < E.imps.length)
    (hfn : E.fns[f.value.val - E.imps.length]? = none) :
    Ok E H (⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩, s)
      (⟨K, topF E ⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩
        ⟨fid, ls, ops, .call f :: code, nres⟩ :: (bs ++ [root])⟩, s) := by
  have hsrc : src E H (⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩, s) =
      .stop (.done [.val (.trap s)]) := by
    simp only [src, asRes, Tool.srcStep, Tool.step, Tool.exec, Tool.ctlOf, dite_eq_right hf, hfn]
  have h1 : tgt E H (⟨K, topF E ⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩
      ⟨fid, ls, ops, .call f :: code, nres⟩ :: (bs ++ [root])⟩, s) =
      .next (⟨K, ⟨.call f.value.val :: .prim 2 mergeOp :: (trCode E code ++ [.prim 1 finOp]),
        [.val ⟨[], [], g, m⟩, .val ⟨ls, ops, g, m⟩], none⟩ :: (bs ++ [root])⟩, s) := by
    rw [topF_fn fid ls ops nres hf, fnArity_none E hfn, tgt_prim1,
      splitOp_ok (v := ⟨ls, ops, g, m⟩) (Nat.zero_le _)]
    rfl
  refine ⟨2, by omega, ?_⟩
  rw [hsrc, runN_two h1 (tgt_call_none E H K s (trP_none E hfn) _ _ none _)]
  rfl

/-- A call of a defined function without enough operands traps. -/
theorem sim_fn_trap (f : FuncIdx) (code : List Instr) (rest : List Tool.Frame)
    (bs : List (SFrame KV)) (hf : ¬ f.value.val < E.imps.length) {fn : Tool.FnDef}
    (hfn : E.fns[f.value.val - E.imps.length]? = some fn) (hn : ¬ fn.nparams ≤ ops.length) :
    Ok E H (⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩, s)
      (⟨K, topF E ⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩
        ⟨fid, ls, ops, .call f :: code, nres⟩ :: (bs ++ [root])⟩, s) := by
  have hsrc : src E H (⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩, s) =
      .stop (.done [.val (.trap s)]) := by
    simp only [src, asRes, Tool.srcStep, Tool.step, Tool.exec, Tool.ctlOf, dite_eq_right hf, hfn,
      ite_eq_right hn]
  have h1 : tgt E H (⟨K, topF E ⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩
      ⟨fid, ls, ops, .call f :: code, nres⟩ :: (bs ++ [root])⟩, s) =
      .next (⟨K, ⟨.call f.value.val :: .prim 2 mergeOp :: (trCode E code ++ [.prim 1 finOp]),
        [], none⟩ :: (bs ++ [root])⟩, s) := by
    rw [topF_fn fid ls ops nres hf, fnArity_eq E hfn, tgt_prim1,
      splitOp_short (v := ⟨ls, ops, g, m⟩) hn]
    rfl
  refine ⟨2, by omega, ?_⟩
  rw [hsrc, runN_two h1 (tgt_call_nil E H K s (trP_some E hf hfn) _ none _)]
  rfl

end Silmaril.Proofs.Wasm.FX.Asyncify.Bridge
