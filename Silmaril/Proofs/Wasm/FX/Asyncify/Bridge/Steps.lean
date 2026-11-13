module

public import Silmaril.Wasm.FX.Asyncify.Bridge.Defs
public import Silmaril.Wasm.FX.Asyncify.Host.Obs.Thms

/-!
# The tool in the kernel: single steps

Steps of the translated kernel `tgt E H` (the host-closed kernel on `trP E`, host states
observed, mapped to tool observations) on the frame shapes of the translation, and steps of the
tool's source system `src E H`, as equations. Short proofs by unfolding.

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

/-- The tool's source system as a machine over tool observations. -/
abbrev src : Tool.Cfg × σ → Res (Tool.Cfg × σ) (Tool.Obs σ) := asRes (Tool.srcStep E H)

/-- The translated kernel, host states observed, as a machine over tool observations. -/
abbrev tgt : SCfg KV × σ → Res (SCfg KV × σ) (Tool.Obs σ) := mapObs toolOut (kSrc E H)

/-! ## Runs -/

section runs

variable {C O : Type} {step : C → Res C O}

theorem runN_two {c c₁ : C} {r : Res C O} (h1 : step c = .next c₁) (h2 : step c₁ = r) :
    runN step 2 c = r := by
  cases r <;> simp only [runN, h1, h2]

theorem runN_three {c c₁ c₂ : C} {r : Res C O} (h1 : step c = .next c₁) (h2 : step c₁ = .next c₂)
    (h3 : step c₂ = r) : runN step 3 c = r := by
  cases r <;> simp only [runN, h1, h2, h3]

theorem runN_one' {c : C} {r : Res C O} (h : step c = r) : runN step 1 c = r := by
  cases r <;> simp only [runN, h]

end runs

/-! ## Kernel steps -/

variable (K : List (Option (List (SFrame KV)))) (s : σ)

theorem tgt_prim1 (op : List KV → List KV) (c : List (Ins KV)) (v : KV) (L : List (SFrame KV)) :
    tgt E H (⟨K, ⟨.prim 1 op :: c, [.val v], none⟩ :: L⟩, s) =
      .next (⟨K, ⟨c, (op [v]).map .val, none⟩ :: L⟩, s) := by
  simp [tgt, mapObs, kSrc, observe, hsstep, blockedOn, sstep, sexec, popN, allVals, Res.map]

theorem tgt_prim2 (op : List KV → List KV) (c : List (Ins KV)) (r v : KV)
    (L : List (SFrame KV)) :
    tgt E H (⟨K, ⟨.prim 2 op :: c, [.val r, .val v], none⟩ :: L⟩, s) =
      .next (⟨K, ⟨c, (op [r, v]).map .val, none⟩ :: L⟩, s) := by
  simp [tgt, mapObs, kSrc, observe, hsstep, blockedOn, sstep, sexec, popN, allVals, Res.map]

theorem tgt_prim_nil (n : Nat) (op : List KV → List KV) (c : List (Ins KV))
    (w : Option (List Clause)) (L : List (SFrame KV)) :
    tgt E H (⟨K, ⟨.prim (n + 1) op :: c, [], w⟩ :: L⟩, s) = .stop (.done [.val (.trap s)]) := by
  simp [tgt, mapObs, kSrc, observe, hsstep, blockedOn, sstep, sexec, popN, Res.map,
    HOut.ofOutcome, toolOut]

theorem tgt_ret (ops : List (SV KV)) (w : Option (List Clause)) (b : SFrame KV)
    (L : List (SFrame KV)) :
    tgt E H (⟨K, ⟨[], ops, w⟩ :: b :: L⟩, s) = .next (⟨K, { b with ops := ops ++ b.ops } :: L⟩, s) := by
  simp [tgt, mapObs, kSrc, observe, hsstep, blockedOn, sstep, Res.map]

theorem tgt_call {g : Nat} {body : List (Ins KV)} (h : trP E g = some (1, body))
    (c : List (Ins KV)) (a v : KV) (L : List (SFrame KV)) :
    tgt E H (⟨K, ⟨.call g :: c, [.val a, .val v], none⟩ :: L⟩, s) =
      .next (⟨K, ⟨body, [.val a], none⟩ :: ⟨c, [.val v], none⟩ :: L⟩, s) := by
  simp [tgt, mapObs, kSrc, observe, hsstep, blockedOn, sstep, sexec, scall, popN, h, Res.map]

theorem tgt_call_nil {g : Nat} {body : List (Ins KV)} (h : trP E g = some (1, body))
    (c : List (Ins KV)) (w : Option (List Clause)) (L : List (SFrame KV)) :
    tgt E H (⟨K, ⟨.call g :: c, [], w⟩ :: L⟩, s) = .stop (.done [.val (.trap s)]) := by
  simp [tgt, mapObs, kSrc, observe, hsstep, blockedOn, sstep, sexec, scall, popN, h, Res.map,
    HOut.ofOutcome, toolOut]

theorem tgt_call_none {g : Nat} (h : trP E g = none) (c : List (Ins KV)) (ops : List (SV KV))
    (w : Option (List Clause)) (L : List (SFrame KV)) :
    tgt E H (⟨K, ⟨.call g :: c, ops, w⟩ :: L⟩, s) = .stop (.done [.val (.trap s)]) := by
  simp [tgt, mapObs, kSrc, observe, hsstep, blockedOn, sstep, sexec, scall, h, Res.map,
    HOut.ofOutcome, toolOut]

theorem tgt_susp {g : Nat} {L : List (SFrame KV)} (h : split g L = none) (c : List (Ins KV))
    (a v : KV) :
    tgt E H (⟨K, ⟨.suspend g 1 :: c, [.val a, .val v], none⟩ :: L⟩, s) =
      .next (⟨K, ⟨c, ((kHost E H).answer s g [.val a]).2 ++ [.val v], none⟩ :: L⟩,
        ((kHost E H).answer s g [.val a]).1) := by
  simp [tgt, mapObs, kSrc, observe, hsstep, blockedOn, popN, h]

theorem tgt_susp_nil (g : Nat) (c : List (Ins KV)) (w : Option (List Clause))
    (L : List (SFrame KV)) :
    tgt E H (⟨K, ⟨.suspend g 1 :: c, [], w⟩ :: L⟩, s) = .stop (.done [.val (.trap s)]) := by
  simp [tgt, mapObs, kSrc, observe, hsstep, blockedOn, sstep, sexec, popN, Res.map,
    HOut.ofOutcome, toolOut]

theorem tgt_done (ops : List (SV KV)) (w : Option (List Clause)) :
    tgt E H (⟨K, [⟨[], ops, w⟩]⟩, s) =
      .stop (.done [.val (toolOut (.done ops s))]) := by
  simp [tgt, mapObs, kSrc, observe, hsstep, blockedOn, sstep, Res.map, HOut.ofOutcome]

/-! ## The translation -/

theorem trCode_cons (i : Instr) (is : List Instr) : trCode E (i :: is) = trI E i ++ trCode E is :=
  rfl

theorem trI_seg {i : Instr} (h : Tool.ctlOf i = none) : trI E i = [.prim 1 (segOp i)] := by
  simp only [trI, h]

theorem trI_imp {f : FuncIdx} (h : f.value.val < E.imps.length) :
    trI E (.call f) = [.prim 1 (splitOp (impArity E f.value.val)), .suspend f.value.val 1,
      .prim 2 mergeOp] := by
  simp only [trI, Tool.ctlOf, ite_eq_left h]

theorem trI_fn {f : FuncIdx} (h : ¬ f.value.val < E.imps.length) :
    trI E (.call f) = [.prim 1 (splitOp (fnArity E f.value.val)), .call f.value.val,
      .prim 2 mergeOp] := by
  simp only [trI, Tool.ctlOf, ite_eq_right h]

/-- Every translated instruction starts with a `prim 1`. -/
theorem trI_head (i : Instr) : ∃ op r, trI E i = .prim 1 op :: r := by
  unfold trI
  split
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- Translated code followed by `finOp` starts with a `prim 1`. -/
theorem trCode_head (code : List Instr) :
    ∃ op r, trCode E code ++ [.prim 1 finOp] = .prim 1 op :: r := by
  cases code with
  | nil => exact ⟨finOp, [], rfl⟩
  | cons i is =>
    obtain ⟨op, r, h⟩ := trI_head E i
    exact ⟨op, r ++ trCode E is ++ [.prim 1 finOp], by
      rw [trCode_cons, h]; simp only [List.cons_append, List.append_assoc]⟩

theorem impArity_eq {g : Nat} (h : g < E.imps.length) : impArity E g = (E.imps[g]'h).1 := by
  simp only [impArity, List.getElem?_eq_getElem h, Option.map_some, Option.getD_some]

theorem fnArity_eq {g : Nat} {fn : Tool.FnDef} (h : E.fns[g - E.imps.length]? = some fn) :
    fnArity E g = fn.nparams := by
  simp only [fnArity, h, Option.map_some, Option.getD_some]

theorem fnArity_none {g : Nat} (h : E.fns[g - E.imps.length]? = none) : fnArity E g = 0 := by
  simp only [fnArity, h, Option.map_none, Option.getD_none]

theorem trP_some {g : Nat} {fn : Tool.FnDef} (hg : ¬ g < E.imps.length)
    (h : E.fns[g - E.imps.length]? = some fn) : trP E g = some (1, trFn E fn) := by
  simp only [trP, ite_eq_left (Nat.le_of_not_lt hg), h, Option.map_some]

theorem trP_none {g : Nat} (h : E.fns[g - E.imps.length]? = none) : trP E g = none := by
  unfold trP
  split
  · simp only [h, Option.map_none]
  · rfl

theorem splitOp_ok {n : Nat} {v : KV} (h : n ≤ v.ops.length) :
    splitOp n [v] = [⟨(v.ops.take n).reverse, [], v.globals, v.mem⟩, { v with ops := v.ops.drop n }] := by
  simp only [splitOp, ite_eq_left h]

theorem splitOp_short {n : Nat} {v : KV} (h : ¬ n ≤ v.ops.length) : splitOp n [v] = [] := by
  simp only [splitOp, ite_eq_right h]

theorem segOp_some {i : Instr} {v v' : KV} (h : Tool.segCore i v = some v') : segOp i [v] = [v'] := by
  simp only [segOp, h]

theorem segOp_none {i : Instr} {v : KV} (h : Tool.segCore i v = none) : segOp i [v] = [] := by
  simp only [segOp, h]

/-- No frame of a stack waits on a `resume`: no tag is handled. -/
theorem split_none {t : Nat} : ∀ {L : List (SFrame KV)}, (∀ b ∈ L, b.wait = none) → split t L = none
  | [], _ => rfl
  | b :: L, h => by
    have hb : b.wait = none := h b (List.mem_cons_self ..)
    have ih : split t L = none := split_none fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
    simp only [split, hb, Option.bind_none, ih, Option.map_none]

end Silmaril.Proofs.Wasm.FX.Asyncify.Bridge
