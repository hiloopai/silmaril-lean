module

public import Silmaril.Proofs.X86.Sep.CSpec.Template
public import Silmaril.X86.Sep.SysV.Thms
public import Silmaril.Machine.Abi.SpecNotions.Thms
/-!
# Proofs: `FnSpec` embeds into `CSpec`

Behind `Silmaril/Machine/X86/Sep/CSpec/Thms.lean`. Imports only headers (and the sibling proof
module `Template`).

* The integer shape: `argsPtL_int` (word arguments are register atoms), `unusedGp_intPlan`,
  `unusedX_intPlan`, `otherGp_intPlan`, `otherX_intPlan`, `stackArgsAnyL_int`.
* **`argsIn_intShape`**: `ArgsIn (intShape args) fr = ↑ₓ(SysVRegs args) ∗ₓ xmmsAny allXRegs`,
  and **`retOut_intShape`**: the exit side with `rax ↦ v`.
* **`toC_pre`**: the precondition of `S.toC` is `FnSpec.SysVPre` with all XMM registers;
  **`toC_post`**: `FnSpec.SysVPost` with all XMM registers entails `S.toC`'s postcondition.
* **`sat_toC_of_sat`**: `S.Sat Open.isa C entry → S.toC.Sat M ↑ₓC entry` for every XMM machine
  extending `Open9`; `toC_sub`: `toC` preserves refinement.
* `intPlan_eq_plan`: `intPlan` is what `Abi.plan` computes for up to six 64-bit INTEGER
  arguments and an INTEGER result (no classification of our own).
* `strlen_csat`: libmini's `strlen` (`SpecNotions.strlen_spine`) meets `scanSpec.toC` on
  `Sse9.isa`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SepCSpec

open Silmaril.X86 (Reg XReg Word Byte MState)
open Silmaril.X86.Sse9 (Xmm XState)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Xmm
open Silmaril.X86.Sep.Plan
open Silmaril.X86.Sep.CSpec
open Silmaril.Machine.SystemV.Abi (Chunk Argument CallPlan)

/-! ## Registers with values -/

/-- Registers paired with values, as far as both lists go. -/
def zipRegs : List Reg → List Word → SProp
  | r :: rs, v :: vs => regPt r v ∗ zipRegs rs vs
  | _, _ => emp

theorem regsWith_split : ∀ (rs : List Reg) (vs : List Word),
    regsWith rs vs = (zipRegs rs vs ∗ regsAny (rs.drop vs.length))
  | [], vs => by
    cases vs <;> simp [regsWith, zipRegs, regsAny, sep_emp]
  | r :: rs, [] => by
    simp only [regsWith, zipRegs, regsAny, List.length_nil, List.drop_zero, emp_sep]
  | r :: rs, v :: vs => by
    simp only [regsWith, zipRegs, List.length_cons, List.drop_succ_cons]
    rw [regsWith_split rs vs, sep_assoc]

theorem regsAny_append : ∀ (a b : List Reg), regsAny (a ++ b) = (regsAny a ∗ regsAny b)
  | [], b => by simp [regsAny, regsWith, emp_sep]
  | r :: a, b => by
    have := regsAny_append a b
    simp only [regsAny, regsWith, List.cons_append] at this ⊢
    rw [this, sep_assoc]

/-! ## The integer shape -/

theorem argsPtL_int (fr : Frame) : ∀ (rs : List Reg) (ws : List Word),
    argsPtL fr ((rs.zip ws).map fun p => intArgument p.1)
      ((rs.zip ws).map fun p => wordBytes p.2) = ↑ₓ(zipRegs rs ws)
  | [], ws => by simp [argsPtL, zipRegs, lift_emp]
  | r :: rs, [] => by simp [argsPtL, zipRegs, lift_emp]
  | r :: rs, w :: ws => by
    simp only [List.zip_cons_cons, List.map_cons, argsPtL, zipRegs, lift_sep]
    rw [argsPtL_int fr rs ws]
    simp only [argPt, intArgument, chunksPt_gp8]

theorem stackArgsAnyL_int (fr : Frame) : ∀ (L : List (Reg × Word)),
    stackArgsAnyL fr (L.map fun p => intArgument p.1) (L.map fun p => wordBytes p.2) = xemp
  | [] => by simp [stackArgsAnyL]
  | p :: L => by
    simp only [List.map_cons, stackArgsAnyL]
    rw [stackArgsAnyL_int fr L]
    exact xemp_sep xemp

theorem regChunks_int (L : List (Reg × Word)) (res : Silmaril.Machine.SystemV.Abi.Return)
    (a b c d : Nat) (e : Option Nat) :
    regChunks ⟨L.map (fun p => intArgument p.1), res, a, b, c, d, e⟩ =
      L.map fun p => (⟨0, 8, .gp p.1⟩ : Chunk) := by
  simp only [regChunks]
  induction L with
  | nil => rfl
  | cons p L ih => rw [List.map_cons, List.flatMap_cons, ih]; rfl

theorem gpRegs_int (L : List (Reg × Word)) :
    gpRegs (L.map fun p => (⟨0, 8, .gp p.1⟩ : Chunk)) = L.map Prod.fst := by
  induction L with
  | nil => rfl
  | cons p L ih => simp_all [gpRegs]

theorem xRegs_int (L : List (Reg × Word)) :
    xRegs (L.map fun p => (⟨0, 8, .gp p.1⟩ : Chunk)) = [] := by
  induction L with
  | nil => rfl
  | cons p L ih => simp_all [xRegs]

theorem map_fst_zip_take : ∀ (rs : List Reg) (ws : List Word),
    (rs.zip ws).map Prod.fst = rs.take ws.length
  | [], _ => by simp
  | _ :: _, [] => by simp
  | r :: rs, _ :: ws => by simp [map_fst_zip_take rs ws]

theorem filter_argRegs (k : Nat) :
    callerSavedGp.filter (fun r => decide (r ∉ argRegs.take k ++ [] ++ [])) =
      argRegs.drop k ++ scratchRegs := by
  obtain _ | _ | _ | _ | _ | _ | k := k
  all_goals try decide
  rw [List.take_of_length_le (by simp [argRegs]), List.drop_of_length_le (by simp [argRegs])]
  decide

theorem unusedGp_intPlan (args : List Word) :
    unusedGp (intPlan args) = argRegs.drop args.length ++ scratchRegs := by
  have : usedGp (intPlan args) = argRegs.take args.length ++ [] ++ [] := by
    simp only [usedGp, intPlan, regChunks_int, gpRegs_int, map_fst_zip_take]
  simp only [unusedGp, this, filter_argRegs]

theorem unusedX_intPlan (args : List Word) : unusedX (intPlan args) = allXRegs := by
  have : usedX (intPlan args) = [] := by simp only [usedX, intPlan, regChunks_int, xRegs_int]
  simp [unusedX, this]

theorem otherGp_intPlan (args : List Word) :
    otherGp (intPlan args) = [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] := by
  show callerSavedGp.filter (fun r => decide (r ∉ resultGp (.direct [⟨0, 8, .gp .rax⟩]))) = _
  decide

theorem otherX_intPlan (args : List Word) : otherX (intPlan args) = allXRegs := by
  show allXRegs.filter (fun r => decide (r ∉ resultX (.direct [⟨0, 8, .gp .rax⟩]))) = _
  decide

/-- **The integer entry placement is `SysVRegs`**, with all XMM registers. -/
theorem argsIn_intShape (args : List Word) (fr : Frame) :
    ArgsIn (intShape args) fr = (↑ₓ(SysVRegs args) ∗ₓ xmmsAny allXRegs) := by
  have hs : sretPt (intShape args).plan.result (intShape args).sret = xemp := rfl
  have ha : alPt (intShape args).plan = xemp := rfl
  simp only [ArgsIn, hs, ha]
  simp only [intShape, argsPt, intPlan, argsPtL_int] at *
  rw [show unusedGp ⟨(argRegs.zip args).map (fun p => intArgument p.1),
      .direct [⟨0, 8, .gp .rax⟩], 0, 16, (argRegs.zip args).length, 0, none⟩ =
      argRegs.drop args.length ++ scratchRegs from unusedGp_intPlan args,
    show unusedX ⟨(argRegs.zip args).map (fun p => intArgument p.1),
      .direct [⟨0, 8, .gp .rax⟩], 0, 16, (argRegs.zip args).length, 0, none⟩ =
      allXRegs from unusedX_intPlan args]
  simp only [SysVRegs, regsWith_split, regsAny_append, lift_sep, xemp_sep]
  ac_rfl

/-- **The integer exit placement** for the result word `v`. -/
theorem retOut_intShape (args : List Word) (fr : Frame) (v : Word) :
    RetOut (intShape args) fr (wordBytes v) =
      (↑ₓ(regPt .rax v ∗ regsAny [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11]) ∗ₓ
        xmmsAny allXRegs) := by
  have hr : retPt (intShape args).plan.result (intShape args).sret (wordBytes v) =
      ↑ₓ(regPt .rax v) := chunksPt_gp8 .rax v
  simp only [RetOut, hr]
  rw [show (intShape args).plan = intPlan args from rfl, otherGp_intPlan, otherX_intPlan]
  simp only [intShape, intPlan, stackArgsAnyL_int, lift_sep, xemp_sep]
  ac_rfl

/-! ## `FnSpec.toC` -/

/-- **The precondition of `S.toC`** is `S`'s System V precondition with all XMM registers. -/
theorem toC_pre (S : FnSpec) (x : S.Arg) (entry : Word) (fr : Frame) :
    S.toC.Pre x entry fr = (↑ₓ(S.SysVPre x entry fr.sp fr.ret) ∗ₓ xmmsAny allXRegs) := by
  simp only [CSpec.Pre, CSpec.Entry, EntryOf, FnSpec.toC, argsIn_intShape, CtlIn,
    FnSpec.SysVPre, FnSpec.SysVEntry, lift_sep]
  ac_rfl

/-- **`S`'s System V postcondition with all XMM registers gives `S.toC`'s.** -/
theorem toC_post (S : FnSpec) (x : S.Arg) (fr : Frame) :
    (↑ₓ(S.SysVPost x fr.sp fr.ret) ∗ₓ xmmsAny allXRegs) ⊢ₓ S.toC.Post x fr := by
  simp only [FnSpec.SysVPost, lift_sexists, xsexists_sep]
  refine xsexists_elim fun v => xsexists_intro (wordBytes v) ?_
  simp only [CSpec.Exit, ExitOf, FnSpec.toC, retOut_intShape, CtlOut, FnSpec.SysVExit,
    SysVRet]
  refine xentails_trans ?_ (xsep_mono (xentails_refl _)
    (xsexists_intro v (fun g hg => (xspure_sep_apply _ _ _).2 ⟨rfl, hg⟩)))
  simp only [clobberedRegs, regsAny, regsWith, lift_sep]
  exact xentails_of_eq (by ac_rfl)

/-- **Every `FnSpec` proof is a `CSpec` proof** on every XMM machine extending `Open9`. -/
theorem sat_toC_of_sat {M : Silmaril.X86.SegVC.Isa XState} [ExtendsOpen9X M] {S : FnSpec}
    {C : SProp} {entry : Word} (hS : S.Sat Silmaril.X86.Open.isa C entry) : S.toC.Sat M ↑ₓC entry := by
  intro n x fr hA hst
  have h := (xstriple_of_triple (M := M) (n := n) (hS x fr.sp fr.ret hA hst)).frame
    (xmmsAny allXRegs)
  refine XSTriple.conseq ?_ h ?_
  · rw [toC_pre S x entry fr, lift_sep]
    exact xentails_of_eq (by ac_rfl)
  · rw [lift_sep, xsep_assoc]
    exact xsep_mono (xentails_refl _) (toC_post S x fr)

/-- `toC` preserves refinement. -/
theorem toC_sub {S T : FnSpec} (h : S.Sub T) : S.toC.Sub T.toC := by
  refine ⟨fun y => ?_⟩
  obtain ⟨x, hargs, R, hpre, hpost⟩ := h.arg y
  refine ⟨x, by simp [FnSpec.toC, hargs], h.stack, fun _ => ⟨↑ₓR, ?_, fun rb => ?_⟩⟩
  · simp only [FnSpec.toC]
    rw [← lift_sep]
    exact lift_mono hpre
  · simp only [FnSpec.toC, xsexists_sep]
    refine xsexists_mono fun v => ?_
    rw [xsep_assoc, ← lift_sep]
    exact xsep_mono (xentails_refl _) (lift_mono (hpost v))

/-! ## `intPlan` is `Abi.plan`'s -/

/-- **`intPlan` is what `Silmaril.Machine.SystemV.Abi.plan` computes** for up to six 64-bit
INTEGER arguments and a 64-bit INTEGER result (fixed arity). -/
theorem intPlan_eq_plan (args : List Word) (h : args.length ≤ 6) :
    (Silmaril.Machine.SystemV.Abi.plan {} (List.replicate args.length int64Object)
      (some int64Object) args.length false).toOption = some (intPlan args) := by
  match args, h with
  | [], _ => decide
  | [_], _ =>
    simp only [intPlan, argRegs, List.zip_cons_cons, List.zip_nil_right, List.map_cons,
      List.map_nil, List.length_cons, List.length_nil]
    decide
  | [_, _], _ =>
    simp only [intPlan, argRegs, List.zip_cons_cons, List.zip_nil_right, List.map_cons,
      List.map_nil, List.length_cons, List.length_nil]
    decide
  | [_, _, _], _ =>
    simp only [intPlan, argRegs, List.zip_cons_cons, List.zip_nil_right, List.map_cons,
      List.map_nil, List.length_cons, List.length_nil]
    decide
  | [_, _, _, _], _ =>
    simp only [intPlan, argRegs, List.zip_cons_cons, List.zip_nil_right, List.map_cons,
      List.map_nil, List.length_cons, List.length_nil]
    decide
  | [_, _, _, _, _], _ =>
    simp only [intPlan, argRegs, List.zip_cons_cons, List.zip_nil_right, List.map_cons,
      List.map_nil, List.length_cons, List.length_nil]
    decide
  | [_, _, _, _, _, _], _ =>
    simp only [intPlan, argRegs, List.zip_cons_cons, List.zip_nil_right, List.map_cons,
      List.map_nil, List.length_cons, List.length_nil]
    decide

/-! ## Examples: the template's register bookkeeping on plans computed by `Abi.plan`

Each register is owned once at entry and once at exit: the registers a plan uses (argument
chunks, `rdi` for sret, `rax` for variadic `al`) are exactly the ones left out of
`unusedGp`/`unusedX`, and the result registers are left out of `otherGp`/`otherX`. -/

namespace Examples

open Silmaril.Machine.SystemV.Abi (Object plan)

/-- A 32-byte MEMORY-class object (returned through sret). -/
def big : Object := ⟨32, 8, [.memory]⟩

/-- A `double`. -/
def dbl : Object := ⟨8, 8, [.sse]⟩

/-- `big f(big)`: `rdi` carries the sret pointer; `rax` returns it. -/
theorem sret_regs : (plan {} [big] (some big) 1 false).toOption.map
    (fun p => (usedGp p, unusedGp p, otherGp p)) =
    some ([.rdi], [.rsi, .rdx, .rcx, .r8, .r9, .rax, .r10, .r11],
      [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11]) := by decide

/-- `void f(int64, int64, int64, ...)` with seven variadic words: six GP argument registers
and `al`; `r10`, `r11` are unused. -/
theorem variadic_regs : (plan {} (List.replicate 10 int64Object) none 3 true).toOption.map
    (fun p => (usedGp p, unusedGp p, p.variadicAL)) =
    some ([.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rax], [.r10, .r11], some 0) := by decide

/-- `double f(double, int64)`: `xmm0` in, `xmm0` out. -/
theorem sse_regs : (plan {} [dbl, int64Object] (some dbl) 2 false).toOption.map
    (fun p => (usedX p, unusedX p == allXRegs.drop 1, otherX p == allXRegs.drop 1)) =
    some ([xregOfIdx 0], true, true) := by decide

end Examples

/-! ## Acceptance: libmini's `strlen` on `Sse9` -/

open Silmaril.X86.Stencils.ByteLoop Silmaril.X86.Ladder.LibMini in
/-- **libmini's `strlen` meets `scanSpec.toC` on `Sse9.isa`**, from the author spec of
`SpecNotions.strlen_spine`, with no re-proof. -/
theorem strlen_csat (entry : Word) :
    scanSpec.toC.Sat Silmaril.X86.Sse9.isa ↑ₓ(codePt entry.toNat strlenCode) entry :=
  sat_toC_of_sat (Silmaril.Machine.Abi.SpecNotions.strlen_spine {} {} entry).1

end Silmaril.Proofs.X86.SepCSpec
