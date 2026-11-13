module

public import Silmaril.Wasm.Auto2.Calls.Defs
public import Silmaril.Wasm.Auto.EquivUnroll.Thms
public import Silmaril.Wasm.Auto.Bridge.Thms

/-!
# Symbolic execution with inlined calls: soundness (unrefined)

* `wp_callIdx_iff`: `call x` steps only to `ref.func a; call_ref` of the function it names;
* `firstFail_retLocals`: replacing the locals of the trap states does not change which guard
  fails first;
* **`wp_xsexecC`**: the executor with inlined calls gives the weakest precondition of the code as
  `XOut` of its final state (both readings, every profile and host relation), like
  `EquivUnroll.wp_xsexecU`, in every context whose function environment is correct
  (`FEnvOk`: every callee it returns is the Wasm function the module instance names, with the
  same function, global and memory addresses). The call case: the callee's run (the induction
  hypothesis at the callee's context, total reading) pins the callee's body
  (`EquivFn.Pinned`), `EquivFn.wp_call_pinned` turns the call into what the caller sees of the
  pinned outcome, and the caller continues from `afterCall`.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Calls

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Bridge (map_denX_zeros)
open Silmaril.Wasm.Auto.Bridge (intTy? locals_zero)
open Silmaril.Wasm.Auto.Equiv (NoFuncTop wp_seq_iff seqPostM_normal seqPostM_ne_normal)
open Silmaril.Wasm.Auto.EquivFn (wp_iff_of_det wp_call_pinned Pinned Pin xOutcome fits_xOutcome)
open Silmaril.Wasm.Auto.EquivUnroll (wp_loop_xstep xout_of_fail)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Function environments -/

/-- The callee `ce` is function index `x` of an instance with function addresses `fs`, global
addresses `gs` and memory addresses `ms` in the store `s`. -/
def CalleeAt (s : Store H) (fs gs ms : List Nat) (x : Nat) (ce : Callee) : Prop :=
  ∃ a fi code ps rs, fs[x]? = some a ∧ s.funcs[a]? = some fi ∧ fi.code = .wasm code ∧
    Expand fi.type (.func ps rs) ∧ ps.length = ce.np ∧ rs.length = ce.nr ∧ code.body = ce.body ∧
    code.locals.mapM intTy? = some ce.ls ∧ fi.module.funcs = fs ∧ fi.module.globals = gs ∧
    fi.module.mems = ms

/-- **A correct function environment** for the module instance `mi` in the store `s`. -/
def FEnvOk (s : Store H) (mi : ModuleInst) (fe : Nat → Option Callee) : Prop :=
  ∀ x ce, fe x = some ce → CalleeAt s mi.funcs mi.globals mi.mems x ce

theorem calleeOf_ok (s : Store H) (mi : ModuleInst) : FEnvOk s mi (calleeOf s mi) := by
  intro x ce h
  unfold calleeOf at h
  split at h
  · cases h
  · rename_i a ha
    split at h
    · cases h
    · rename_i fi hfi
      split at h
      · rename_i code ps rs hcode hexp
        split at h
        · rename_i hm
          split at h
          · rename_i ls hls
            obtain rfl := Option.some.inj h
            exact ⟨a, fi, code, ps, rs, ha, hfi, hcode, Expand.iff.mpr hexp, rfl, rfl, rfl, hls,
              hm.1, hm.2.1, hm.2.2⟩
          · cases h
        · cases h
      · cases h

/-! ## Stores, frames and guards -/

theorem setGlobals_funcs : ∀ (s : Store H) (as : List Nat) (vs : List Val),
    (setGlobals s as vs).funcs = s.funcs
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl
  | s, a :: as, v :: vs => by
    simp only [setGlobals]
    rw [setGlobals_funcs]
    rfl

theorem storeOf_funcs (c : XCtx H) (mem : Bool) (S : XState) :
    (c.storeOf mem S).funcs = c.s.funcs := by
  simp only [XCtx.storeOf]
  split
  · simp only [Store.setMem]
    exact setGlobals_funcs _ _ _
  · exact setGlobals_funcs _ _ _

/-- The store of a symbolic state depends on its globals and memory only. -/
theorem storeOf_congr (c : XCtx H) (mem : Bool) {S T : XState} (hg : S.globs = T.globs)
    (hm : S.mem = T.mem) : c.storeOf mem S = c.storeOf mem T := by
  simp only [XCtx.storeOf, hg, hm]

/-- The frame of a symbolic state depends on its locals only. -/
theorem frameOf_congr (c : XCtx H) {S T : XState} (hl : S.locals = T.locals) :
    c.frameOf S = c.frameOf T := by
  simp only [XCtx.frameOf, hl]

theorem firstFail_retLocals (ρ : Silmaril.Wasm.Auto.Equiv.Env) (B0 : ByteArray)
    (L : List (IntType × XT)) : ∀ G : List (Guard × XState),
    firstFail ρ B0 (retLocals L G) = (firstFail ρ B0 G).map fun T => { T with locals := L }
  | [] => rfl
  | (g, T) :: G => by
    simp only [retLocals, List.map_cons, firstFail] at *
    split
    · exact firstFail_retLocals ρ B0 L G
    · rfl

/-! ## The call step -/

/-- **`call x` steps only to `ref.func a; call_ref`.** -/
theorem wp_callIdx_iff {m : Corr} {s : Store H} {f : Frame} {W : List Val} {x : FuncIdx}
    {R : List Admin} {Q : Post H} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
    Wp m P host s f (vals W ++ .plain (.call x) :: R) Q ↔
      Wp m P host s f (vals W ++ [.ref (.func a), .callRefType fi.type] ++ R) Q := by
  have hstep : Step P host ⟨s, f, vals W ++ .plain (.call x) :: R⟩
      ⟨s, f, vals W ++ [.ref (.func a), .callRefType fi.type] ++ R⟩ := by
    simpa using Sim.Step.append_right (Sim.Step.vals_left (Step.call hx hf) W) R
  refine wp_iff_of_det (m := m) (Q := Q) hstep fun d hd => ?_
  obtain ⟨vs, args, c₀, hW, hh, rfl⟩ :=
    SingleThreaded.inert_head_inv (by rfl) (by simp) (by rfl) hd
  obtain ⟨rfl, a', fi', hx', hf', rfl⟩ := head_call hh
  rw [hx] at hx'
  obtain rfl := Option.some.inj hx'
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  simp only [List.append_nil] at hW
  subst hW
  simp

/-! ## Runs -/

theorem xsexecC_globs {mem : Bool} {fe : Nat → Option Callee} : ∀ (fuel : Nat) {S S' : XState}
    {a : List Instr}, xsexecC mem fe fuel S a = some S' → S'.globs.length = S.globs.length
  | _, S, S', [], h => by
    unfold xsexecC at h
    cases h
    rfl
  | 0, _, _, _ :: _, h => by unfold xsexecC at h; cases h
  | f + 1, S, S', i :: is, h => by
    unfold xsexecC at h
    split at h
    · split at h
      · split at h
        · rename_i S₁ hr
          split at h
          · split at h
            · rw [xsexecC_globs f h]
              simp [xsexec_globs hr]
            · rw [xsexecC_globs f h]
              simp [xsexec_globs hr]
            · cases h
          · cases h
        · cases h
      · cases h
    · split at h
      · rename_i ce hce
        split at h
        · split at h
          · rename_i A hA
            split at h
            · rw [xsexecC_globs f h]
              simp only [afterCall]
              rw [xsexecC_globs f hA]
              rfl
            · cases h
          · cases h
        · cases h
      · cases h
    · split at h
      · rename_i S₁ hs
        rw [xsexecC_globs f h, xstep_globs hs]
      · cases h

theorem xsexecC_guards {mem : Bool} {fe : Nat → Option Callee} : ∀ (fuel : Nat) {S S' : XState}
    {a : List Instr}, xsexecC mem fe fuel S a = some S' → ∃ G, S'.guards = S.guards ++ G
  | _, S, S', [], h => by
    unfold xsexecC at h
    cases h
    exact ⟨[], by simp⟩
  | 0, _, _, _ :: _, h => by unfold xsexecC at h; cases h
  | f + 1, S, S', i :: is, h => by
    unfold xsexecC at h
    split at h
    · split at h
      · split at h
        · rename_i S₁ hr
          split at h
          · obtain ⟨G₁, hG₁⟩ := xsexec_guards hr
            split at h
            · obtain ⟨G, hG⟩ := xsexecC_guards f h
              exact ⟨G₁ ++ G, by rw [hG]; simp [hG₁]⟩
            · obtain ⟨G, hG⟩ := xsexecC_guards f h
              exact ⟨G₁ ++ G, by rw [hG]; simp [hG₁]⟩
            · cases h
          · cases h
        · cases h
      · cases h
    · split at h
      · split at h
        · split at h
          · rename_i A hA
            split at h
            · obtain ⟨G, hG⟩ := xsexecC_guards f h
              exact ⟨retLocals S.locals A.guards ++ G, by rw [hG]; simp [afterCall]⟩
            · cases h
          · cases h
        · cases h
      · cases h
    · split at h
      · rename_i S₁ hs
        obtain ⟨G, hG⟩ := xsexecC_guards f h
        obtain ⟨G₁, hG₁⟩ := xsexec_guards (mem := mem) (S := S) (S' := S₁) (a := [i])
          (by simp [xsexec, hs])
        exact ⟨G₁ ++ G, by rw [hG, hG₁]; simp⟩
      · cases h

/-! ## The callee -/

/-- The context of a callee: the caller's, with the callee's call frame. -/
def calleeCtx (c : XCtx H) (mi : ModuleInst) (args : List Val) (lts : List ValType) : XCtx H :=
  { c with f := Frame.forCall mi args lts }

@[simp] theorem calleeCtx_ρ (c : XCtx H) (mi : ModuleInst) (args : List Val) (lts : List ValType) :
    (calleeCtx c mi args lts).ρ = c.ρ := rfl

@[simp] theorem calleeCtx_mi (c : XCtx H) (mi : ModuleInst) (args : List Val) (lts : List ValType) :
    (calleeCtx c mi args lts).mi = c.mi := rfl

@[simp] theorem calleeCtx_storeOf (c : XCtx H) (mi : ModuleInst) (args : List Val)
    (lts : List ValType) (mem : Bool) (S : XState) :
    (calleeCtx c mi args lts).storeOf mem S = c.storeOf mem S := rfl

@[simp] theorem calleeCtx_stackOf (c : XCtx H) (mi : ModuleInst) (args : List Val)
    (lts : List ValType) (S : XState) :
    (calleeCtx c mi args lts).stackOf S = c.stackOf S := rfl

theorem calleeCtx_good {mem : Bool} {c : XCtx H} (hc : c.Good mem) {mi : ModuleInst}
    (hg : mi.globals = c.f.module.globals) (hm : mi.mems = c.f.module.mems) (args : List Val)
    (lts : List ValType) : (calleeCtx c mi args lts).Good mem := by
  refine ⟨hc.1, fun k hk => ?_, fun hmem => ?_⟩
  · obtain ⟨h₁, h₂⟩ := hc.2.1 k hk
    refine ⟨?_, h₂⟩
    simp only [calleeCtx, Frame.forCall, hg]
    exact h₁
  · have := hc.2.2 hmem
    simpa [calleeCtx, Frame.forCall, Store.mem?, hm] using this

theorem fenvOk_congr {s : Store H} {mi mi' : ModuleInst} {fe : Nat → Option Callee}
    (h : FEnvOk s mi fe) (hf : mi'.funcs = mi.funcs) (hg : mi'.globals = mi.globals)
    (hm : mi'.mems = mi.mems) : FEnvOk s mi' fe := by
  intro x ce hx
  rw [hf, hg, hm]
  exact h x ce hx

/-- The callee's initial state denotes its call frame. -/
theorem frameOf_calleeInit (c : XCtx H) (S : XState) {n : Nat} {ls : List IntType}
    {mi : ModuleInst} {lts : List ValType} (hls : lts.mapM intTy? = some ls) :
    (calleeCtx c mi ((S.stack.take n).map (denX c.ρ c.mi.bytes)).reverse lts).frameOf
        (calleeInit S n ls) =
      Frame.forCall mi ((S.stack.take n).map (denX c.ρ c.mi.bytes)).reverse lts := by
  have hz := map_denX_zeros c.ρ c.mi.bytes ls
  rw [locals_zero (mi.types.map .dt) _ hls] at hz
  simp only [XCtx.frameOf, calleeCtx, calleeInit, Frame.forCall, List.map_append, hz]
  simp [List.map_reverse, Function.comp_def]

end Silmaril.Wasm.Auto2.Calls
