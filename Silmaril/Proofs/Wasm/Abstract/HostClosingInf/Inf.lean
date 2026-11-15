module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Log
public import Silmaril.Games.Abstract.ModuleInf.Thms

/-!
# Productive runs inside one function, natively (proofs)

**Productivity of `InfL`.** Empty trees have no productive run (`infL_nil`), and a loop
whose iterations log no call and whose body has no productive run of its own claims no stream
(`infL_loop_silent`). In particular `loop { i }` for a flat non-call instruction `i` (such as
`br 0`, the loop that a greatest fixpoint over streams with an empty back edge would let claim
every stream) has no productive run (`infL_loop_op`).

**Assembly in the closure.** `wasmEvInfN` contains the resolved productive runs of a Wasm
body (`wasmEvInfN_of_infL`), is closed under a logged reach in a Wasm body with a resolved
prefix in front (`wasmEvInfN_of_reachL`, a descent by `descends_of_reachL`), and contains the
productive runs through unbounded recursion (`closeInf_le_wasmEvInfN`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInf

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

/-! ## Productivity -/

/-- **Empty trees have no productive run.** -/
theorem infL_nil {s : Store H} {f : Frame} {stk : List Val} {ω : Nat → OCall H} :
    ¬ InfL s f stk [] ω := nofun

/-- Empty trees log no call. -/
theorem evalL_nil_log {s : Store H} {f : Frame} {stk : List Val} {l : List (OCall H)}
    {r : Store H × Frame × Flow} (h : EvalL s f stk [] l r) : l = [] := by
  cases h
  rfl

/-- **A silent loop has no productive run**: a loop alone, whose iterations log no call and
whose body has no productive run of its own. -/
theorem infL_loop_silent {bt : BlockType} {body : List BExpr}
    (hsil : ∀ (s : Store H) f stk l r, EvalL s f stk body l r → l = [])
    (hno : ∀ (s : Store H) f stk (ω : Nat → OCall H), ¬ InfL s f stk body ω)
    {s : Store H} {f : Frame} {stk : List Val} {ω : Nat → OCall H} :
    ¬ InfL s f stk [.loop bt body] ω := by
  intro h
  generalize hes : [BExpr.loop bt body] = es at h
  induction h with
  | args | callK | opK | block | blockK | cond | arm | ifK => cases hes
  | loop _ h => cases hes; exact hno _ _ _ _ h
  | loopK _ _ h => cases hes; exact infL_nil h
  | loopBack _ _ _ ih => exact ih hes
  | loopInf st l _ _ hit hω =>
    cases hes
    have hl : ∀ n, l n = [] := fun n => by
      obtain ⟨vs, hb, -⟩ := hit n
      exact hsil _ _ _ _ _ hb
    obtain ⟨n, hn⟩ := hω.2 1
    have : (List.range n).flatMap l = [] := by simp [hl]
    rw [this] at hn
    simp at hn

/-- **`loop { i }` has no productive run** for a flat non-call instruction `i` with no
operand trees, such as `br 0`. -/
theorem infL_loop_op {bt : BlockType} {i : Instr} (hi : ∀ x, i ≠ .call x) {s : Store H}
    {f : Frame} {stk : List Val} {ω : Nat → OCall H} :
    ¬ InfL s f stk [.loop bt [.op i []]] ω := by
  refine infL_loop_silent (fun s f stk l r h => ?_) (fun s f stk ω h => ?_)
  · cases h with
    | argsAbort hargs _ => exact evalL_nil_log hargs
    | callRet => exact (hi _ rfl).elim
    | callThrow => exact (hi _ rfl).elim
    | opOk _ hargs _ hk => rw [evalL_nil_log hargs, evalL_nil_log hk]; rfl
    | opStop _ hargs _ _ => exact evalL_nil_log hargs
  · cases h with
    | args h => exact infL_nil h
    | callK => exact (hi _ rfl).elim
    | opK _ _ _ h => exact infL_nil h

/-! ## Assembly in the closure -/

/-- **A resolved productive run of a Wasm body** is a productive run of the invocation. -/
theorem wasmEvInfN_of_infL {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {fn : Func} {ω : Nat → OCall H} {ω' : Nat → Call (wasmHostSig H)}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (h : InfL s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) ω)
    (hs : Shape.SubstInf (Shape.close wasmHOpen) (fun i => (ω i).lift) ω') :
    ω' ∈ wasmEvInfN s (a, vs) :=
  Shape.mem_closeInfL_of_open ⟨fi, fn, ω, hf, hcode, h, rfl⟩ hs

/-- **A logged reach in a Wasm body**, its completed calls resolved to `q`, puts `q` in front
of the productive runs of the reached call. -/
theorem wasmEvInfN_of_reachL {y : (wasmOShape H).self.Op} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {l : List (OCall H)} {z : (wasmOShape H).self.Op}
    {q : List (Call (wasmHostSig H))} {ω : Nat → Call (wasmHostSig H)}
    (hf : y.2.2.funcs[y.1]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hr : ReachL y.2.2 (Frame.forCall fi.module y.2.1 fn.locals) [] (liftInstrs fn.body) l z)
    (hq : Shape.SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q)
    (h : ω ∈ wasmEvInfN z.2.2 (z.1, z.2.1)) : q ++ω ω ∈ wasmEvInfN y.2.2 (y.1, y.2.1) :=
  Shape.closeInfL_descends (descends_of_reachL hf hcode hty hr hq) h

/-- The productive runs through unbounded recursion are productive runs of the invocation. -/
theorem closeInf_le_wasmEvInfN {s : Store H} {a : Nat} {vs : List Val} :
    Shape.closeInf wasmHOpen a s vs ⊆ wasmEvInfN s (a, vs) :=
  Shape.closeInf_subset_closeInfL _ _ _ _ _

/-- **An infinite chain of logged reaches in Wasm bodies**, its resolved prefixes concatenating
to `ω`, is a productive run through unbounded recursion (`Shape.InfChain`). -/
theorem wasmEvInfN_of_chain (g : Nat → (wasmOShape H).self.Op)
    (q : Nat → List (Call (wasmHostSig H))) (ω : Nat → Call (wasmHostSig H))
    (hg : ∀ n, ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType)
      (l : List (OCall H)), (g n).2.2.funcs[(g n).1]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      ReachL (g n).2.2 (Frame.forCall fi.module (g n).2.1 fn.locals) [] (liftInstrs fn.body) l
        (g (n + 1)) ∧
      Shape.SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) (q n))
    (hc : Shape.StreamConcat q ω) : ω ∈ wasmEvInfN (g 0).2.2 ((g 0).1, (g 0).2.1) := by
  apply closeInf_le_wasmEvInfN
  refine ⟨g, q, rfl, fun n => ?_, hc.1, hc.2⟩
  obtain ⟨fi, fn, ps, rs, l, hf, hcd, hty, hr, hq⟩ := hg n
  exact descends_of_reachL hf hcd hty hr hq

/-- **The bridge** (deterministic profile, typed checked invocations, a host with typed answers
in the native host slice): every productive Core run of an invocation is a productive run of
the logged native semantics, with exactly its host events. -/
theorem coreInf_wasmEvInfN {o : SingleThreaded.GrowOracle} {host : HostSemantics H}
    (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat}
    {vs : List Val} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf (SingleThreaded.profile o) host (invoke s a vs) ω) :
    ω ∈ wasmEvInfN s (a, vs) :=
  coreInf_invokeL hT hH (fun y ω => ω ∈ wasmEvInfN y.2.2 (y.1, y.2.1))
    (fun _ _ _ _ _ hf hc hν hsub => wasmEvInfN_of_infL hf hc hν hsub)
    (fun _ _ _ _ _ _ _ _ _ hf hc hty hr hq hz => wasmEvInfN_of_reachL hf hc hty hr hq hz)
    (fun g q ω hg hc => wasmEvInfN_of_chain g q ω hg hc) hs hS hok h

end Silmaril.Proofs.Wasm.Abstract.HostClosingInf
