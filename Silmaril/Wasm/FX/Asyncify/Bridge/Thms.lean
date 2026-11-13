module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.Main

/-!
# The asyncify tool as an instance of the family: results

The header of `Defs` (the translation `trP`, the host `kHost`, the observation maps).

* **`tool_src_kernel`**: for a well-formed program of the tool (statement form) and a call of a
  defined function, under every host, the tool's source behaviours (the frame machine, import
  calls answered by the host, final host state observed) are the behaviours of the translated
  kernel program `trP P.env` closed by `kHost` (`hsstep`), host states observed (`hSrcObs`),
  read back by `obsOut`. Proof: a stuttering simulation (`Bridge.bridge_sim`), one to three
  kernel steps per tool step, across the two observation types.
* `tool_family o`: with `host_correct_obs`, the tool's source behaviours are also those of the
  family's host instance on `trP P.env`, for every optimization on its fragment: the target
  `compPO o (trP P.env)` under the host protocol (`htstep`). `tool_whole` (the tool's own
  instrumentation, every call) and `tool_analyzed` (the computed suspension analysis of the
  translated program) need no hypothesis.
* **`asyncify_square`**: with the tool's own correctness `asyncify_beh`, the asyncified program
  under the tool's host protocol has the behaviours of the family's whole-program host target on
  the translated program. Tool and family agree on the source (`tool_src_kernel`) and on the
  target.
* **`asyncify_beh_via_family`**: `asyncify_beh` **follows from `host_correct_obs`** and the
  open target `Task.tool_tgt_sim` (a stuttering simulation from the family's host target on
  `trP P.env` to the asyncified program under the protocol; not proved). The source half of
  that derivation is `tool_src_kernel`, proved.
* `straight_of_wf`: statement-form programs have no `return` and no `if`, the hypothesis of
  the simulation (`Straight`); the general form `tool_in_kernel` holds for every machine
  program without them.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Bridge

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify.Host
open Silmaril.Proofs.Wasm.FX.Asyncify.Bridge (cfg0)

variable {σ : Type}

/-- **The tool's frame machine in the kernel**: every machine program without `return` and
`if`, every call of a defined function, every host. -/
theorem tool_in_kernel (E : Tool.Env) (hE : Straight E) (H : Tool.Host σ) {e : Nat}
    {fn : Tool.FnDef} (he : E.imps.length ≤ e) (hfn : E.fns[e - E.imps.length]? = some fn)
    (args : List Tool.W) (s : σ) :
    Tool.beh (Tool.srcStep E H) (⟨[Tool.entry e fn args], [], fun _ => 0⟩, s) =
      obsOut '' hSrcObs (trP E) kTest (kHost E H) s e (kArgs args) :=
  Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.src_beh_kernel E H hE he hfn args s

/-- Statement-form programs have no `return` and no `if`. -/
theorem straight_of_wf {P : Tool.Prog} (hP : P.WF) : Straight P.env :=
  Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.straight_of_wf hP

/-- **The tool's source system is the family's source**: the translated kernel closed by the
tool's host, host states observed. -/
theorem tool_src_kernel (P : Tool.Prog) (hP : P.WF) (H : Tool.Host σ) {e : Nat}
    {fn : Tool.FnSrc} (hfn : P.fnAt e = some fn) (args : List Tool.W) (s : σ) :
    Tool.beh (Tool.srcStep P.env H) (Tool.srcCfg e fn args, s) =
      obsOut '' hSrcObs (trP P.env) kTest (kHost P.env H) s e (kArgs args) :=
  tool_in_kernel P.env (straight_of_wf hP) H (Tool.Prog.fnAt_ge hfn) (Tool.Prog.env_fn hfn) args s

/-- **The tool's source is the source of the family's host instance**, for every optimization on
its fragment: its behaviours are those of `compPO o (trP P.env)` under the host protocol. -/
theorem tool_family (o : Opt) (P : Tool.Prog) (hP : P.WF) (hD : o.Dom (trP P.env))
    (H : Tool.Host σ) {e : Nat} {fn : Tool.FnSrc} (hfn : P.fnAt e = some fn) (args : List Tool.W)
    (s : σ) :
    Tool.beh (Tool.srcStep P.env H) (Tool.srcCfg e fn args, s) =
      obsOut '' hTgtObs (compPO o (trP P.env)) kTest (kHost P.env H) s e (kArgs args) := by
  rw [tool_src_kernel P hP H hfn args s,
    host_correct_obs o (trP P.env) hD kTest (kHost P.env H) s e (kArgs args)]

/-- The tool's instrumentation (every call site) in the family: no hypothesis. -/
theorem tool_whole (P : Tool.Prog) (hP : P.WF) (H : Tool.Host σ) {e : Nat} {fn : Tool.FnSrc}
    (hfn : P.fnAt e = some fn) (args : List Tool.W) (s : σ) :
    Tool.beh (Tool.srcStep P.env H) (Tool.srcCfg e fn args, s) =
      obsOut '' hTgtObs (compPO .whole (trP P.env)) kTest (kHost P.env H) s e (kArgs args) :=
  tool_family .whole P hP (whole_dom _) H hfn args s

/-- The computed suspension analysis of the translated program: no hypothesis. -/
theorem tool_analyzed (P : Tool.Prog) (hP : P.WF) (n : Nat) (H : Tool.Host σ) {e : Nat}
    {fn : Tool.FnSrc} (hfn : P.fnAt e = some fn) (args : List Tool.W) (s : σ) :
    Tool.beh (Tool.srcStep P.env H) (Tool.srcCfg e fn args, s) =
      obsOut '' hTgtObs (compPO (Selective.analyzed (trP P.env) n) (trP P.env)) kTest
        (kHost P.env H) s e (kArgs args) :=
  tool_family (Selective.analyzed (trP P.env) n) P hP (Selective.analyze_sound (trP P.env) n) H hfn
    args s

/-- **The square**: the asyncified program under the tool's protocol has the behaviours of the
family's whole-program host target on the translated program (by `asyncify_beh`). -/
theorem asyncify_square (P : Tool.Prog) (hP : P.WF) (H : Tool.Host σ) {e : Nat}
    {fn : Tool.FnSrc} (hfn : P.fnAt e = some fn) (args : List Tool.W)
    (hargs : args.length = fn.nparams) (s : σ)
    (hbound : Tool.DepthBound P H (Tool.srcCfg e fn args, s)) :
    Tool.beh (Tool.tgtStep (Tool.asyncifyProg P) H) (Tool.tgtSt P e fn args s) =
      obsOut '' hTgtObs (compPO .whole (trP P.env)) kTest (kHost P.env H) s e (kArgs args) := by
  rw [← Tool.asyncify_beh P hP H hfn args hargs s hbound]
  exact tool_whole P hP H hfn args s

/-- **Open target**: the target half of the tool as an instance. For a well-formed program and a
call within `DepthBound`, a stuttering simulation from the family's whole-program host target on
`trP P.env` (host states observed, read as tool observations) to the asyncified program under
the tool's host protocol, relating the initial configurations. Not proved; it would replace the
tool's own simulation (`asyncify_beh`) by the family's (`host_correct_obs`). -/
def Task.tool_tgt_sim : Prop :=
  ∀ (σ : Type) (P : Tool.Prog), P.WF → ∀ (H : Tool.Host σ) (e : Nat) (fn : Tool.FnSrc)
    (args : List Tool.W) (s : σ), P.fnAt e = some fn → args.length = fn.nparams →
    Tool.DepthBound P H (Tool.srcCfg e fn args, s) →
    ∃ R : TCfg KV × σ → Tool.TSt σ → Prop,
      SimRel (mapObs toolOut (observe (htstep (compPO .whole (trP P.env)) kTest (kHost P.env H))))
        (asRes (Tool.tgtStep (Tool.asyncifyProg P) H)) R ∧
      R (tInit e (kArgs args), s) (Tool.tgtSt P e fn args s)

/-- **`asyncify_beh` from the family**: given the target half (`Task.tool_tgt_sim`), the tool's
correctness follows from `host_correct_obs` and the source half `tool_src_kernel`. -/
theorem asyncify_beh_via_family (hT : Task.tool_tgt_sim) (P : Tool.Prog) (hP : P.WF)
    (H : Tool.Host σ) {e : Nat} {fn : Tool.FnSrc} (hfn : P.fnAt e = some fn) (args : List Tool.W)
    (hargs : args.length = fn.nparams) (s : σ)
    (hbound : Tool.DepthBound P H (Tool.srcCfg e fn args, s)) :
    Tool.beh (Tool.srcStep P.env H) (Tool.srcCfg e fn args, s) =
      Tool.beh (Tool.tgtStep (Tool.asyncifyProg P) H) (Tool.tgtSt P e fn args s) := by
  obtain ⟨R, hR, hi⟩ := hT σ P hP H e fn args s hfn hargs hbound
  have h1 : beh (mapObs toolOut (observe (htstep (compPO .whole (trP P.env)) kTest
      (kHost P.env H)))) (tInit e (kArgs args), s) =
      beh (asRes (Tool.tgtStep (Tool.asyncifyProg P) H)) (Tool.tgtSt P e fn args s) :=
    beh_eq_of_simRel hR hi
  have h2 : Tool.beh (Tool.tgtStep (Tool.asyncifyProg P) H) (Tool.tgtSt P e fn args s) =
      obsOut '' hTgtObs (compPO .whole (trP P.env)) kTest (kHost P.env H) s e (kArgs args) := by
    rw [Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.tool_beh_asRes, ← h1,
      Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.beh_mapObs, Set.image_image]
    exact congrArg (· '' _) (funext fun b =>
      (Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.obsOut_eq b).symm)
  rw [h2]
  exact tool_whole P hP H hfn args s

/-! ## An example: `sleep-add` in the kernel -/

open Silmaril.Wasm in
/-- The body of `sleep-add`: `local.get 0; call $sleep; local.set 1; local.get 1; local.get 0;
i32.add`. -/
def exBody : List Instr :=
  [.localGet (Tool.lidx 0), .call ⟨Fin.ofNat _ 0⟩, .localSet (Tool.lidx 1),
    .localGet (Tool.lidx 1), .localGet (Tool.lidx 0), .intBinOp .i32 .add]

/-- `sleep-add` as a machine program: import 0 (one argument, one result), function 1. -/
def exE : Tool.Env := ⟨[(1, 1)], [⟨1, 1, 1, exBody⟩]⟩

/-- A host answering `x + 100` and counting its calls. -/
def exH : Tool.Host Nat := ⟨fun s _ as => (s + 1, as.map (· + 100))⟩

/-- The tool's source: `5 + (5 + 100)`, one host call. -/
theorem ex_tool : Tool.runN (Tool.srcStep exE exH) 20
    (⟨[Tool.entry 1 ⟨1, 1, 1, exBody⟩ [5]], [], fun _ => 0⟩, 0) = .stop (.done [110] 1) := rfl

/-- The translated kernel closed by the host: the same result and host state. -/
theorem ex_kernel : runN (mapObs toolOut (kSrc exE exH)) 30 (sInit 1 (kArgs [5]), 0) =
    .stop (.done [.val (.done [110] 1)]) := rfl

/-- The family's whole-program host target of the translated program: the same. -/
theorem ex_target : runN (mapObs toolOut (observe (htstep (compPO .whole (trP exE)) kTest
    (kHost exE exH)))) 60 (tInit 1 (kArgs [5]), 0) = .stop (.done [.val (.done [110] 1)]) := rfl

/-- info: 'Silmaril.Wasm.FX.Asyncify.Bridge.tool_src_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tool_src_kernel

/-- info: 'Silmaril.Wasm.FX.Asyncify.Bridge.asyncify_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms asyncify_square

end Silmaril.Wasm.FX.Asyncify.Bridge
