module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD.Thms

/-!
# Round 7, `BD`: context lifting at `configVD`, and host calls under contexts (definitions)

Round 5 (pass 1) proved Core's two host-call steps forward at `configVD` and `BD`, at top level
(`HostRulesD.fwd_callRefHostD`, `fwd_callRefHostDivD`). A host call inside a label, handler or
frame, or under a value prefix and an instruction suffix, is a Core step built by the four
context constructors of `Step` on top of one of those two leaves. This header names that
closure.

* `FwdPD env hn c c'`: `Sim.FwdP` at `configVD` and `TypedD`: when both `configVD` images are
  typed, they are related by SpecTec's whole step.
* `CtxStep L`: the closure of a relation `L` on Core configurations under the four context
  constructors of Core's `Step` (`ctxtInstrs`, `ctxtLabel`, `ctxtHandler`, `ctxtFrame`), with
  the same side conditions.
* `HostLeaf P host`: the two host-call constructors of Core's `Step`, `callRefHost` (the host
  returns) and `callRefHostDiv` (it diverges; the configuration stutters), with their premises.
* `HostCtxStep P host := CtxStep (HostLeaf P host)`: a host call at any depth of evaluation
  context.
* `CallLeaf P host`: the four `call_ref` constructors on a reference (`callRefNull`,
  `callRefFunc`, and the two host calls); `CallCtxStep P host := CtxStep (CallLeaf P host)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HCtx

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round7.MemSimd (configVD TypedD)

variable {H : Type}

/-- **`Sim.FwdP` at `configVD`**: when both images are typed, SpecTec's whole step relates them. -/
def FwdPD (env : Env) (hn : H → String) (c c' : Config H) : Prop :=
  TypedD env hn c → TypedD env hn c' → SStep env (configVD hn c) (configVD hn c')

/-- **The closure of `L` under the four context constructors of Core's `Step`.** -/
inductive CtxStep (L : Config H → Config H → Prop) : Config H → Config H → Prop where
  /-- A leaf step. -/
  | leaf {c c' : Config H} : L c c' → CtxStep L c c'
  /-- `Step/ctxt-instrs`. -/
  | instrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin} :
      CtxStep L ⟨s, f, is⟩ ⟨s', f', is'⟩ → (vs ≠ [] ∨ rest ≠ []) →
      CtxStep L ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩
  /-- `Step/ctxt-label`. -/
  | label {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr} {is is' : List Admin} :
      CtxStep L ⟨s, f, is⟩ ⟨s', f', is'⟩ →
      CtxStep L ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩
  /-- `Step/ctxt-handler`. -/
  | handler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch} {is is' : List Admin} :
      CtxStep L ⟨s, f, is⟩ ⟨s', f', is'⟩ →
      CtxStep L ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩
  /-- `Step/ctxt-frame`. -/
  | frame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin} :
      CtxStep L ⟨s, fi, is⟩ ⟨s', fi', is'⟩ →
      CtxStep L ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩

/-- **Core's two host-call steps, with their premises**: `call_ref` into a host function that
returns (`Step.callRefHost`) or diverges (`Step.callRefHostDiv`). -/
inductive HostLeaf (P : Numerics.Profile) (host : HostSemantics H) : Config H → Config H → Prop
    where
  /-- The host returns `r` in the store `s'`. -/
  | ret {s s' : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H}
      {ps rs : Ty (.list .val)} {h : H} {r : Result} :
      c.IsCallRef → s.funcs[a]? = some fi → Expand fi.type (.func ps rs) →
      vs.length = ps.length → fi.code = .host h → host h s vs (.returned s' r) →
      HostLeaf P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s', f, r.toAdmin⟩
  /-- The host diverges. -/
  | div {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H}
      {ps rs : Ty (.list .val)} {h : H} :
      c.IsCallRef → s.funcs[a]? = some fi → Expand fi.type (.func ps rs) →
      vs.length = ps.length → fi.code = .host h → host h s vs .diverged →
      HostLeaf P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s, f, vals vs ++ [.ref (.func a), c]⟩

/-- **A host call under any evaluation context.** -/
abbrev HostCtxStep (P : Numerics.Profile) (host : HostSemantics H) :
    Config H → Config H → Prop :=
  CtxStep (HostLeaf P host)

/-- **Core's four `call_ref` steps on a reference**, with their premises: a null reference
(`Step.callRefNull`), a Wasm function (`Step.callRefFunc`), and the two host-call steps
(`HostLeaf`). These are exactly the Core leaves that `Step` rules 6–9 (the rules whose left-hand
side ends in `CALL_REF`) simulate. -/
inductive CallLeaf (P : Numerics.Profile) (host : HostSemantics H) : Config H → Config H → Prop
    where
  /-- `call_ref` on a null reference traps. -/
  | null {s : Store H} {f : Frame} {c : Admin} :
      c.IsCallRef → CallLeaf P host ⟨s, f, [.ref .null, c]⟩ ⟨s, f, [.trap]⟩
  /-- `call_ref` into a Wasm function enters a frame. -/
  | func {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H}
      {ps rs : Ty (.list .val)} {code : Func} :
      c.IsCallRef → s.funcs[a]? = some fi → Expand fi.type (.func ps rs) →
      vs.length = ps.length → fi.code = .wasm code →
      CallLeaf P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
        ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
          [.label rs.length [] (expression code.body)]]⟩
  /-- A host call. -/
  | host {c c' : Config H} : HostLeaf P host c c' → CallLeaf P host c c'

/-- **A `call_ref` step on a reference under any evaluation context.** -/
abbrev CallCtxStep (P : Numerics.Profile) (host : HostSemantics H) :
    Config H → Config H → Prop :=
  CtxStep (CallLeaf P host)

end Silmaril.Wasm.SpecTec.Sim.Round7.HCtx
