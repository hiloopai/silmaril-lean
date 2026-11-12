module

public import Silmaril.Wasm.SpecTec.Sim.Defs
public import Silmaril.Wasm.SpecTec.Sim.Control.Defs

/-!
# SpecTec ↔ Core 3.0, track "backward": definitions

Two things, both for the SpecTec → Core half of `Task.wholeStep` and for obstruction 1
(`docs/projects/spectec/README.md`).

1. **Call-annotation equivalence** (`AdminEq`, `CodeEq`, `ConfigEq`). Core's
   `returnCallRefFrameAddr` turns `RETURN_CALL_REF y` into `Admin.retToCallIn fi.module`, a
   `CALL_REF` whose annotation is resolved in the exited frame's module; SpecTec's
   `return_call_ref-frame-addr` yields `CALL_REF y` unchanged. Every call rule of both semantics
   ignores the annotation (`Admin.IsCallRef` in Core, the unconstrained `yy` in SpecTec), so the
   honest one-step simulation relates configurations whose *active* code agrees up to the
   annotation of every administrative `CALL_REF`. `AdminEq` is that relation, structurally:
   two `CALL_REF`s (in either representation, with any annotations) are related; labels, handlers
   and frames are related when their bodies are; every instruction is related to itself.
   Instruction sequences that are not active (block bodies, label continuations, store function
   bodies) are compared by equality.
2. **The backward obligations up to the equivalence** (`BackwardUpTo`), and the minimal decoders
   the generic part of the backward direction needs (`StructDecode`). `Backward` (`Sim/Defs.lean`)
   implies `BackwardUpTo` by reflexivity.

`Task.wholeStepUpTo` restates `Task.wholeStep` with both conclusions up to `ConfigEq`. It is
implied by `Task.wholeStep` (`wholeStep_upTo`), and it is what can hold while Core keeps
`retToCallIn` (option (b) of obstruction 1).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

/-! ## 1. Call-annotation equivalence -/

mutual
/-- Two administrative instructions that agree up to the annotations of `CALL_REF`s in active
position. -/
inductive AdminEq : Admin → Admin → Prop where
  /-- Every instruction agrees with itself. -/
  | refl (a : Admin) : AdminEq a a
  /-- Two `CALL_REF`s, in either representation and with any annotations. -/
  | call {a b : Admin} : a.IsCallRef → b.IsCallRef → AdminEq a b
  /-- Labels with related bodies. -/
  | label {n : Nat} {cont : List Instr} {is js : List Admin} :
      CodeEq is js → AdminEq (.label n cont is) (.label n cont js)
  /-- Handlers with related bodies. -/
  | handler {n : Nat} {cs : List Catch} {is js : List Admin} :
      CodeEq is js → AdminEq (.handler n cs is) (.handler n cs js)
  /-- Frames with related bodies. -/
  | frame {n : Nat} {f : Frame} {is js : List Admin} :
      CodeEq is js → AdminEq (.frame n f is) (.frame n f js)

/-- Two code sequences that agree pointwise up to `AdminEq`. -/
inductive CodeEq : List Admin → List Admin → Prop where
  | nil : CodeEq [] []
  | cons {a b : Admin} {is js : List Admin} : AdminEq a b → CodeEq is js → CodeEq (a :: is) (b :: js)
end

/-- Configurations with the same store and frame and code that agrees up to `CALL_REF`
annotations. -/
def ConfigEq {H : Type} (c d : Config H) : Prop :=
  c.store = d.store ∧ c.frame = d.frame ∧ CodeEq c.code d.code

/-! ## 2. Decoders and the backward obligations up to `ConfigEq` -/

variable {H : Type}

/-- The decoders the generic backward part (`Step` rules 0–5) needs: which Core instruction has
an image with a given context head, and that a code sequence whose image is a typed `val*` is a
value sequence. These are the `label`, `handler`, `frame` and `vals` fields of family C's
`CtrlDecode` (`ofCtrlDecode`); family E (track "typing") is to discharge them. -/
structure StructDecode (env : Env) : Prop where
  /-- `LABEL_n{…} …`. -/
  label : ∀ (a : Admin) (x : Value), adminToV a = .case "LABEL_%{%}%" x →
    ∃ n cont body, a = .label n cont body
  /-- `HANDLER_n{…} …`. -/
  handler : ∀ (a : Admin) (x : Value), adminToV a = .case "HANDLER_%{%}%" x →
    ∃ n cs body, a = .handler n cs body
  /-- `FRAME_n{…} …`. -/
  frame : ∀ (a : Admin) (x : Value), adminToV a = .case "FRAME_%{%}%" x →
    ∃ n fi body, a = .frame n fi body
  /-- A code sequence whose image is a `val*` is a value sequence. -/
  vals : ∀ (ρ : VarEnv) (l : List Admin), ValsOnly ρ → HasTyp env ρ valsT (.list (adminsToV l)) →
    ∃ vs, l = vals vs

/-- The one decoder the `return_call_ref` rules need beyond family C's `CtrlDecode`: an image
headed `RETURN_CALL_REF` is a `RETURN_CALL_REF` in one of its two representations. True by
inspection of `adminToV`; family E (track "typing") is to discharge it. -/
structure RetDecode : Prop where
  /-- `RETURN_CALL_REF yy`. -/
  returnCallRef : ∀ (a : Admin) (x : Value), adminToV a = .case "RETURN_CALL_REF" x →
    a.IsReturnCallRef

open Silmaril.Wasm.Validation in
/-- **SpecTec's `Expand`, read back** (the converse of family C's `CtrlCall.expand`): if the
declarative `Expand` relates the image of a defined type to a function type
`FUNC %(t_1*) -> %(t_2*)`, then Core's `Expand` gives a function type with as many parameters
and results as `t_1*` and `t_2*`. Assumed (family E/C); used by `return_call_ref-frame-addr` backwards. -/
structure CallInv (env : Env) : Prop where
  /-- `Expand` on images, backwards. -/
  expand : ∀ (d : DefType) (T₁ T₂ : List Value),
    DDerives env (otherwise env) "Expand" "%~~%" []
      (.tuple [CT.defType d, .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list T₁]),
        .case "%" (.tuple [.list T₂])])]) →
    ∃ ps rs : Ty (.list .val), Expand d (.func ps rs) ∧ T₁.length = ps.length ∧
      T₂.length = rs.length

/-- **`$blocktype_`, read back** (the converse of family C's `CtrlState.blocktype`): if
`$blocktype_(z, bt)` on an encoded state and block type is `%(t_1*) ->_ [] %(t_2*)`, then Core's
`blockType?` is defined with as many parameters and results. Assumed (family C/E); used by
`block` and `loop` backwards. -/
structure BlockInv {H : Type} (env : Env) (hn : H → String) : Prop where
  /-- `$blocktype_` on images, backwards. -/
  blocktype : ∀ (s : Store H) (f : Frame) (bt : BlockType) (T₁ T₂ : List Value),
    Silmaril.SpecTec.Equiv.ExecNumeric.Applies env "blocktype_"
      [.val (stateV hn s f), .val (Encode.toValue bt)]
      (.case "%->_%%" (.tuple [.case "%" (.tuple [.list T₁]), .list [],
        .case "%" (.tuple [.list T₂])])) →
    ∃ t₁ t₂, f.module.blockType? bt = some (t₁, t₂) ∧ T₁.length = t₁.length ∧
      T₂.length = t₂.length

/-- **`$hostcall` is sound** (the converse of family C's `CtrlHost.hostcall`): every value
`$hostcall` returns on the images of a host function, store and arguments is the image of an
outcome the host allows. Membership is SpecTec's (`Sem.memValue`), so the statement does not
fix the shape of the returned value. Assumed (the choice of `B`'s `$hostcall` from
`HostFinite`); used by the host-call rules backwards. -/
structure HostInv {H : Type} (env : Env) (hn : H → String) (host : HostSemantics H) : Prop where
  /-- Every member of `$hostcall`'s result is an allowed outcome. -/
  hostcall : ∀ (h : H) (s : Store H) (vs : List Val) (v x : Value),
    Silmaril.SpecTec.Equiv.ExecNumeric.Applies env "hostcall"
      [.val (.case "_HOSTFUNC" (.text (hn h))), .val (storeV hn s), .val (.list (vs.map valV))] v →
    memValue x v = .ok (.bool true) → ∃ o, host h s vs o ∧ x = outcomeV hn o

/-- The typing fact the forward direction up to `ConfigEq` needs at `return_call_ref`: a
`CALL_REF yy` is an `instr` when `yy` is a `typeuse` (the converse of family C's
`CtrlTyping.callRefInv`). Assumed (family E). -/
structure CallRefTyping (env : Env) : Prop where
  /-- `CALL_REF yy : instr`. -/
  callRef : ∀ yy : Value, TypedV env (.varT "typeuse" []) yy →
    TypedV env (.varT "instr" []) (.case "CALL_REF" yy)

/-- The backward goal for one SpecTec step from the image of `c`, up to `ConfigEq`: it lands on
the image of a configuration equivalent to a Core successor of `c`. -/
def BwdUpTo (hn : H → String) (P : Profile) (host : HostSemantics H) (c : Config H)
    (w : Value) : Prop :=
  ∃ c' d', ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c'

/-- **The per-rule backward obligations, up to `ConfigEq`**: `Backward` (`Sim/Defs.lean`) with
every conclusion weakened to "the image of a configuration equivalent to a Core successor". The
only rule that needs the weakening is `Step_read` 11 (`return_call_ref-frame-addr`,
obstruction 1). -/
structure BackwardUpTo (env : Env) (hn : H → String) (P : Profile) (host : HostSemantics H) :
    Prop where
  /-- `Step_pure`, rule by rule. -/
  pure : ∀ (i : Nat) (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed env hn ⟨s, f, is⟩ → Fires env "Step_pure" i (.tuple [.list (adminsToV is), w]) →
    ∃ is' js, CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read`, rule by rule. -/
  read : ∀ (i : Nat) (c : Config H) (w : Value),
    Typed env hn c → Fires env "Step_read" i (.tuple [configV hn c, w]) →
    ∃ is' js, CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host c ⟨c.store, c.frame, is'⟩
  /-- The store-changing rules of `Step`, rule by rule. -/
  step : ∀ (i : Nat), 6 ≤ i → ∀ (c : Config H) (w : Value),
    Typed env hn c → Fires env "Step" i (.tuple [configV hn c, w]) → BwdUpTo hn P host c w

/-! ## 3. The goal up to call annotations -/

/-- **`Task.wholeStep` up to call annotations** (obstruction 1, option (b)). As `Task.wholeStep`,
except that the SpecTec successor is the image of a configuration *equivalent* (`ConfigEq`) to
the Core successor, in both directions. A frozen goal: it is implied by `Task.wholeStep`
(`wholeStep_upTo`); this track proves its backward conjunct from per-rule obligations
(`Bwd.backward_upTo`, `docs/projects/spectec/README.md`). -/
def Task.wholeStepUpTo : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
      ∃ B : Builtins,
        (∀ c c' : Config H, Typed (simEnv B) hn c → Typed (simEnv B) hn c' →
          Step (Profile.spec nd r) host c c' →
          ∃ d', ConfigEq c' d' ∧ SStep (simEnv B) (configV hn c) (configV hn d')) ∧
        (∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
          SStep (simEnv B) (configV hn c) w →
          ∃ c' d', ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c')

end Silmaril.Wasm.SpecTec.Sim.Bwd
