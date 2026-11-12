module

public import Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Unstrip.Defs

/-!
# SpecTec ↔ Core 3.0, round 7: the export swap at the value level (round 2, pass 4)

`Round7.Task.swapEquiv` relates SpecTec's `Step` at `configV hn c` with SpecTec's `Step` at
`configV hn (stripConfig c)`. This header names the value-level relation between the two sides
and the side condition under which it is a partial bijection. It is the value layer of the
swap; the evaluator layer (an invariant over the 29 members of `Sem.evalExp`) is not here.

* `eraseV v`: `v` with the contents of every record field named `EXPORTS` replaced by `[]`
  (deeply). It is the identity on records without such a field, and commutes with every value
  operation that does not name `EXPORTS`.
* `nxB v`: `v` has no record with an `EXPORTS` field at all, as a boolean.
* `AllIn Q v`: every record of `v` that has an `EXPORTS` field satisfies `Q`.
* `unerase Q`: the partial inverse of `eraseV` that `Q` determines.
* `QInj Q`: `eraseV` is injective on records satisfying `Q`. Under it, `eraseV` is injective
  on `AllIn Q` values (`Round7.Swap.eraseV_inj`).
* `InMods c r`: `r` is the image of a module instance of `c` (`Round7.mods c`).
* `QC c r`: `InMods c r`, or `r` is the image of an export-free module instance that is not the
  stripped form of a module instance of `c` with exports. Under `StripInj c` this is injective
  (`Round7.Swap.qInj_QC`), and it holds of every module record of `configV hn c` and of
  `configV hn (mapConfig (unstrip c) d)` for export-free `d`.

**The leaf `Task.stepErase`** (frozen, open): SpecTec's `Step` commutes with `eraseV` on the
swap set `AllIn (QC c)`. It implies `Round7.Task.swapEquiv` (`Round7.Swap.swapEquiv_of_stepErase`)
and is a statement about the evaluator only.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge

variable {H : Type}

mutual
/-- **Erase the export lists**: every record field named `EXPORTS` becomes `[]`, deeply. -/
def eraseV : Value → Value
  | .bool b => .bool b
  | .num n => .num n
  | .text t => .text t
  | .tuple vs => .tuple (eraseVs vs)
  | .case op w => .case op (eraseV w)
  | .struct gs => .struct (eraseVf gs)
  | .list vs => .list (eraseVs vs)
  | .opt none => .opt none
  | .opt (some w) => .opt (some (eraseV w))

/-- `eraseV` on a list of values. -/
def eraseVs : List Value → List Value
  | [] => []
  | v :: vs => eraseV v :: eraseVs vs

/-- `eraseV` on the fields of a record: an `EXPORTS` field becomes `[]`. -/
def eraseVf : List (IL.AtomS × Value) → List (IL.AtomS × Value)
  | [] => []
  | (a, v) :: gs => (a, if a = "EXPORTS" then .list [] else eraseV v) :: eraseVf gs
end

/-- The fields of a record include one named `EXPORTS`. -/
def hasExp (gs : List (IL.AtomS × Value)) : Bool := gs.any fun g => g.1 == "EXPORTS"

mutual
/-- **No record of `v` has an `EXPORTS` field**, as a boolean. -/
def nxB : Value → Bool
  | .bool _ => true
  | .num _ => true
  | .text _ => true
  | .tuple vs => nxBs vs
  | .case _ w => nxB w
  | .struct gs => nxBf gs
  | .list vs => nxBs vs
  | .opt none => true
  | .opt (some w) => nxB w

/-- `nxB` on a list of values. -/
def nxBs : List Value → Bool
  | [] => true
  | v :: vs => nxB v && nxBs vs

/-- `nxB` on the fields of a record. -/
def nxBf : List (IL.AtomS × Value) → Bool
  | [] => true
  | (a, v) :: gs => nxB v && (a != "EXPORTS") && nxBf gs
end

mutual
/-- **Every record of `v` with an `EXPORTS` field satisfies `Q`.** -/
def AllIn (Q : Value → Prop) : Value → Prop
  | .bool _ => True
  | .num _ => True
  | .text _ => True
  | .tuple vs => AllIns Q vs
  | .case _ w => AllIn Q w
  | .struct gs => (hasExp gs = true → Q (.struct gs)) ∧ AllInf Q gs
  | .list vs => AllIns Q vs
  | .opt none => True
  | .opt (some w) => AllIn Q w

/-- `AllIn` on a list of values. -/
def AllIns (Q : Value → Prop) : List Value → Prop
  | [] => True
  | v :: vs => AllIn Q v ∧ AllIns Q vs

/-- `AllIn` on the field values of a record. -/
def AllInf (Q : Value → Prop) : List (IL.AtomS × Value) → Prop
  | [] => True
  | (_, v) :: gs => AllIn Q v ∧ AllInf Q gs
end

mutual
/-- **Undo `eraseV` along `Q`**: a record with an `EXPORTS` field that is the erasure of a
record satisfying `Q` goes back to (a chosen) one; elsewhere `unerase` recurses. Under `QInj Q`
it inverts `eraseV` on `AllIn Q` values (`Round7.Swap.unerase_eraseV`). -/
noncomputable def unerase (Q : Value → Prop) : Value → Value
  | .bool b => .bool b
  | .num n => .num n
  | .text t => .text t
  | .tuple vs => .tuple (uneraseS Q vs)
  | .case op w => .case op (unerase Q w)
  | .struct gs =>
    open Classical in
    if h : hasExp gs = true ∧ ∃ r, Q r ∧ eraseV r = .struct gs then h.2.choose
    else .struct (uneraseF Q gs)
  | .list vs => .list (uneraseS Q vs)
  | .opt none => .opt none
  | .opt (some w) => .opt (some (unerase Q w))

/-- `unerase` on a list of values. -/
noncomputable def uneraseS (Q : Value → Prop) : List Value → List Value
  | [] => []
  | v :: vs => unerase Q v :: uneraseS Q vs

/-- `unerase` on the field values of a record. -/
noncomputable def uneraseF (Q : Value → Prop) : List (IL.AtomS × Value) → List (IL.AtomS × Value)
  | [] => []
  | (a, v) :: gs => (a, unerase Q v) :: uneraseF Q gs
end

/-- **`eraseV` is injective on `Q`.** -/
def QInj (Q : Value → Prop) : Prop :=
  ∀ x y, Q x → Q y → eraseV x = eraseV y → x = y

/-- `r` is the image of a module instance of `c`. -/
def InMods (c : Config H) (r : Value) : Prop :=
  ∃ m ∈ mods c, r = moduleInstToValue Sim.CT m

/-- **The records allowed on the unstripped side**: images of module instances of `c`, and
images of export-free module instances that are not the stripped form of a module instance of
`c` with exports. -/
def QC (c : Config H) (r : Value) : Prop :=
  InMods c r ∨
    ∃ m : ModuleInst, m.exports = [] ∧ r = moduleInstToValue Sim.CT m ∧
      ∀ m' ∈ mods c, stripModule m' = m → m'.exports = []

/-! ## The evaluator-level leaf -/

open Silmaril.Wasm.Validation in
open Silmaril.Wasm.Numerics (Profile RelaxedChoice) in
/-- **SpecTec's `Step` commutes with erasing export lists** (frozen, open), at round 6's
primitives, in the round-7 environment, on the domain of `Round7.Task.swapEquiv`:

* every successor `w` of `configV hn c` keeps the swap set (`AllIn (QC c) w`), and its erasure is
  a successor of `configV hn (stripConfig c)`;
* every successor of `configV hn (stripConfig c)` that is the image of an export-free `d` is the
  erasure of a successor of `configV hn c` that keeps the swap set.

It is the statement about the evaluator alone that `Round7.Task.swapEquiv` needs: the encoding is
handled by `Round7.Swap.eraseV_configV` and `Round7.Swap.eq_configV_unstrip`
(`Round7.Swap.swapEquiv_of_stepErase`). -/
def Task.stepErase : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → HostExportBlind host →
      HostExportParam host → ∀ (nd : Bool) (r : RelaxedChoice),
        ∀ (c : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelE c → StripInj c →
          (∀ w : Value,
            Round6.Reading.SStepB (utf8Env (Round4Int.BI (Profile.spec nd r) hn host))
              (configV hn c) w →
            AllIn (QC c) w ∧
              Round6.Reading.SStepB (utf8Env (Round4Int.BI (Profile.spec nd r) hn host))
                (configV hn (stripConfig c)) (eraseV w)) ∧
          (∀ d : Config H, Stripped d →
            Round6.Reading.SStepB (utf8Env (Round4Int.BI (Profile.spec nd r) hn host))
              (configV hn (stripConfig c)) (configV hn d) →
            ∃ w : Value, AllIn (QC c) w ∧ eraseV w = configV hn d ∧
              Round6.Reading.SStepB (utf8Env (Round4Int.BI (Profile.spec nd r) hn host))
                (configV hn c) w)

end Silmaril.Wasm.SpecTec.Sim.Round7.Swap
