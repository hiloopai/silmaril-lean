module

public import Silmaril.Wasm.Logic.VC.Thms

/-!
# Regression examples for `wat_vc`

Small conditions of `Silmaril.Wasm.Logic.VC.wpc` that `wat_vc` must close alone, one per construct
the generator handles itself rather than by `exec1`: `br_table` (an entry and the default), a
conversion (`cvt1`), `unreachable` (the outcome `trap`) and a `call` against an explicit spec
context (`callVC`, `callK`).
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.WatSpec.VCRegress

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.Core (Post)
open Silmaril.Wasm.Logic.Hoare (FSpec)
open Silmaril.Wasm.Logic.VC

/-- No loop invariants. -/
def noInv : Invs Nat := fun _ _ _ _ => True

variable (s : Store Nat) (f : Frame) (Q : Post Nat)

/-- `br_table` with an in-range index takes the table entry. -/
theorem brTable_entry (h : Q s f (.br 1 [])) :
    wpc noInv 0 [.intConst .i32 1, .brTable [⟨0⟩, ⟨1⟩] ⟨2⟩] Q s f [] := by
  wat_vc

/-- `br_table` with an out-of-range index takes the default. -/
theorem brTable_default (h : Q s f (.br 2 [])) :
    wpc noInv 0 [.intConst .i32 5, .brTable [⟨0⟩, ⟨1⟩] ⟨2⟩] Q s f [] := by
  wat_vc

/-- `i32.wrap_i64` and `i64.extend_i32_u` (`cvt1`). -/
theorem cvt_wrap_extend (c : BitVec 64)
    (h : Q s f (.normal [.num ⟨.int .i64, (c.setWidth 32).setWidth 64⟩])) :
    wpc noInv 0 [.intConst .i64 c, .convert .wrap, .convert (.extend .unsigned)] Q s f [] := by
  wat_vc

/-- `unreachable` ends with the outcome `trap`; the code after it is not looked at. -/
theorem unreachable_trap (h : Q s f .trap) :
    wpc noInv 0 [.unreachable, .intConst .i32 0, .drop] Q s f [] := by
  wat_vc

/-- The specification of a callee: on `[5]`, it returns `[6]` and leaves the store unchanged. -/
abbrev incSpec : FSpec Nat where
  pre _ args := args = [.num ⟨.int .i32, 5#32⟩]
  post s _ s' o := s' = s ∧ o = .normal [.num ⟨.int .i32, 6#32⟩]

/-- A spec context with `incSpec` (one parameter) at address `3`. -/
@[instance_reducible] def ctx : VCSpecs Nat := ⟨fun a => if a = 3 then some (1, incSpec) else none⟩

/-- **`call`** of function `0` of the instance, at address `3`, against the spec context. -/
theorem call_ctx (hf : f.module.funcs[0]? = some 3) (h : Q s f (.normal [.num ⟨.int .i32, 6#32⟩])) :
    wpc (Γ := ctx) noInv 0 [.intConst .i32 5, .call ⟨0⟩] Q s f [] := by
  wat_vc [ctx, incSpec, hf]

end Silmaril.Wasm.Examples.WatSpec.VCRegress
