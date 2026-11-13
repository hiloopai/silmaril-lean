module

public import Silmaril.Wasm.Logic.HoareExamples.Defs

/-!
# Example: throwing and catching an exception

`catchProg_hwp`: in every profile and for every host, every run of
`block (result t) (try_table (result t) (catch x 0) (i32.const 7; throw x))`
ends normally with `7`, in the store extended by the thrown exception. The proof
goes through `HWP.block`, `HWP.tryTable` and `HWP.throw`; the handler postcondition
(`catchPost`) dispatches the exception to the clause `catch x 0`, which branches
out of the `block` with the exception's payload.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.HoareExamples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post handlerPost catchPost caughtPost)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The final postcondition. -/
def catchPost₀ (s : Store H) (f : Frame) (ta : Nat) : Post H := fun s' f' o =>
  s' = s.addExn ⟨ta, [.i32 7]⟩ ∧ f' = f ∧ o = .normal [.i32 7]

/-- The caught exception branches out of the block with its payload. -/
theorem catch_branch {s : Store H} {f : Frame} {ta : Nat} {t : ValType} :
    prePost [] (seqPost P host [] (labelPost P host [f.module.instVal t].length [] []
      (seqPost P host [] (catchPost₀ s f ta)))) (s.addExn ⟨ta, [.i32 7]⟩) f
      (.br l0.toNat [.i32 7]) := by
  show ∃ vs₁ vs₂, [Val.i32 7] = vs₁ ++ vs₂ ∧ vs₂.length = 1 ∧
    HWP P host _ f (vals [] ++ vals vs₂ ++ expression []) (seqPost P host [] (catchPost₀ s f ta))
  refine ⟨[], [.i32 7], rfl, rfl, ?_⟩
  have hq : catchPost₀ s f ta (s.addExn ⟨ta, [.i32 7]⟩) f (.normal [.i32 7]) := ⟨rfl, rfl, rfl⟩
  have hn : HWP P host (s.addExn ⟨ta, [.i32 7]⟩) f (vals [.i32 7] ++ []) (catchPost₀ s f ta) := by
    simpa using HWP.of_vals hq
  simpa [expression] using HWP.of_vals (Q := seqPost P host [] (catchPost₀ s f ta)) hn

/-- **Throw and catch.** -/
theorem catchProg_hwp {s : Store H} {f : Frame} {t : ValType} {x : TagIdx} {ta : Nat}
    {ti : TagInst} {ts : Ty (.list .val)} (ht : s.tag? f x = some (ta, ti))
    (hx : f.module.tags[x.toNat]? = some ta) (he : Expand ti.type (.func ts .nil))
    (hts : ts.length = 1) :
    HWP P host s f (expression (catchProg t x)) (catchPost₀ s f ta) := by
  have hexn : (s.addExn ⟨ta, [.i32 7]⟩).exns[s.exns.length]? = some ⟨ta, [.i32 7]⟩ := by
    simp [Store.addExn]
  have hcatch : catchPost (s.addExn ⟨ta, [.i32 7]⟩) f s.exns.length
      (prePost [] (seqPost P host [] (labelPost P host [f.module.instVal t].length [] []
        (seqPost P host [] (catchPost₀ s f ta))))) [.catch_ x l0] :=
    .inl ⟨⟨_, ta, hexn, hx, rfl⟩, _, hexn, catch_branch⟩
  have hthrow : HWP P host s f (vals ([] ++ [.i32 7]) ++ .plain (.throw x) :: [])
      (labelPost P host [f.module.instVal t].length [] [] (handlerPost [.catch_ x l0]
        (prePost [] (seqPost P host [] (labelPost P host [f.module.instVal t].length [] []
          (seqPost P host [] (catchPost₀ s f ta))))))) :=
    HWP.throw ht he (by simp [hts]) hcatch
  have htry : HWP P host s f (vals ([] ++ []) ++ .plain (.tryTable (.value t) [.catch_ x l0]
      [.intConst .i32 7, .throw x]) :: [])
      (labelPost P host [f.module.instVal t].length [] [] (seqPost P host [] (catchPost₀ s f ta))) :=
    HWP.tryTable rfl rfl hthrow
  exact HWP.block (us := []) (vs := []) rfl rfl (by simpa [expression] using htry)

end Silmaril.Wasm.Logic.HoareExamples
