module

public import Silmaril.Wasm.Auto.EquivUnroll.Defs
public import Silmaril.Wasm.Auto.EquivFn.Thms
import Silmaril.Raw.Wasm.Auto.EquivUnroll.Sound

/-!
# Loop unrolling by symbolic execution: results

For `Silmaril.Wasm.Auto.EquivUnroll.Defs` (proofs in `Silmaril/Raw/Wasm/Auto/EquivUnroll/Sound`):

* `wp_loop_iff`, `wp_brIf_iff`: a loop's only step enters its label; `br_if` on a known condition;
* `wp_loop_xstep`: one iteration of a `do … while` loop (entered with an empty stack) is the
  body's symbolic run followed by its first failing guard's trap, the exit, or the next iteration;
* **`wp_xsexecU`**: the unrolling executor is sound against the every-run logic (both readings,
  every profile and host relation), for values below that do not end in a function reference;
* **`segEquivXN_of_checkXU`**: the equivalence check with unrolling is sound (`SegEquivXN`).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivUnroll

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Equiv (NoFuncTop wp_seq_iff wp_label_iff seqPostM_normal seqPostM_ne_normal
  labelPostM loop_step wp_step_inv wp_exit_post)
open Silmaril.Wasm.Auto.EquivFn (wp_iff_of_det)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem wp_loop_iff {m : Corr} {s : Store H} {f : Frame} {us : List Val} {b : List Instr}
    {rest : List Admin} {Q : Post H} :
    Wp m P host s f (vals us ++ .plain (.loop .empty b) :: rest) Q ↔
      Wp m P host s f (vals us ++ [.label 0 [.loop .empty b] (expression b)] ++ rest) Q :=
  Silmaril.Proofs.Wasm.Auto.EquivUnroll.wp_loop_iff

theorem wp_brIf_iff {m : Corr} {s : Store H} {f : Frame} {us : List Val} {c : BitVec 32}
    {l : LabelIdx} {Q : Post H} :
    Wp m P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]) Q ↔
      (if c = 0 then Q s f (.normal us) else Q s f (.br l.toNat us)) :=
  Silmaril.Proofs.Wasm.Auto.EquivUnroll.wp_brIf_iff

/-- **One iteration of a `do … while` loop.** -/
theorem wp_loop_xstep {m : Corr} {mem : Bool} {c : XCtx H} (hc : c.Good mem) {us : List Val}
    (hus : NoFuncTop us) {rest : List Admin} {Q : Post H} {S S₁ : XState} {b body : List Instr}
    {e : XT} {st' : List (IntType × XT)} {k : Nat}
    (hS : S.stack = []) (hl : S.globs.length = c.ga.length)
    (hf : firstFail c.ρ c.mi.bytes S.guards = none)
    (hb : whileBody? b = some body) (hr : xsexec mem S body = some S₁)
    (h₁ : S₁.stack = (.i32, e) :: st') (hk : condConst? e = some k) :
    Wp m P host (c.storeOf mem S) (c.frameOf S)
        (vals (us ++ (c.stackOf S).reverse) ++ .plain (.loop .empty b) :: rest) Q ↔
      match firstFail c.ρ c.mi.bytes S₁.guards with
      | some T => Q (c.storeOf mem T) (c.frameOf T) .trap
      | none =>
        if k = 0 then
          Wp m P host (c.storeOf mem S₁) (c.frameOf S₁)
            (vals (us ++ (c.stackOf { S₁ with stack := st' }).reverse) ++ rest) Q
        else
          Wp m P host (c.storeOf mem S₁) (c.frameOf S₁)
            (vals (us ++ (c.stackOf { S₁ with stack := [] }).reverse) ++ .plain (.loop .empty b) :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.EquivUnroll.wp_loop_xstep hc hus hS hl hf hb hr h₁ hk

/-- **The unrolling executor is sound.** -/
theorem wp_xsexecU {m : Corr} {mem : Bool} {c : XCtx H} (hc : c.Good mem) (us : List Val)
    (hus : NoFuncTop us) (rest : List Admin) (Q : Post H) :
    ∀ (fuel : Nat) (a : List Instr) {S S' : XState}, S.globs.length = c.ga.length →
      firstFail c.ρ c.mi.bytes S.guards = none → xsexecU mem fuel S a = some S' →
      (Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ expression a ++ rest) Q ↔
        XOut m P host c mem S' us rest Q) :=
  Silmaril.Proofs.Wasm.Auto.EquivUnroll.wp_xsexecU hc us hus rest Q

/-- **The equivalence check with unrolling is sound.** -/
theorem segEquivXN_of_checkXU {fuel : Nat} {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (h : checkXU fuel lt st gt mem a b = true) : SegEquivXN lt st gt mem a b :=
  Silmaril.Proofs.Wasm.Auto.EquivUnroll.segEquivXN_of_checkXU h

/-! ## Results used by `Silmaril.Wasm.Auto2` -/

section
-- A lemma of `Silmaril.Proofs.Wasm.Auto.EquivUnroll` that the proofs of `Silmaril.Wasm.Auto2` use.

open Silmaril.Wasm.Auto.EquivUnroll
open Silmaril.Wasm Silmaril.Wasm.Auto
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv

theorem xout_of_fail {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {mem : Bool}
    {c : XCtx H} {us : List Val} {rest : List Admin}
    {Q : Post H} {S₁ S' : XState} {T : XState} (hT : firstFail c.ρ c.mi.bytes S₁.guards = some T)
    (hG : ∃ G, S'.guards = S₁.guards ++ G) :
    XOut m P host c mem S' us rest Q ↔ Q (c.storeOf mem T) (c.frameOf T) .trap :=
  Silmaril.Proofs.Wasm.Auto.EquivUnroll.xout_of_fail hT hG

end

end Silmaril.Wasm.Auto.EquivUnroll
