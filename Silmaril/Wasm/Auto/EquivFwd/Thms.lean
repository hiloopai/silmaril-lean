module

public import Silmaril.Wasm.Auto.EquivFwd.Defs
import Silmaril.Proofs.Wasm.Auto.EquivFwd.Sound

/-!
# Store-to-load forwarding: results

For `Silmaril.Wasm.Auto.EquivFwd.Defs` (proofs in `Silmaril/Proofs/Wasm/Auto/EquivFwd/Sound`):

* `loadV_storeM_same`, `loadV_storeM_disjoint`: read after write of the same range (in bounds),
  and through a store to a disjoint range;
* `evX_fwd_and`: forwarding preserves values under guards that hold;
* `firstFail_fwdG_none`, `firstFail_fwdG_some`, `xout_fwdS`: repeated guards can be dropped and
  every state rewritten under the guards before it, without changing the weakest precondition a
  symbolic run leaves;
* **`segEquivX_of_checkXF`**: the equivalence check with forwarding is sound (`SegEquivX`, both
  readings, every profile and host relation, every typed context).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivFwd

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv (Env)
open Silmaril.Wasm.Auto.Equiv

variable {ρ : Env} {B0 : ByteArray}
variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem loadV_storeM_same (B : ByteArray) (t : IntType) (x : BitVec 32) (arg' arg : MemArg)
    (w : BitVec t.width) (ho : arg'.offset = arg.offset)
    (hb : effAddr x.toNat arg + t.width / 8 ≤ B.size) :
    loadV (storeM B t none x arg' w) t none x arg = w :=
  Silmaril.Proofs.Wasm.Auto.EquivFwd.loadV_storeM_same B t x arg' arg w ho hb

theorem loadV_storeM_disjoint (B : ByteArray) (t' : IntType) (p' : Option PackSize) (x : BitVec 32)
    (arg' arg : MemArg) (w : BitVec t'.width) (t : IntType) (p : Option (PackSize × Signedness))
    (hd : arg'.offset.val + accBytes t' p' ≤ arg.offset.val ∨
      arg.offset.val + accBytes t (p.map Prod.fst) ≤ arg'.offset.val) :
    loadV (storeM B t' p' x arg' w) t p x arg = loadV B t p x arg :=
  Silmaril.Proofs.Wasm.Auto.EquivFwd.loadV_storeM_disjoint B t' p' x arg' arg w t p hd

theorem evX_fwd_and {K : List Guard} (hK : ∀ g ∈ K, g.holds ρ B0 = true) : ∀ e : XT,
    (∀ t, evX ρ B0 t (fwd K t e) = evX ρ B0 t e) ∧ evM ρ B0 (fwdM K e) = evM ρ B0 e :=
  Silmaril.Proofs.Wasm.Auto.EquivFwd.evX_fwd_and hK

theorem firstFail_fwdG_none {ρ : Env} {B0 : ByteArray} :
    ∀ (seen : List Guard) {G : List (Guard × XState)}, firstFail ρ B0 G = none →
      firstFail ρ B0 (fwdG seen G) = none :=
  Silmaril.Proofs.Wasm.Auto.EquivFwd.firstFail_fwdG_none

theorem firstFail_fwdG_some {ρ : Env} {B0 : ByteArray} :
    ∀ (seen : List Guard) {G : List (Guard × XState)} {T : XState},
      (∀ g ∈ seen, g.holds ρ B0 = true) → firstFail ρ B0 G = some T →
      ∃ K, (∀ g ∈ K, g.holds ρ B0 = true) ∧ firstFail ρ B0 (fwdG seen G) = some (fwdT K T) :=
  Silmaril.Proofs.Wasm.Auto.EquivFwd.firstFail_fwdG_some

/-- **The weakest precondition left by a run is that of the forwarded state.** -/
theorem xout_fwdS {m : Corr} {c : XCtx H} {mem : Bool} (S : XState) (us : List Val)
    (rest : List Admin) (Q : Post H) :
    XOut m P host c mem S us rest Q ↔ XOut m P host c mem (fwdS S) us rest Q :=
  Silmaril.Proofs.Wasm.Auto.EquivFwd.xout_fwdS S us rest Q

/-- **The equivalence check with forwarding is sound.** -/
theorem segEquivX_of_checkXF {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (h : checkXF lt st gt mem a b = true) : SegEquivX lt st gt mem a b :=
  Silmaril.Proofs.Wasm.Auto.EquivFwd.segEquivX_of_checkXF h

end Silmaril.Wasm.Auto.EquivFwd
