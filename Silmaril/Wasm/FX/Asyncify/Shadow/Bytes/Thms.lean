module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Bytes.Rec
public import Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Bytes.Bound
public import Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Bytes.Core
public import Silmaril.Wasm.FX.Asyncify.Shadow.Thms

/-!
# The shadow stack in a bounded byte memory: results

The header of `Defs`.

* **`read_record`**: in the byte layout of a memory whose cells are `pre ++ enc q ++ post`, the
  record read backwards from the byte address where `enc q` ends (`readRec`: trailer words, then
  operand slots) is `q`, and it starts at the byte address where `pre` ends. This is the read
  that a rewinding step of `mstep` makes (`popRev` on the cells), done on bytes with addresses
  and widths.
* **`word_is_load`**: the words that `readRec` reads (`rd32`) are the four-byte little-endian
  loads of silmaril-lean's Core memory (`Execution.Memory.load`, used by `i32.load`) holding the
  same bytes.
* **`bounded_sub`**: the bounded shadow-stack machine `bmstep C cap` (a trap when the memory
  would not fit in `cap` bytes) has only behaviours of `mstep` and the trap;
  **`bounded_eq`**: the same behaviours when every reachable memory fits (`AllFit`).
* **The instance** `bytesScheme C cap o`: the shadow-stack strategy with its memory in `cap`
  bytes. It is a **semi-comorphism, target to source**: `bytes_sub` (every behaviour of the
  bounded target is a kernel behaviour or a trap, on the fragment `o.Dom`); and correct
  (`bytes_eq`) on calls whose shadow memory fits.

What this does **not** give: Core 3.0 code. The words of the layout are Core loads
(`word_is_load`), but no Core instruction sequence is shown to read a record (the tool's
`load_core` and `store_core` do that for its own word memory); `mstep` still runs on cells and the layout is a view
of them, checked against the bound after each step. A compiler of the kernel to Core 3.0
functions (with `FXCoreSave`'s save and restore code and `FXDispatch`'s prologue) is open.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Shadow

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.Models.FXAsyncPC
open Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Bytes

variable {V : Type}

/-- **A record reads back from the byte layout.** -/
theorem read_record (C : Codec V) {pre post : List (Cell V)} {q : Rec V} {bs : List UInt8}
    (h : layout C (pre ++ enc q ++ post) = some bs) :
    readRec C bs (addrOf C (pre ++ enc q)) = some (q, addrOf C pre) :=
  readRec_layout C h

/-- **The words of the layout are Core 3.0 loads.** -/
theorem word_is_load (bs : List UInt8) (a : Nat) (h : a + 4 ≤ bs.length) :
    Silmaril.Wasm.Execution.Memory.load ⟨bs.toArray⟩ a 4 = some (BitVec.ofNat 32 (rd32 bs a)) :=
  load_rd32 bs a h

theorem bmstep_guard (C : Codec V) (cap : Nat) (P : Prog (AIns V))
    (B : Nat → Option (List (TIns V))) (test : V → Bool) :
    bmstep C cap P B test = guardStep (mstep P B test) (fitsB C cap) := by
  funext x
  unfold bmstep guardStep
  cases mstep P B test x <;> rfl

/-- **The bounded machine: behaviours of `mstep` or a trap.** -/
theorem bounded_sub (C : Codec V) (cap : Nat) (P : Prog (AIns V))
    (B : Nat → Option (List (TIns V))) (test : V → Bool) (x : MCfg V) :
    beh (bmstep C cap P B test) x ⊆ beh (mstep P B test) x ∪ {.trap} := by
  rw [bmstep_guard]
  exact beh_guard_sub x

/-- **When every reachable memory fits, the same behaviours as `mstep`.** -/
theorem bounded_eq (C : Codec V) (cap : Nat) (P : Prog (AIns V))
    (B : Nat → Option (List (TIns V))) (test : V → Bool) {x : MCfg V}
    (h : AllFit C cap P B test x) : beh (bmstep C cap P B test) x = beh (mstep P B test) x := by
  rw [bmstep_guard]
  exact beh_guard_eq h

/-- The empty memory of an initial configuration fits. -/
theorem mInit_fits (C : Codec V) (cap : Nat) (f : Nat) (args : List (SV V)) :
    fitsB C cap (mInit f args) = true := by
  simp [fitsB, mInit, layout]

/-- **The shadow-stack strategy in a bounded byte memory.** -/
def bytesScheme (V : Type) (C : Codec V) (cap : Nat) (o : Opt) : Scheme V where
  TP := Prog (TIns V)
  compile := compPO o
  run := fun Q test f args =>
    beh (bmstep C cap (annP Q) (bodies Q (rootCode f)) test) (mInit f args)
  dom := o.Dom

/-- **Semi-comorphism, target to source**: every behaviour of the bounded target is a kernel
behaviour or a trap. -/
theorem bytes_sub (C : Codec V) (cap : Nat) (o : Opt) (P : Prog (Ins V)) (hP : o.Dom P)
    (test : V → Bool) (f : Nat) (args : List (SV V)) :
    (bytesScheme V C cap o).run ((bytesScheme V C cap o).compile P) test f args ⊆
      srcRun P test f args ∪ {.trap} := by
  have h := shadow_correct (V := V) o P hP test f args
  have hs := bounded_sub C cap (annP (compPO o P)) (bodies (compPO o P) (rootCode f)) test
    (mInit f args)
  exact h ▸ hs

/-- **Correct where the shadow memory fits.** -/
theorem bytes_eq (C : Codec V) (cap : Nat) (o : Opt) (P : Prog (Ins V)) (hP : o.Dom P)
    (test : V → Bool) (f : Nat) (args : List (SV V))
    (hfit : AllFit C cap (annP (compPO o P)) (bodies (compPO o P) (rootCode f)) test
      (mInit f args)) :
    (bytesScheme V C cap o).run ((bytesScheme V C cap o).compile P) test f args =
      srcRun P test f args :=
  (bounded_eq C cap _ _ test hfit).trans (shadow_correct o P hP test f args)

/-- info: 'Silmaril.Wasm.FX.Asyncify.Shadow.bytes_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytes_sub

/-- info: 'Silmaril.Wasm.FX.Asyncify.Shadow.read_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms read_record

end Silmaril.Wasm.FX.Asyncify.Shadow
