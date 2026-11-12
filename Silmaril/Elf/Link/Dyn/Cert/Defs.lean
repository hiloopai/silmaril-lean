module

public import Silmaril.Elf.Link.Dyn.Proc.Defs
public import Silmaril.X86.Bir9.Defs
public import Silmaril.X86.BlockCert9.Defs
public import Silmaril.X86.Bir9.X.Defs

/-! # Block certificates for the process machine

A **block certificate** (`Blk`) covers a straight-line stretch of an executable's code: its
offset in a code chunk, its listing (`Bir9.LInstr` entries of `Ext` and `Ext9` forms, with their
lengths) and the symbolic block the Bir9 lifter computes for it: the statements (loads, stores,
pushes, condition evaluations) and the final registers, flags and `rip` as terms over the
block's entry state.

`Blk.ok code B` is the decidable check that ties a certificate to the bytes:

* the listing is what `Open9.decode` reads in `code` from `B.off` on, instruction after
  instruction, and every instruction but the last falls through (`seqAt`). Unlike silmaril's
  `BlockCert9.listingAt9`, stores, pushes and calls are allowed;
* every instruction lifts on its own (`Bir9.liftBlock [(i, l)]`); this gives the
  instruction-level memory frame used by the soundness proof (a lifted instruction writes only
  through permission-checked stores, so bytes that are not writable are kept);
* the whole listing lifts to `B.b` (`Bir9.liftBlock B.L = some B.b`).

It is closed by `decide +kernel`. Nothing about the generator that prints certificates is
trusted.

`Wp sts env P` is the weakest precondition of a block's statements: they all run from `env`
(no data fault, no undefined condition) and `P` holds of the final environment. The checker
lemma `Cert.must_blk` (in `Cert/Thms.lean`) turns a checked certificate and the `Wp` of its
block into a `MustQ` step of the process machine `Proc.proc W`.

`BlkX` is the same certificate over the extended lifter `Silmaril.X86.Bir9X`, whose
listings may also hold `Ext8` byte forms and whose lifter also lifts ADC/SBB (`liftBlockX`).

`CodeRO m base code`: the code chunk is not writable (the executable's text segment is mapped
`r-x` by the loader), so the block's own stores cannot change the code it runs.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Cert

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.X86.Bir9 (LInstr Block Stmt Env)
open Silmaril.Process (Memory)

/-- **The listing check.** `L` is what `Open9.decode` reads in `code` from offset `o` on, every
entry is an `Ext` or `Ext9` form that the Bir9 lifter accepts on its own, and every entry but
the last falls through. -/
def seqAt (code : List Byte) : Nat → List (LInstr × Nat) → Bool
  | _, [] => true
  | o, (i, l) :: rest =>
    match Silmaril.X86.Bir9.toX9 i with
    | none => false
    | some j =>
      decide (Silmaril.X86.Open9.decode ((code.drop o).take l) = some (j, l)) && decide (0 < l) &&
        decide (o + l ≤ code.length) &&
        (rest.isEmpty || Silmaril.X86.BlockCert9.fallsThrough9 j) &&
        (Silmaril.X86.Bir9.liftBlock [(i, l)]).isSome &&
        seqAt code (o + l) rest

/-- The total length of a listing. -/
def lenL : List (LInstr × Nat) → Nat
  | [] => 0
  | (_, l) :: rest => l + lenL rest

/-- A block certificate: offset in the code chunk, listing, lifted block. -/
structure Blk where
  off : Nat
  L : List (LInstr × Nat)
  b : Block

/-- **The certificate check** (closed by `decide +kernel`). -/
def Blk.ok (code : List Byte) (B : Blk) : Bool :=
  seqAt code B.off B.L && decide (Silmaril.X86.Bir9.liftBlock B.L = some B.b)

/-- The block's length in bytes. -/
def Blk.len (B : Blk) : Nat := lenL B.L

/-- The code chunk at `base` is not writable. -/
def CodeRO (m : Memory) (base : Word) (code : List Byte) : Prop :=
  ∀ k, k < code.length → m.permits .write (base.toNat + k) = false

/-- **The weakest precondition of a block's statements.** -/
@[irreducible] def Wp : List Stmt → Env → (Env → Prop) → Prop
  | [], env, P => P env
  | st :: rest, env, P =>
    match st.run env with
    | .ok env' => Wp rest env' P
    | .error _ => False

/-- The entry environment of a block run from machine state `m`. -/
def env0 (m : MState) : Env := ⟨m.core, [], m.memory, fun _ => 0⟩

/-- The process state a block leaves, from entry state `s`, in final environment `env`. -/
def post (b : Block) (s : Proc.PState) (env : Env) : Proc.PState :=
  ⟨⟨(b.state env).core, env.mem⟩, s.g⟩

/-! ## Certificates over the extended lifter -/

open Silmaril.X86.Bir9X (XL toX9X liftBlockX)

/-- `seqAt` for `Bir9X` listings. -/
def seqAtX (code : List Byte) : Nat → List (XL × Nat) → Bool
  | _, [] => true
  | o, (i, l) :: rest =>
    match toX9X i with
    | none => false
    | some j =>
      decide (Silmaril.X86.Open9.decode ((code.drop o).take l) = some (j, l)) && decide (0 < l) &&
        decide (o + l ≤ code.length) &&
        (rest.isEmpty || Silmaril.X86.BlockCert9.fallsThrough9 j) &&
        (liftBlockX [(i, l)]).isSome &&
        seqAtX code (o + l) rest

def lenLX : List (XL × Nat) → Nat
  | [] => 0
  | (_, l) :: rest => l + lenLX rest

/-- A block certificate over the extended lifter. -/
structure BlkX where
  off : Nat
  L : List (XL × Nat)
  b : Block

/-- **The certificate check** (closed by `decide +kernel`). -/
def BlkX.ok (code : List Byte) (B : BlkX) : Bool :=
  seqAtX code B.off B.L && decide (liftBlockX B.L = some B.b)

def BlkX.len (B : BlkX) : Nat := lenLX B.L

end Silmaril.Elf.Link.Dyn.Cert
