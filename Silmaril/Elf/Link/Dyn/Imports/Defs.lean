module

public import Silmaril.Elf.Link.Dyn.Proc.Defs
public import Silmaril.Crypto.SHA256
public import Silmaril.Apps.Sha256sum.Run

/-! # Loose contracts of further imports, and the `sha256sum` goal

Contracts in the style of `Proc` (a System V call that returns, under a precondition, to a
state satisfying a postcondition), for imports of GNU `sha256sum` beyond `puts`/`exit`:

* `quietStep`: a call whose effect the program cannot observe except through `rax`
  (`setlocale`, `bindtextdomain`, `textdomain`): any `rax` meeting `P`, the image and the
  caller's frames kept, the library state unchanged;
* `cxaAtexitStep` (`__cxa_atexit (f, arg, d)`, which gnulib's `atexit (close_stdout)` becomes):
  `f` is appended to the handlers `exit` runs (`Ghost.atexit`) and 0 returned, or the call
  fails with a non-zero result and registers nothing;
* `sha256InitStep`, `sha256UpdateStep`, `sha256FinalStep` (`libcrypto.so.3`'s
  `SHA256_Init/Update/Final`), stated over an **abstract representation** `ShaRep` of
  `SHA256_CTX` objects: a predicate `holds mem ctx m` ("the context at `ctx` has absorbed `m`")
  chosen by the library and local to the context's 112 bytes. The client relies only on
  `Init` establishing `holds … []`, `Update` extending it with the bytes read at `rsi`, and
  `Final` writing `Silmaril.Crypto.SHA256.digest m` to `rdi`; OpenSSL's actual layout of
  `SHA256_CTX` is never mentioned (a loose spec: every implementation with *some* such
  representation meets it). The writes are confined to the context or the digest buffer
  (`ReturnsExcept`).

The goal for `sha256sum` (`Task.sha256sumFile`) is stated over the contracts of the stdio and
file-system imports, a parameter `Io`, because those are not written yet (see the note in
`Task.sha256sumFile`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Imports

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.RelIsa (Res)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn.Proc

/-- A return that may also write the addresses `fp` (an output buffer of the caller). -/
def ReturnsExcept (W : World) (fp : Nat → Prop) (s t : PState) : Prop :=
  AbiReturn s.m.core s.m.memory t.m.core ∧
  Keeps (fun a => (W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) ∧ ¬ fp a) s.m.memory t.m.memory

/-- A call with no observable effect but its result `rax ∈ P`. -/
def quietStep (W : World) (P : Word → Prop) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory)
    fun t => Returns W s t ∧ P (t.m.core.read .rax) ∧ t.g = s.g

/-- **`__cxa_atexit (f, arg, d)`**. -/
def cxaAtexitStep (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory)
    fun t => Returns W s t ∧
      ((low32 (t.m.core.read .rax) = 0 ∧ t.g = { s.g with atexit := s.g.atexit ++ [s.m.core.read .rdi] }) ∨
       (low32 (t.m.core.read .rax) ≠ 0 ∧ t.g = s.g))

/-- An abstract representation of `SHA256_CTX` objects (chosen by the library). -/
structure ShaRep where
  holds : Memory → Word → List Byte → Prop
  /-- Only the context's 112 bytes and their permissions matter. -/
  local_ : ∀ m m' ctx msg, Keeps (fun a => ctx.toNat ≤ a ∧ a < ctx.toNat + 112) m m' →
    holds m ctx msg → holds m' ctx msg

/-- The bytes of a context. -/
def ctxRange (ctx : Word) (a : Nat) : Prop := ctx.toNat ≤ a ∧ a < ctx.toNat + 112

/-- **`SHA256_Init (ctx)`**: the context has absorbed nothing; returns 1. -/
def sha256InitStep (R : ShaRep) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧
      s.m.memory.Permitted .write (s.m.core.read .rdi).toNat 112)
    fun t => ReturnsExcept W (ctxRange (s.m.core.read .rdi)) s t ∧
      R.holds t.m.memory (s.m.core.read .rdi) [] ∧ low32 (t.m.core.read .rax) = 1 ∧ t.g = s.g

/-- **`SHA256_Update (ctx, data, len)`**: the context absorbs the `len` bytes at `data`. -/
def sha256UpdateStep (R : ShaRep) (W : World) (s : PState) : Res PState → Prop :=
  let ctx := s.m.core.read .rdi
  Contract (AbiEntry s.m.core s.m.memory ∧ (∃ m, R.holds s.m.memory ctx m) ∧
      (∃ d, s.m.memory.readBytes (s.m.core.read .rsi).toNat (s.m.core.read .rdx).toNat = some d) ∧
      s.m.memory.Permitted .write ctx.toNat 112)
    fun t => ReturnsExcept W (ctxRange ctx) s t ∧
      (∀ m d, R.holds s.m.memory ctx m →
        s.m.memory.readBytes (s.m.core.read .rsi).toNat (s.m.core.read .rdx).toNat = some d →
        R.holds t.m.memory ctx (m ++ d)) ∧
      low32 (t.m.core.read .rax) = 1 ∧ t.g = s.g

/-- SHA-256 of a byte list (`Silmaril.Crypto.SHA256.digest`) as machine bytes. -/
def sha256 (m : List Byte) : List Byte :=
  (Silmaril.Crypto.SHA256.digest (m.map UInt8.ofBitVec)).map UInt8.toBitVec

/-- **`SHA256_Final (md, ctx)`**: the 32 bytes at `md` are the digest of what the context
absorbed. -/
def sha256FinalStep (R : ShaRep) (W : World) (s : PState) : Res PState → Prop :=
  let md := s.m.core.read .rdi
  let ctx := s.m.core.read .rsi
  Contract (AbiEntry s.m.core s.m.memory ∧ (∃ m, R.holds s.m.memory ctx m) ∧
      s.m.memory.Permitted .write md.toNat 32 ∧ s.m.memory.Permitted .read md.toNat 32 ∧
      s.m.memory.Permitted .write ctx.toNat 112)
    fun t => ReturnsExcept W (fun a => ctxRange ctx a ∨ (md.toNat ≤ a ∧ a < md.toNat + 32)) s t ∧
      (∀ m, R.holds s.m.memory ctx m → t.m.memory.readBytes md.toNat 32 = some (sha256 m)) ∧
      low32 (t.m.core.read .rax) = 1 ∧ t.g = s.g

/-- The contracts written here, by import name. -/
def specified (R : ShaRep) (W : World) : List (Name × (PState → Res PState → Prop)) :=
  [(nm "setlocale", quietStep W fun _ => True), (nm "bindtextdomain", quietStep W fun _ => True),
   (nm "textdomain", quietStep W fun _ => True), (nm "__cxa_atexit", cxaAtexitStep W),
   (nm "SHA256_Init", sha256InitStep R W), (nm "SHA256_Update", sha256UpdateStep R W),
   (nm "SHA256_Final", sha256FinalStep R W)]

/-- What `sha256sum` must do on a world: exit with the specification's status, having written
its standard output (`Silmaril.Apps.Sha256sum.sha256sum`, GNU coreutils 9.4's behaviour). -/
def ShaDone (w : Silmaril.Apps.Sha256sum.World) (rel : Bool) : PState → Prop :=
  Ended (Silmaril.Apps.Sha256sum.sha256sum w).status fun out =>
    out <+: (Silmaril.Apps.Sha256sum.sha256sum w).stdout.map UInt8.toBitVec ∧
    (rel = true → out = (Silmaril.Apps.Sha256sum.sha256sum w).stdout.map UInt8.toBitVec)

end Silmaril.Elf.Link.Dyn.Imports
