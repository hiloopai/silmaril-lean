module

public import Silmaril.Data.Layout.Cerberus.Defs
public import Silmaril.Data.Layout.Glibc.Malloc.Defs
public import Silmaril.Proofs.Data.Layout.Cerberus

/-!
# Agreement with Cerberus' concrete layout (System V x86-64)

`Mem.Concrete.typeLayout` (Cerberus' LP64 `DefaultImpl`) and `declLayout sysvX86_64` compute
the same size, alignment and member offsets:

* `Silmaril.Proofs.Data.Layout.Cerb.flat_agree` (PROVED for every such struct): a struct whose
  members are integers, `_Bool` or pointers (through typedefs), without `_Alignas` or
  bit-fields (`FlatField`), alone in its environment;
* `malloc_agree`: for the five glibc 2.39 malloc structures (checked by evaluation in the
  kernel);
* `test_agree`: for a test environment with padding, a union, nested structs, two-dimensional
  arrays, `_Bool` and an over-aligned (`_Alignas(16)`) member;
* `floatDisagreement`: they differ on `float` members: Cerberus' concrete layout gives every
  floating type size and alignment 8, the psABIs `float` 4/4 (`struct { char c; float f; }`
  is 8 bytes with `f` at 4 under System V, 16 bytes with `f` at 8 in Cerberus).
  `Silmaril.Machine.SystemV.Abi.layoutOfCtype` already avoids that shortcut for native code.

Open goal: `Task.cerberusAgreement`, the agreement on the whole fragment `Env.inFragment`
(nested structs and unions, arrays, `_Alignas`, several tags); `flat_agree` is its flat,
single-tag case.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Cerb

open Glibc.Malloc

theorem malloc_agree :
    (["malloc_chunk", "malloc_state", "malloc_par", "tcache_entry",
      "tcache_perthread_struct"].map fun tag =>
        cerberusLayout (env sysvX86_64) .struct tag ==
          ourLayout sysvX86_64 (env sysvX86_64) .struct tag) = [true, true, true, true, true] := by
  decide +kernel

theorem malloc_inFragment : Env.inFragment (env sysvX86_64) = true := by
  decide +kernel

/-- A test environment for the fragment. -/
def testEnv : Env := [
  ⟨.struct, "pad", [⟨"c", .int .char .plain, none, none⟩, ⟨"l", .int .long .signed, none, none⟩,
    ⟨"s", .int .short .unsigned, none, none⟩]⟩,
  ⟨.union, "u", [⟨"c", .int .char .plain, none, none⟩, ⟨"l", .int .long .signed, none, none⟩,
    ⟨"a", .array (.int .int .signed) 3, none, none⟩]⟩,
  ⟨.struct, "nest", [⟨"c", .int .char .plain, none, none⟩, ⟨"u", .union "u", none, none⟩,
    ⟨"p", .struct "pad", none, none⟩, ⟨"m", .array (.array (.int .short .signed) 3) 2, none, none⟩,
    ⟨"b", .bool, none, none⟩, ⟨"w", .int .wchar .plain, none, none⟩,
    ⟨"q", .ptr (.struct "nest"), none, none⟩, ⟨"e", .int (.exact 1) .unsigned, none, none⟩]⟩,
  ⟨.struct, "over", [⟨"c", .int .char .plain, none, none⟩,
    ⟨"x", .int .int .signed, some 16, none⟩, ⟨"d", .int .size .unsigned, none, none⟩]⟩]

theorem test_agree :
    (([(.struct, "pad"), (.union, "u"), (.struct, "nest"), (.struct, "over")] : List (Kind × String)).map
      fun (k, tag) => cerberusLayout testEnv k tag == ourLayout sysvX86_64 testEnv k tag) =
      [true, true, true, true] := by
  decide +kernel

/-- The test layouts themselves (`nest`: `u` at 8, `p` at 24, `m` at 48, `b` at 60, `w` at 64,
`q` at 72, `e` at 80, size 88; `over`: `x` at 16, size 32). -/
theorem test_values :
    ourLayout sysvX86_64 testEnv .struct "nest" = some (88, 8,
      [("c", 0), ("u", 8), ("p", 24), ("m", 48), ("b", 60), ("w", 64), ("q", 72), ("e", 80)]) ∧
    ourLayout sysvX86_64 testEnv .struct "over" = some (32, 16, [("c", 0), ("x", 16), ("d", 24)]) := by
  decide +kernel

def floatEnv : Env :=
  [⟨.struct, "cf", [⟨"c", .int .char .plain, none, none⟩, ⟨"f", .float .float, none, none⟩]⟩]

theorem floatDisagreement :
    ourLayout sysvX86_64 floatEnv .struct "cf" = some (8, 4, [("c", 0), ("f", 4)]) ∧
    cerberusLayout floatEnv .struct "cf" = some (16, 8, [("c", 0), ("f", 8)]) := by
  decide +kernel

/-- Agreement on the whole fragment: for an environment in the fragment, Cerberus' concrete
layout of every struct and union is the System V layout. -/
def Task.cerberusAgreement : Prop :=
  ∀ (env : Env) (k : Kind) (tag : String) r, Env.inFragment env = true →
    ourLayout sysvX86_64 env k tag = some r → cerberusLayout env k tag = some r

end Silmaril.Data.Layout.Cerb
