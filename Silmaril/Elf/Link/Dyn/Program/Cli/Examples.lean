module

public import Silmaril.Elf.Link.Dyn.Program.Cli.Thms
public import Silmaril.Elf.Link.Dyn.Program.Examples.Thms

/-!
# Verified x86 programs in the CLI institution: hello and cat

The two smallest programs of the Program API (`examples/dyn/ladder`, gcc `-O2` PIE on the
pinned glibc 2.39), read as models of the CLI institution.

PROVED (standard axioms):

* `helloGcc_prints`: **hello-gcc prints `hello, world` and succeeds on every invocation**: the
  full model satisfies the `L1` sentence `Sen.prints` lifted uniformly (`liftAll`: whatever the
  arguments, environment, stdin and files), so its `L1` reduct satisfies `Sen.prints`;
* `catStdinGcc_filter`: **cat-stdin-gcc copies stdin to stdout**: the `L1` reduct of its model
  satisfies the stream filter `Sen.filter id` (default expansion: no arguments).
-/

@[expose] public section

namespace Silmaril.Elf.Link.Dyn.Program.Examples

open Silmaril.Cli.Institution (Level Sen)
open Silmaril.Elf.Link.Dyn.Program

theorem helloGcc_toCli (conv : PathConv) :
    toCli conv helloSpec Tier.reliable ≤ Level.liftAll (L := .stream) (Sen.prints (lit "hello, world\n")) := by
  intro i o h
  rw [Level.liftAll_iff]
  obtain ⟨h1, -, h3, -⟩ := h rfl
  exact ⟨h1, h3⟩

/-- **hello-gcc prints `hello, world` and succeeds, on every invocation.** -/
theorem helloGcc_prints (conv : PathConv) :
    (x86Model helloGcc libc ld lib (fun _ => True) conv).Sat
      (Level.liftAll (L := .stream) (Sen.prints (lit "hello, world\n"))) :=
  (x86Model_sat conv helloGcc_verified).mono (helloGcc_toCli conv)

/-- The `L1` reduct of hello-gcc prints `hello, world`. -/
theorem helloGcc_prints_L1 (conv : PathConv) :
    ((Level.homAll .stream .full).mod (x86Model helloGcc libc ld lib (fun _ => True) conv)).Sat
      (Sen.prints (lit "hello, world\n")) :=
  (Level.sat_liftAll_iff _ _).mp (helloGcc_prints conv)

theorem catStdinGcc_toCli (conv : PathConv) :
    toCli conv catSpec Tier.stdinOnly ≤ Level.lift (L := .stream) (Sen.filter id) := by
  rintro i o h s rfl
  obtain ⟨h1, -, h3, -⟩ := h ⟨rfl, rfl, s, rfl⟩
  exact ⟨h1, h3⟩

/-- **cat-stdin-gcc copies stdin to stdout** (level `L1`, no arguments). -/
theorem catStdinGcc_filter (conv : PathConv) :
    (Level.stream.reduct (x86Model catStdinGcc libc ld lib (fun _ => True) conv)).Sat
      (Sen.filter id) :=
  x86Model_sat_lift conv catStdinGcc_verified (catStdinGcc_toCli conv)

end Silmaril.Elf.Link.Dyn.Program.Examples
