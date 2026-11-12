module

public import Silmaril.Cli.Io.Defs

/-!
# Example CLI programs built from pure cores, with their behaviour specifications

* `echo`: prints its arguments joined by spaces, then `\n` (`echoProg`, `echoSpec`).
* `cat`: copies stdin to stdout and consumes all of it (`catProg`, `catSpec`).
* `copy SRC -o DST`: copies a file (`copyProg`). Its specification `copySpec` is the behaviour
  model's file transformer `Spec.transform` with the identity, so a missing or unreadable `SRC`
  and a usage error are loose `Spec.failure`s; the program meets it up to environment refusals
  (`copy_sat : copyProg.Sat copySpec.orRefused`): it reads `SRC` before it finds that `DST`
  cannot be written.

`Silmaril.Cli.Io.Examples.Thms` proves the programs satisfy them. The harness checks of the same
specifications are in `Silmaril.Cli.Io.Check`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Io.Examples

open Silmaril.Cli Silmaril.Cli.Io

/-! ## echo -/

/-- What `echo` prints on its arguments. -/
def echoOut (args : List String) : Bytes := utf8 (" ".intercalate args ++ "\n")

/-- The core of `echo`. -/
def echoCore (args : List String) (_ : Bytes) : Result := { stdout := echoOut args }

/-- **`echo`**. -/
def echoProg : Prog ExitCode := Prog.ofCore echoCore

/-- **`echo`'s specification**: print the line, touch no file, exit `0`. -/
def echoSpec : Spec := Spec.pure fun i => { stdout := echoOut i.args }

/-! ## cat -/

/-- The core of `cat`. -/
def catCore (_ : List String) (s : Bytes) : Result := { stdout := s }

/-- **`cat`**. -/
def catProg : Prog ExitCode := Prog.ofCore catCore

/-- **`cat`'s specification**: stdout is stdin, all of it consumed. -/
def catSpec : Spec := Spec.pure (fun i => { stdout := i.stdin }) ⊓ Spec.consumesAll

/-! ## copy -/

/-- `copy SRC -o DST`: the source and destination. -/
def copyArgs : List String → Option (String × String)
  | [src, "-o", dst] => some (src, dst)
  | _ => none

/-- The files `copy` reads. -/
def copyReads (args : List String) : List String :=
  match copyArgs args with
  | some (src, _) => [src]
  | none => []

/-- The usage message. -/
def copyUsage : Bytes := utf8 "usage: copy SRC -o DST\n"

/-- The start of the message for an unreadable source. -/
def copyCannot : Bytes := utf8 "copy: cannot read "

/-- The core of `copy`. -/
def copyCore (args : List String) (fs : List (String × Option Bytes)) : Result :=
  match copyArgs args, fs with
  | none, _ => { stderr := copyUsage, exit := 2 }
  | some (_, dst), [(_, some b)] => { files := [(dst, b)] }
  | some (src, _), _ => { stderr := copyCannot ++ utf8 src ++ utf8 "\n", exit := 1 }

/-- **`copy`**. -/
def copyProg : Prog ExitCode := Prog.ofTool copyReads copyCore

/-- **`copy`'s specification**: a file transformer with the identity, from the file `SRC` to
the file `DST`. -/
def copySpec : Spec :=
  Spec.transform (fun i => (copyArgs i.args).bind fun a => (i.resolve a.1).map .file)
    (fun i => (copyArgs i.args).bind fun a => (i.resolve a.2).map .file) fun _ x => .ok x

end Silmaril.Cli.Io.Examples

end
