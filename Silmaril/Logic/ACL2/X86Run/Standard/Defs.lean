module

public import Silmaril.Logic.ACL2.Standard.Objects.Defs
public import Silmaril.Logic.ACL2.X86Run.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run

open Standard

/-- The three unresolved logical functions in the exported X86-RUN body. Each binding
is total on ACL2 objects, including inputs outside the x86 stobj guard. -/
structure MachineBindings where
  fault : Object → Object
  ms : Object → Object
  fetchDecodeExecute : Object → Object

/-- Interpret the exported old signature over standard objects. The state accessors
and step come from the explicit bindings. ZP, BINARY-+, and the quoted -1 are fixed. -/
def MachineBindings.objectModel (m : MachineBindings) : Model old :=
  let Interpretation (S : Signature) := ∀ {k}, S.Symbol k → (Fin k → Object) → Object
  let addBinding {S : Signature} (name : Name) (n : Nat) (denote : (Fin n → Object) → Object)
      (prior : Interpretation S) : Interpretation (S.add name n) :=
    fun {k} f args =>
      if h : f.val = name then
        have arity : n = k := Option.some.inj (by simpa [Signature.add, h] using f.property)
        denote (fun i => args (Fin.cast arity i))
      else
        prior ⟨f.val, by simpa [Signature.add, h] using f.property⟩ args
  let empty : Interpretation Signature.empty := fun f _ => nomatch f.property
  Standard.objectModel old
    (empty
      |> addBinding faultName 1 (fun args => m.fault (args 0))
      |> addBinding msName 1 (fun args => m.ms (args 0))
      |> addBinding stepName 1 (fun args => m.fetchDecodeExecute (args 0))
      |> addBinding zpName 1 (fun args => (args 0).zp)
      |> addBinding addName 2 (fun args => (args 0).binaryAdd (args 1))
      |> addBinding minusOneName 0 (fun _ => Object.integer (-1)))

end Silmaril.Logic.ACL2.X86Run
