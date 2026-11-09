module

public import Silmaril.Formats.Compression.Inflate.Stream.RawSemantics

/-!
# Compositional schedules for the whole raw inflater

Delivered input and caller scheduling are separate:
every finite call schedule preserves the controller's complete logical
continuation under every future input extension. The result does not assume
decoding has completed or impose a token/block budget on the executable state.

Only an actually completed controller yields the successful raw-format
corollary. Both abstract version dispatchers share the same mathematical
specification; each source version still needs its own C/Core/assembly bridge.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.RawRuns

open Silmaril.Formats.Compression

/-- Bytes delivered by the caller, in call order, independently of budgets. -/
def deliveredInput (calls : List RawMachine.Call) : List UInt8 :=
  calls.flatMap RawMachine.Call.input

/-- The one-step law used to compose schedules. Quantification over all future
input is essential when a parser suspends in the middle of a code or field. -/
def StepLaw (version : Version) : Prop :=
  ∀ machine reader schedulerFuel capacity,
    Reservoir.Normalizes machine.reservoir reader →
    RawSemantics.WellFormed machine reader →
    ∃ rest, Reservoir.Normalizes (RawMachine.step version machine schedulerFuel capacity).reservoir rest ∧
      RawSemantics.WellFormed (RawMachine.step version machine schedulerFuel capacity) rest ∧
      ∀ future, RawSemantics.denote machine (Reservoir.readerFeed reader future) =
        RawSemantics.denote (RawMachine.step version machine schedulerFuel capacity)
          (Reservoir.readerFeed rest future)

end Silmaril.Formats.Compression.Inflate.Stream.RawRuns
