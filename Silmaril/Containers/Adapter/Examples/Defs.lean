module

public import Silmaril.Containers.Category.Defs
public import Silmaril.Containers.Events.Defs
public import Silmaril.Containers.Outcome.Defs
public import Silmaril.Containers.Executor.Defs
public import Silmaril.Containers.Fixtures.Defs
public import Silmaril.Containers.Signals.Defs

/-! # Small experimental adapter examples

Default examples use abstract stores; no OCI layout SHA-256 is evaluated here. The executor
is an explicitly finite Boolean model, not a Wasm implementation or an x86 runtime. -/

@[expose] public section
namespace Silmaril.Containers.Adapter.Examples

/-- Configuration, layer and contents are already abstract values. -/
def stores : Stores Unit Fixtures.Blob where
  configs _ := some Fixtures.noop.config
  layers _ := some [(["app"], some (.file () true))]
  blobs _ := some (.prog (.exit 0))

def manifest : Layered Unit := ⟨(), [()]⟩
def abstractRuntime := Runtime.layered stores Fixtures.small

/-- Two descriptor aliases share description 0 and its file identity 91. -/
def aliases : Posix.State where
  descriptors fd := if fd = 3 ∨ fd = 4 then some 0 else none
  descriptions id := if id = 0 then some ⟨91, 0⟩ else none
  files _ := [65, 66]

def cleanupSocket : Sock := ⟨3, .inet4, .stream⟩
def cancelPrefix : List Signals.Action :=
  [.register 2 (.handler 7), .call (.read 0 1), .arrive 2, .deliver 2, .enter, .interrupted]
def cleanup : List Signals.Action := [.effect (.close cleanupSocket), .returnHandler, .exit 130]
def cancelled : Signals.State := Signals.execute {} (cancelPrefix ++ cleanup)
def buggy : Signals.State := Signals.execute {} (cancelPrefix ++ [.fault .memory])

/-- A model executor for two return-code programs, universally over both Boolean host choices.
The host is deliberately irrelevant for these programs. All contexts are the singleton `Unit`.
This demonstrates the certificate fields without a claim about any Wasm binary. -/
def toyExecutor : Executor Bool Bool Unit Bool Unit Unit where
  runtime := Runtime.exact (fun i => .ok i.1)
    (fun g b => b = .done [] (.exited (if g then 0 else 1)))
  supported _ := True
  valid _ := True
  admits _ _ _ := True
  linked g _ _ b := b = .done [] (.exited (if g then 0 else 1))
  observe := Adapter.id

/-- Refusing a wellformed image for resources is permitted by the original API. -/
def resourceLoader : LoaderCat :=
  ⟨Unit, Unit, fun _ => .error .resources⟩

end Silmaril.Containers.Adapter.Examples
