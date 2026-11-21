module

public import Silmaril.Process.Syscall
public import Silmaril.Process.TypedSyscall.Defs

@[expose] public section

namespace Silmaril.Process.TypedSyscall.Linux

/-- The existing byte-stream syscall contract: `read` and `write` can return,
while `exit` has no response that can resume user code. -/
def signature : Signature := ⟨Syscall.Request, fun
  | .read .. | .write .. => Syscall.Result
  | .exit _ => Empty⟩

/-- Reuse the `Syscall.Step` relation without changing its store or event. -/
def kernel : Kernel signature Syscall.State Syscall.Event := fun req before event answer =>
  match answer with
  | .returned reply after =>
    let result : Syscall.Result := match req, reply with
      | .read .., value | .write .., value => value
      | .exit _, impossible => nomatch impossible
    Syscall.Step before req event (.returned result) after
  | .exited status after => Syscall.Step before req event (.exited status) after

end Silmaril.Process.TypedSyscall.Linux
