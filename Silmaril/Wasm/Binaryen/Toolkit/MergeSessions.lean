module

public import Silmaril.Wasm.Binaryen.MergeSessions
public import Silmaril.Wasm.Binaryen.Toolkit.MergeSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

open Execution.Core Numerics

/-- Exact persistent sessions for the actual retained decoded input modules
and actual merged module. Original names/byte meanings, output validity and
output-byte meaning remain certified independently by `mergeBytes_sound`.
The session follows successful initialization, uses the closed host, and asks
only names declared in the selected source namespace. -/
theorem mergeBytes_sessions_profile {H : Type} {inputs : List (String × ByteArray)}
    {artifact : MergedArtifact} (h : mergeBytes inputs = .ok artifact) (P : Profile)
    {n : String} {script : List Call}
    (hscript : Program.ScriptExports artifact.inputs n script) :
    Program.sessionBeh P (SingleThreaded.Det.noHost (H := H)) artifact.inputs n script =
      moduleReadySessions P (SingleThreaded.Det.noHost (H := H)) closedEnv
        artifact.merged script :=
  checkedMerge?_sessions_profile (mergeBytes_sound h).2.1 P hscript

end Silmaril.Wasm.Binaryen.Toolkit
