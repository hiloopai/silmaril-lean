module

public import Silmaril.Wasm.Binaryen.MergeInterleavedSessions
public import Silmaril.Wasm.Binaryen.Toolkit.MergeSessions

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

open Execution.Core Numerics

/-- The retained decoded source modules and actual merged byte artifact have
exact interleaved persistent sessions, after successful initialization and
under the same arbitrary numerical profile and closed host. Every request
names an export declared by its own source namespace; arguments are unrestricted.
`mergeBytes_sound` independently retains input/output byte meaning and validity. -/
theorem mergeBytes_interleaved_sessions_profile {H : Type}
    {inputs : List (String × ByteArray)} {artifact : MergedArtifact}
    (h : mergeBytes inputs = .ok artifact) (P : Profile)
    {script : List NamedCall} (hscript : Program.NamedScriptExports artifact.inputs script) :
    Program.interleavedSessionBeh P (SingleThreaded.Det.noHost (H := H)) artifact.inputs script =
      moduleReadySessions P (SingleThreaded.Det.noHost (H := H)) closedEnv artifact.merged
        (script.map Prod.snd) :=
  checkedMerge?_interleaved_sessions_profile (mergeBytes_sound h).2.1 P hscript

end Silmaril.Wasm.Binaryen.Toolkit
