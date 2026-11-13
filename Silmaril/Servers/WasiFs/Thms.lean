module

public import Silmaril.Servers.WasiFs.Defs

@[expose] public section

namespace Silmaril.Servers.WasiFs
open Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples Silmaril.Cli
open Silmaril.Net.Http (Request Response)

def reqAt (m : Silmaril.Net.Http.Method) (path : String) (c : List UInt8) : Request :=
  ⟨⟨m, ⟨none, none, some (ascii path)⟩⟩, [], c, []⟩

def fs1 : Fs := Fs.ofList [(keyFile "data" (reqAt .get "/a" []).target, ascii "hi")]

theorem t_get : respOf 1 (runStore "data" fs1 (reqAt .get "/a" [])) =
    some (Response.simple 200 (ascii "hi")) := by decide

theorem t_get_missing : respOf 1 (runStore "data" fs1 (reqAt .get "/b" [])) =
    some (Response.simple 404 []) := by decide

theorem t_put : respOf 1 (runStore "data" fs1 (reqAt .put "/b" (ascii "yo"))) =
    some (Response.simple 201 []) := by decide

theorem t_put_files : (replay "data" fs1 (runStore "data" fs1 (reqAt .put "/b" (ascii "yo")))).files
    (keyFile "data" (reqAt .get "/b" []).target) = some (ascii "yo") := by decide

theorem t_del : respOf 1 (runStore "data" fs1 (reqAt .delete "/a" [])) =
    some (Response.simple 204 []) := by decide

end Silmaril.Servers.WasiFs
