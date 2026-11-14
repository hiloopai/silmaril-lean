module

public import Silmaril.Servers.Cgi.Defs

/-!
# CGI: proofs

For `Silmaril.Servers.Cgi.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Cgi

open Silmaril.Net.Http Silmaril.Cli Silmaril.Servers.Cgi

theorem respond_hello : respond helloOut = helloResponse := by decide

theorem hello_origin_iff (g : Gateway) (fs : Fs) (r : Request) (resp : Response) (fs' : Fs) :
    origin g hello fs r resp fs' ↔
      resp = Origin.webAnswer (fun _ => helloResponse) r ∧ fs' = fs := by
  constructor
  · rintro ⟨o, ⟨_, hout, hfs⟩, rfl, rfl⟩
    rw [hout, respond_hello]
    exact ⟨rfl, hfs⟩
  · rintro ⟨rfl, h⟩
    refine ⟨{ stdout := helloOut, fs := fs }, ⟨rfl, rfl, rfl⟩, ?_, h⟩
    rw [respond_hello]
    rfl

end Silmaril.Proofs.Servers.Cgi
