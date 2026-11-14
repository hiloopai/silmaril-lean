module

public import Silmaril.Servers.Cgi.Defs
import Silmaril.Proofs.Servers.Cgi.Basic

/-!
# CGI: theorems

PROVED (standard axioms):

* `origin_mono`: refining the program (`Silmaril.Cli.Spec`, `≤`) refines its origin: CLI
  refinement lifts to the server.
* `origin_keeps`, `respectsSafe_of_keepsFiles`: a program that leaves the files is a server
  whose state never changes; in particular it respects safe methods (RFC 9110 §9.2.1).
* `parse_status_example`, `parse_location_example`, `respond_not_cgi` (checked by `decide`):
  the status rules of §6.2 and §6.3.3 on examples.
* `respond_hello` (checked by `decide`) and **`hello_origin_iff`**: the hello script is the
  stateless origin of the web that answers every target with `helloResponse` (and `HEAD`
  without content).
-/

@[expose] public section

namespace Silmaril.Servers.Cgi

open Silmaril.Net.Http Silmaril.Cli

variable {g : Gateway} {S T : Spec} {fs fs' : Fs} {r : Request} {resp : Response}

theorem origin_mono (h : S ≤ T) (hS : origin g S fs r resp fs') : origin g T fs r resp fs' :=
  let ⟨o, ho, h₁, h₂⟩ := hS
  ⟨o, h _ _ ho, h₁, h₂⟩

theorem origin_keeps (h : S ≤ Spec.keepsFiles) (hS : origin g S fs r resp fs') : fs' = fs :=
  let ⟨_, ho, _, h₂⟩ := hS
  h₂.trans (h _ _ ho)

theorem respectsSafe_of_keepsFiles (h : S ≤ Spec.keepsFiles) : (origin g S).RespectsSafe :=
  fun _ _ _ _ _ hS => origin_keeps h hS

/-- A `Status` field gives the status and is not passed on; CRLF line ends are accepted. -/
theorem parse_status_example :
    parse (Method.ascii "Status: 404 Not Found\r\nContent-Type: text/plain\r\n\r\nno") =
      some ⟨404, [⟨Method.ascii "Content-Type", Method.ascii "text/plain"⟩], Method.ascii "no",
        []⟩ := by decide

/-- A `Location` field without `Status` is a client redirect (302). -/
theorem parse_location_example :
    parse (Method.ascii "Location: /x\n\n") =
      some ⟨302, [⟨Method.ascii "Location", Method.ascii "/x"⟩], [], []⟩ := by decide

/-- Output without a blank line ending the header is not a CGI response: the gateway sends
500. -/
theorem respond_not_cgi : respond (Method.ascii "hello\n") = internalError := by decide

theorem respond_hello : respond helloOut = helloResponse := Proofs.Servers.Cgi.respond_hello

/-- **The hello script is the constant web.** -/
theorem hello_origin_iff (g : Gateway) (fs : Fs) (r : Request) (resp : Response) (fs' : Fs) :
    origin g hello fs r resp fs' ↔
      resp = Origin.webAnswer (fun _ => helloResponse) r ∧ fs' = fs :=
  Proofs.Servers.Cgi.hello_origin_iff g fs r resp fs'

end Silmaril.Servers.Cgi
