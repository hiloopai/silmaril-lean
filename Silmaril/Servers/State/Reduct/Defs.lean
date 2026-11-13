module

public import Silmaril.Servers.State.Defs

@[expose] public section

/-!
# Reducts of servers: requests and responses read through maps

See `docs/projects/http-servers.md` (section "State models"). A server over requests `Req'`
and responses `Resp'` can be read as a server over `Req` and `Resp` through a map of requests
`f : Req → Req'` and a map of responses `g : Resp' → Resp`: a request `r` is handled as `f r`,
and a response `x` is observed as `g x` (`Atomic.comap`, `Server.comap`). Two instances:

* `Server.mapResp g`: the responses are read through `g`, the requests are unchanged. The
  `wasi:http` reading of a component does not observe header fields, so a specification is
  compared with a component through `noFields` (`Silmaril.Servers.WasiFs`);
* `f` a normalisation of requests: a server that does not distinguish the requests `r` and
  `r'` with `f r = f r'` (a store keyed by the path-with-query of the target, not by its scheme
  or authority).

`Ev.map f g` and `Op.map f g` map the events of a history and the operations of a run.

A Silmaril addition.
-/

namespace Silmaril.Servers.State

variable {σ Req Resp Req' Resp' : Type}

/-- An event with its request mapped by `f` and its response by `g`. -/
def Ev.map (f : Req → Req') (g : Resp → Resp') : Ev Req Resp → Ev Req' Resp'
  | .call i r => .call i (f r)
  | .ret i s => .ret i (g s)

/-- An operation with its request mapped by `f` and its response by `g`. -/
def Op.map (f : Req → Req') (g : Resp → Resp') (o : Op Req Resp) : Op Req' Resp' :=
  ⟨o.id, f o.req, g o.resp⟩

/-- **The handler `B` read through maps**: the request `r` is handled as `f r`, and the
response `x` of `B` is observed as `g x`. -/
def Atomic.comap (f : Req → Req') (g : Resp' → Resp) (B : Atomic σ Req' Resp') :
    Atomic σ Req Resp :=
  fun s r resp s' => ∃ x, B s (f r) x s' ∧ resp = g x

/-- **The server `M` read through maps**: same state, environment and initial state, the
handler read through `f` and `g`. -/
def Server.comap (f : Req → Req') (g : Resp' → Resp) (M : Server Req' Resp') :
    Server Req Resp :=
  ⟨M.σ, M.handler.comap f g, M.env, M.init⟩

/-- **The server `M` with its responses read through `g`.** -/
abbrev Server.mapResp (g : Resp → Resp') (M : Server Req Resp) : Server Req Resp' :=
  M.comap id g

end Silmaril.Servers.State
