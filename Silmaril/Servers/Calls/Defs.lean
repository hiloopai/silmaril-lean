module

public import Silmaril.Wasi.Comp.Defs
public import Silmaril.Wasi.Host.Defs
public import Silmaril.Servers.Basic.Defs

@[expose] public section

/-!
# Export calls of a WASI component as atomic exchanges

A component given by its body (`Silmaril.Wasi.Comp`) runs one export call at a time: between
the call and its return, the play holds only the component's import calls and the host's
answers. Each export call is therefore an **atomic segment** of the trace, which is what lets
a sequential component be read as a server of atomic exchanges (`Silmaril.Servers.Basic`).

* `Leads p t p'`: running the program `p` on the import answers recorded in `t` (pairs of a
  request and its answer) reaches the program `p'`.
* `Call`: a completed export call: the function, its arguments, the events in between and the
  result. `Done h q c`: `c` is a complete run of the body `h` on the export call `q`.
* `runP impl past p`: the run of the program `p` over a concrete host.
* `calls t`: the completed export calls of an event list, in order (an unfinished last call is
  dropped).
* `model T ans obs σ`: the **reading of a component as a server**. Its traces are those
  explained by a play `s` of `σ` whose events all satisfy `T` (a pointwise theory of the
  host): the completed calls of `s` that `ans` counts as answered are matched, one by one, by
  the exchanges of the trace through `obs` (which may leave the request partly open: a request
  is any one consistent with what the host revealed).

The shape theorem (`Silmaril.Servers.Calls.Thms`): the completed calls of every play of
`ofBody h` are complete runs of `h`, whose events occur in the play.

A Silmaril addition.
-/

namespace Silmaril.Servers.Calls

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

variable {I X : Set FnName}

/-- `Leads p t p'`: the program `p` reaches `p'` on the import calls and answers `t`. -/
inductive Leads : BProg I → List WEv → BProg I → Prop
  /-- No import call. -/
  | refl (p : BProg I) : Leads p [] p
  /-- One import call `m`, answered `n`. -/
  | call (m : (nsig I).Op) (k : Option (List Val) → BProg I) (n : Option (List Val))
      {t : List WEv} {p : BProg I} :
      Leads (k n) t p → Leads (.call m k) (.req m.1.1 m.2 :: .imp m.1.1 m.2 n :: t) p

/-- A completed export call. -/
structure Call where
  /-- The export. -/
  fn : FnName
  /-- Its arguments. -/
  args : List Val
  /-- The events between the call and the return. -/
  inner : List WEv
  /-- The result (`none`: a trap). -/
  res : Option (List Val)

/-- `c` is a complete run of the body `h` on the export call `q`. -/
def Done (h : Body I X) (q : (nsig X).Op) (c : Call) : Prop :=
  c.fn = q.1.1 ∧ c.args = q.2 ∧ Leads (h q) c.inner (.pure c.res)

/-- The events of a completed call. -/
def Call.events (c : Call) : List WEv := .call c.fn c.args :: (c.inner ++ [.ret c.fn c.args c.res])

/-- The completed calls of an event list, given the call in progress. -/
def callsAux : Option (FnName × List Val × List WEv) → List WEv → List Call
  | _, [] => []
  | _, .call f a :: t => callsAux (some (f, a, [])) t
  | some (f, a, u), .ret _ _ r :: t => ⟨f, a, u, r⟩ :: callsAux none t
  | some (f, a, u), .req g b :: t => callsAux (some (f, a, u ++ [.req g b])) t
  | some (f, a, u), .imp g b r :: t => callsAux (some (f, a, u ++ [.imp g b r])) t
  | none, _ :: t => callsAux none t

/-- **The completed export calls** of an event list. -/
def calls (t : List WEv) : List Call := callsAux none t

/-- **Running a program over a concrete host** `impl` (`Silmaril.Wasi.Impl`), after the answers
`past`: the events of the run and its result. -/
def runP (impl : Impl) (past : List WEv) : BProg I → List WEv × Option (List Val)
  | .pure r => ([], r)
  | .call m k =>
    let n := impl past m.1.1 m.2
    let t := runP impl (past ++ [.imp m.1.1 m.2 n]) (k n)
    (.req m.1.1 m.2 :: .imp m.1.1 m.2 n :: t.1, t.2)

/-- **A component read as a server**: the exchange traces explained by its plays. -/
def model {J : Iface} (T : WEv → Prop) (ans : Call → Bool) (obs : Call → Exch J → Prop)
    (σ : Strategy (nsig I) (nsig X)) : Model J :=
  {t | ∃ s ∈ σ, (∀ e ∈ wtrace s, T e) ∧ List.Forall₂ obs ((calls (wtrace s)).filter ans) t}

end Silmaril.Servers.Calls
