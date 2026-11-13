module

public import Silmaril.Wasi.Versions.Adapter.Defs

@[expose] public section

/-!
# Driving a stateful component, and the play refuting the strict descriptor theory

`drive h c ins` runs the stateful component `h` (`Silmaril.Wasi.Versions.Stateful`) from the control
state `c` on a list of Opponent inputs (export calls and import answers), making the component's
own move after each input; it returns the moves. `Silmaril.Wasi.Versions.Adapter.Strict.Thms` shows
that the result is a reachable play (`drive_reach`).

`strictIns` are the inputs of the play refuting `P1.fdsStrict` for the adapter: `fd_close(1)`
(the adapter creates its table with `get-stdin`, `get-stdout`, `get-stderr`,
`get-directories`, then drops stdout's output stream and answers `ok`), then `fd_write(1, [])`,
which the adapter answers `ok(0)` without looking at the descriptor (`lib.rs`, `fd_write`:
`if iovs_len == 0 { *nwritten = 0; return ERRNO_SUCCESS; }`). The host's answers are those of
the concrete host `p2ImplA` (`Silmaril.Wasi.Versions.Adapter.Over`): handles `0`, `1`, `2`, the
preopen `/` as descriptor `0`, and `()` for the drop.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

variable {S : Type} {I X : Set FnName}

/-- An Opponent input of a stateful component: an export call or an import answer. -/
inductive In (X : Set FnName) : Type where
  /-- The environment calls an export. -/
  | call (q : (nsig X).Op)
  /-- The host answers the pending import call. -/
  | ans (n : Option (List Val))

/-- The component's own move in a control state, if it has one. -/
def pStep : SCSt S I X → Option (Move (nsig I) (nsig X) × SCSt S I X)
  | .run q (.call m k) => some (.inl (.ask m), .wait q m k)
  | .run q (.pure (s, r)) => some (.inr (.ans q r), .idle s)
  | _ => none

/-- An Opponent input in a control state, if it fits. -/
def oStep (h : SBody S I X) : SCSt S I X → In X → Option (Move (nsig I) (nsig X) × SCSt S I X)
  | .idle s, .call q => some (.inr (.ask q), .run q (h s q))
  | .wait q m k, .ans n => some (.inl (.ans m n), .run q (k n))
  | _, _ => none

/-- **Drive a stateful component** on inputs, each followed by the component's move. -/
def drive (h : SBody S I X) : SCSt S I X → List (In X) → List (Move (nsig I) (nsig X)) × SCSt S I X
  | c, [] => ([], c)
  | c, i :: is =>
    match oStep h c i with
    | none => ([], c)
    | some (o, c₁) =>
      match pStep c₁ with
      | none => let r := drive h c₁ is; (o :: r.1, r.2)
      | some (o', c₂) => let r := drive h c₂ is; (o :: o' :: r.1, r.2)

namespace Adapter

/-- A preview1 export call. -/
def p1Call (n : String) (hn : n ∈ P1.fnNames) (a : List Val) : (nsig P1.imports).Op :=
  ⟨⟨P1.fn n, rfl, hn⟩, a⟩

/-- **The inputs of the play refuting the strict descriptor theory.** -/
def strictIns : List (In P1.imports) :=
  [.call (p1Call "fd_close" (by decide) [.u32 1]),
   .ans (some [.u32 0]), .ans (some [.u32 1]), .ans (some [.u32 2]),
   .ans (some [.record [.record [.u32 0, strV "/"]]]),
   .ans (some []),
   .call (p1Call "fd_write" (by decide) [.u32 1, .record []])]

/-- **The play refuting the strict descriptor theory.** -/
def strictPlay : List (Move (nsig imports) (nsig P1.imports)) :=
  (drive body (.idle ASt.init) strictIns).1

end Adapter

end Silmaril.Wasi.Versions
