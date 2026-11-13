module

public import Silmaril.X86.RelIsa.Defs
public import Silmaril.X86.RelIsa.Loosen.Defs
/-!
# Demonic function contracts over relational machines (`FnContract.Must`)


`FnContract.Spec σ` is already machine-independent; only `Spec.Result I` mentions the machine,
through `I.upd`/`I.core`/`I.mem`. This file restates the result and the return test through
`RelIsa.Views` and adds the **demonic** notions. `FnContract/Defs.lean` is not edited.

* `Spec.ResultV V S s t` (`RelIsa.Defs`): the four fields of `Spec.Result` (`silent`, `abi`,
  `frame`, `post`), read through the views `V`.
* `ReturnedV V s m`: `Returned` through `V`.
* `Spec.MustIn A S P`: **demonic first-return total correctness**. From every live entry
  (`AbiEntry` and `S.entry`), *every* run of `A` steps only from states that are not a return
  of this call and satisfy `P s`, never stops, terminates, and reaches a `ResultV` state.
  `Spec.Must A S` is the case `P := ⊤`.
* `FnContract.Must A`: a spec with a `Spec.Must` proof.
* `Spec.comapRel Rel S` (`Spec.comap` is the pull-back along a function): the pull-back of a spec along an abstraction `Rel` (concrete `c`,
  abstract `a`): footprint and postcondition are read through some related abstract state.
  `ViewsRel V W Rel`: the conditions on `Rel` under which `Spec.Must` transfers along a
  simulation (equal registers, `rip` and memory; silent updates reflected).
* `Spec.frameV V S F`: `S` with a memory predicate `F` added to entry and post.

The theorems are in `FnContract/Must/Thms.lean` (proofs in
`Silmaril/Proofs/Machine/X86/FnContract/Must.lean`).
-/

@[expose] public section

namespace Silmaril.X86.FnContract

open Silmaril.X86 (State Word)
open Silmaril.Process (Memory)
open Silmaril.X86.RelIsa (Views)

variable {σ τ : Type}

/-- The function entered at `s` has returned in `m` (`Returned`, through the views `V`). -/
def ReturnedV (V : Views σ) (s m : σ) : Prop :=
  (V.core m).rip = FnContract.retOf (V.core s) (V.mem s) ∧
    (V.core m).read .rsp = (V.core s).read .rsp + 8#64

/-- **Demonic first-return total correctness** of `S` on the relational machine `A`, with the
run predicate `P` (`s` the entry state): from every live entry, every run steps only from
states that are not a return of this call and satisfy `P s`, never stops, terminates, and
reaches a result state. The first such state ends the run (`RelIsa.Must.done`), so the result
is the first return. -/
def Spec.MustIn (A : RelIsa σ) (S : Spec σ) (P : σ → σ → Prop) : Prop :=
  ∀ s, A.live s → AbiEntry (A.core s) (A.mem s) → S.entry s →
    RelIsa.Must A (fun m => ¬ ReturnedV A.toViews s m ∧ P s m) (S.ResultV A.toViews s) s

/-- **Demonic first-return total correctness** of `S` on `A` (no extra run predicate). -/
abbrev Spec.Must (A : RelIsa σ) (S : Spec σ) : Prop := S.MustIn A fun _ _ => True

/-- The pull-back of a spec along an abstraction `Rel` (concrete `c`, abstract `a`). The
precondition asks for a related abstract entry; footprint and postcondition are read through
some related abstract entry (and, for the post, a related abstract final state). -/
def Spec.comapRel (Rel : τ → σ → Prop) (S : Spec σ) : Spec τ where
  entry c := ∃ a, Rel c a ∧ S.entry a
  footprint c x := ∃ a, Rel c a ∧ S.entry a ∧ S.footprint a x
  post c t := ∃ a b, Rel c a ∧ S.entry a ∧ Rel t b ∧ S.post a b

/-- The conditions on an abstraction `Rel` between concrete views `V` and abstract views `W`
under which a contract transfers along a simulation: related states have equal registers,
`rip` and memory (so the System V entry and return tests agree), and a silent abstract result
(only core and memory changed) is silent concretely. For `InfoLe` on `MState` (flags may
differ) the first three hold; the last holds because `MState` is just core and memory. -/
structure ViewsRel (V : Views τ) (W : Views σ) (Rel : τ → σ → Prop) : Prop where
  regs : ∀ {c a}, Rel c a → (V.core c).regs = (W.core a).regs
  rip : ∀ {c a}, Rel c a → (V.core c).rip = (W.core a).rip
  mem : ∀ {c a}, Rel c a → V.mem c = W.mem a
  silent : ∀ {c a t b}, Rel c a → Rel t b → W.upd a (W.core b) (W.mem b) = b →
    V.upd c (V.core t) (V.mem t) = t

/-- `S` with a memory predicate `F` added to its precondition and postcondition, read through
the views `V` (the spec of `FnContract.frame`). -/
def Spec.frameV (V : Views σ) (S : Spec σ) (F : Memory → Prop) : Spec σ where
  entry s := S.entry s ∧ F (V.mem s)
  footprint := S.footprint
  post s t := S.post s t ∧ F (V.mem t)

end FnContract

/-- **A demonic System V function contract** over the relational machine `A`: a spec whose
every run from every entry reaches its first return (`Spec.Must`). -/
structure FnContract.Must {σ : Type} (A : RelIsa σ) extends FnContract.Spec σ where
  must : toSpec.Must A

end Silmaril.X86
