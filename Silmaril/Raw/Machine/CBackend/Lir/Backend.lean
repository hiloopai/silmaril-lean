module

public import Silmaril.Machine.CBackend.Lir.Behaviour.Defs

/-!
# Backend correctness as refinement

Both Lir backends (`RiscV.Backend.compile_correct`,
`X86.Backend.compile_correct`) prove a forward statement of the same shape,
for target predicates `Returned`, `Trapped` and `Exhausted` on machine states:

* a Lir run that returns `vs` with memory `m` is matched by a target run that
  reaches a `Returned vs m` state or an `Exhausted` state;
* a Lir run that traps with memory `m` is matched by a target run that reaches
  a `Trapped m` state or an `Exhausted` state;
* a diverging Lir run is matched by an infinite target run, or the target run
  reaches an `Exhausted` state.

`Backend.refines_of_correct` turns this into `Refines ⟨.strict, .allowed⟩ tgt
(Lir.sem p) Init ob` for a deterministic target semantics `tgt`, provided the
final outcomes of `tgt` classify these states:

* a `Returned vs m` state shows `returned r` with `(ob t s).ret r (vs, m)`;
* a `Trapped m` state shows `trapped e` with `(ob t s).trap e m`, or shows
  `exhausted`;
* an `Exhausted` state shows `exhausted`.

The three predicates need not be disjoint, and a `Trapped` state may be
classified as exhaustion: on x86 a UD2 reached as a Lir trap may also satisfy
the stack-limit test of the target semantics. The proof is `Refines.of_forward`
with target determinism; the `Safe` premise of `Refines` excludes the stuck
Lir behaviour, about which the forward statement says nothing.

`Backend.refines_of_exact` is the variant without the `Exhausted` alternative
and with traps classified as traps only, concluding
`Refines ⟨.strict, .forbidden⟩`.
-/

@[expose] public section

namespace Silmaril.Machine.Lir

open Relation
open Silmaril.Machine.Behaviour (Semantics Refines Mode Obs)
open Silmaril.Machine.Behaviour.Semantics (Beh)

namespace Backend

variable {R : Type} [DecidableEq R] {S' R' T' F' : Type*}
  {tgt : Semantics S' R' T' F'} {p : Prog R} {Init : S' → State R → Prop}
  {ob : S' → State R → Obs R' (List Word × Memory) T' Memory F' Empty}

/-- The common core, in any mode that admits every `Exhausted` state. -/
private theorem refines_core {m : Mode} (hdet : tgt.Deterministic)
    (Returned : List Word → Memory → S' → Prop) (Trapped : Memory → S' → Prop)
    (Exhausted : S' → Prop)
    (hR : ∀ t s, Init t s → ∀ vs mem u, Returned vs mem u →
      ∃ r, tgt.final u (.returned r) ∧ (ob t s).ret r (vs, mem))
    (hT : ∀ t s, Init t s → ∀ mem u, Trapped mem u →
      (∃ e, tgt.final u (.trapped e) ∧ (ob t s).trap e mem) ∨
        (tgt.final u .exhausted ∧ m.exhaustion = .allowed))
    (hX : ∀ u, Exhausted u → tgt.final u .exhausted ∧ m.exhaustion = .allowed)
    (hret : ∀ t s, Init t s → ∀ vs mem, Behaves p s (.returned vs mem) →
      ∃ u, ReflTransGen tgt.step t u ∧ (Returned vs mem u ∨ Exhausted u))
    (htrap : ∀ t s, Init t s → ∀ mem, Behaves p s (.trapped mem) →
      ∃ u, ReflTransGen tgt.step t u ∧ (Trapped mem u ∨ Exhausted u))
    (hdiv : ∀ t s, Init t s → Diverges p s →
      InfiniteTrace tgt.step t ∨ ∃ u, ReflTransGen tgt.step t u ∧ Exhausted u) :
    Refines m tgt (sem p) Init ob := by
  refine Refines.of_forward hdet (fun _ s _ _ => beh_exists s) ?_
  intro t s hI hs o' ho'
  obtain ⟨b, rfl, hb, hns⟩ := beh_of_safe hs ho'
  have exh : ∀ {u} (o : Behaviour.Outcome (List Word × Memory) Memory Empty),
      ReflTransGen tgt.step t u → tgt.final u .exhausted → m.exhaustion = .allowed →
      ∃ o₁, tgt.Beh t o₁ ∧ Behaviour.Outcome.Rel m (ob t s) o₁ o := by
    intro u o hu hf ha
    refine ⟨.exhausted, Beh.of_reach hu (Beh.of_final hf nofun), ?_⟩
    cases o <;> first | exact ha | trivial
  cases b with
  | returned vs mem =>
    obtain ⟨u, hu, hr | hx⟩ := hret t s hI vs mem hb
    · obtain ⟨r, hf, hob⟩ := hR t s hI vs mem u hr
      exact ⟨.returned r, Beh.of_reach hu (Beh.of_final hf nofun), hob⟩
    · exact exh _ hu (hX u hx).1 (hX u hx).2
  | trapped mem =>
    obtain ⟨u, hu, hr | hx⟩ := htrap t s hI mem hb
    · rcases hT t s hI mem u hr with ⟨e, hf, hob⟩ | ⟨hf, ha⟩
      · exact ⟨.trapped e, Beh.of_reach hu (Beh.of_final hf nofun), .inr hob⟩
      · exact exh _ hu hf ha
    · exact exh _ hu (hX u hx).1 (hX u hx).2
  | stuck => exact absurd rfl hns
  | diverges =>
    rcases hdiv t s hI hb with hi | ⟨u, hu, hx⟩
    · exact ⟨.diverges, hi, trivial⟩
    · exact exh _ hu (hX u hx).1 (hX u hx).2

/-- **Forward backend correctness, up to exhaustion, is refinement.** For a
deterministic target whose final outcomes classify `Returned`, `Trapped` and
`Exhausted` states as in the module docstring, the forward statement of a
backend gives `Refines ⟨.strict, .allowed⟩`: from every initial pair whose
source state is safe, every target behaviour is a return related by `ob` to a
source return, a trap related by `ob` to a source trap, divergence of a
diverging source, or exhaustion. -/
theorem refines_of_correct (hdet : tgt.Deterministic)
    (Returned : List Word → Memory → S' → Prop) (Trapped : Memory → S' → Prop)
    (Exhausted : S' → Prop)
    (hR : ∀ t s, Init t s → ∀ vs mem u, Returned vs mem u →
      ∃ r, tgt.final u (.returned r) ∧ (ob t s).ret r (vs, mem))
    (hT : ∀ t s, Init t s → ∀ mem u, Trapped mem u →
      (∃ e, tgt.final u (.trapped e) ∧ (ob t s).trap e mem) ∨ tgt.final u .exhausted)
    (hX : ∀ u, Exhausted u → tgt.final u .exhausted)
    (hret : ∀ t s, Init t s → ∀ vs mem, Behaves p s (.returned vs mem) →
      ∃ u, ReflTransGen tgt.step t u ∧ (Returned vs mem u ∨ Exhausted u))
    (htrap : ∀ t s, Init t s → ∀ mem, Behaves p s (.trapped mem) →
      ∃ u, ReflTransGen tgt.step t u ∧ (Trapped mem u ∨ Exhausted u))
    (hdiv : ∀ t s, Init t s → Diverges p s →
      InfiniteTrace tgt.step t ∨ ∃ u, ReflTransGen tgt.step t u ∧ Exhausted u) :
    Refines ⟨.strict, .allowed⟩ tgt (sem p) Init ob :=
  refines_core hdet Returned Trapped Exhausted hR
    (fun t s hI mem u h => (hT t s hI mem u h).imp_right fun hf => ⟨hf, rfl⟩)
    (fun u h => ⟨hX u h, rfl⟩) hret htrap hdiv

/-- **Exact forward backend correctness is refinement without exhaustion.**
For a deterministic target whose final outcomes classify `Returned` states as
returns and `Trapped` states as traps, related by `ob`, a forward statement
with no exhaustion alternative gives `Refines ⟨.strict, .forbidden⟩`. -/
theorem refines_of_exact (hdet : tgt.Deterministic)
    (Returned : List Word → Memory → S' → Prop) (Trapped : Memory → S' → Prop)
    (hR : ∀ t s, Init t s → ∀ vs mem u, Returned vs mem u →
      ∃ r, tgt.final u (.returned r) ∧ (ob t s).ret r (vs, mem))
    (hT : ∀ t s, Init t s → ∀ mem u, Trapped mem u →
      ∃ e, tgt.final u (.trapped e) ∧ (ob t s).trap e mem)
    (hret : ∀ t s, Init t s → ∀ vs mem, Behaves p s (.returned vs mem) →
      ∃ u, ReflTransGen tgt.step t u ∧ Returned vs mem u)
    (htrap : ∀ t s, Init t s → ∀ mem, Behaves p s (.trapped mem) →
      ∃ u, ReflTransGen tgt.step t u ∧ Trapped mem u)
    (hdiv : ∀ t s, Init t s → Diverges p s → InfiniteTrace tgt.step t) :
    Refines ⟨.strict, .forbidden⟩ tgt (sem p) Init ob :=
  refines_core hdet Returned Trapped (fun _ => False) hR
    (fun t s hI mem u h => .inl (hT t s hI mem u h)) (fun _ h => h.elim)
    (fun t s hI vs mem hb => (hret t s hI vs mem hb).imp fun _ h => ⟨h.1, .inl h.2⟩)
    (fun t s hI mem hb => (htrap t s hI mem hb).imp fun _ h => ⟨h.1, .inl h.2⟩)
    (fun t s hI hd => .inl (hdiv t s hI hd))

end Backend

end Silmaril.Machine.Lir
