module

public import Silmaril.Proofs.Wasm.Dataflow.DropElim.Erase
public import Silmaril.Wasm.Execution.Core.Sim.Segments
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Label

/-!
# an earlier step of the two-pass DCE: matching one step at the first active rewrite

`EraseMatched P host c c' d` is the one-step obligation of the pass-2 simulation. Each
kind of first active rewrite (`Erase.Atom`) has its matching lemma:

* a kept head takes the same redex step (`erase_keep_match`);
* a pending trap or exception that absorbs a suffix (`erase_cut_match`);
* a structured instruction with erased bodies takes the same rule (`erase_struct_match`, in
  `Struct.lean`);
* a dropped removable producer is matched by dropping its operands, or by a stutter for
  values and `local.get` (`erase_pure_match`, in `Pure.lean`).

The label case, which needs the induction hypothesis, is in
`Silmaril.Proofs.Wasm.Dataflow.DropElim.Sim`.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf noHost)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The obligation of one source step `c ⟶ c'` against the target `d`: a related target
`d'`, reached in at least one step or, with `codeSize` decreasing, in none. -/
def EraseMatched (P : Profile) (host : HostSemantics H) (c c' d : Config H) : Prop :=
  ∃ d', ERel c' d' ∧ (Relation.TransGen (Step P host) d d' ∨
    (d' = d ∧ codeSize c'.code < codeSize c.code))

/-! ## Drops -/

/-- `n` drops discard the last `n` values. -/
theorem steps_drops {s : Store H} {f : Frame} (ws args : List Val) (rest : List Admin) :
    Steps P host ⟨s, f, vals (ws ++ args) ++ List.replicate args.length (.plain .drop) ++ rest⟩
      ⟨s, f, vals ws ++ rest⟩ := by
  induction args using List.reverseRecOn with
  | nil => simpa using Relation.ReflTransGen.refl
  | append_singleton as a ih =>
      have h1 : Step P host ⟨s, f, [a.toAdmin, .plain .drop]⟩ ⟨s, f, []⟩ := .parametric (.drop a)
      have h2 := Sim.Step.append_right (Sim.Step.vals_left h1 (ws ++ as))
        (List.replicate as.length (.plain .drop) ++ rest)
      refine Relation.ReflTransGen.head ?_ ih
      simpa [List.replicate_succ, vals] using h2

/-- At least one drop is at least one step. -/
theorem transGen_drops {s : Store H} {f : Frame} (ws args : List Val) (rest : List Admin)
    (ha : args ≠ []) :
    Relation.TransGen (Step P host)
      ⟨s, f, vals (ws ++ args) ++ List.replicate args.length (.plain .drop) ++ rest⟩
      ⟨s, f, vals ws ++ rest⟩ := by
  obtain ⟨as, a, rfl⟩ : ∃ as a, args = as ++ [a] :=
    ⟨args.dropLast, args.getLast ha, (List.dropLast_append_getLast ha).symm⟩
  have h1 : Step P host ⟨s, f, [a.toAdmin, .plain .drop]⟩ ⟨s, f, []⟩ := .parametric (.drop a)
  have h2 := Sim.Step.append_right (Sim.Step.vals_left h1 (ws ++ as))
    (List.replicate as.length (.plain .drop) ++ rest)
  refine Relation.TransGen.head' ?_ (steps_drops ws as rest)
  simpa [List.replicate_succ, vals] using h2

/-! ## Pending traps and exceptions -/

/-- Trap and exception kernels absorb a source suffix. -/
theorem Erase.cut {k : List Admin} (hk : k = [.trap] ∨ ∃ a, k = throwing a)
    (rest : List Admin) : Erase (k ++ rest) k := by
  rcases hk with rfl | ⟨a, rfl⟩
  · exact .trap rest
  · exact .throwRef a rest

/-- A kernel step that absorbs a nonempty context. -/
theorem kernel_step {s : Store H} {f : Frame} {k : List Admin}
    (hk : k = [.trap] ∨ ∃ a, k = throwing a) (vs : List Val) (rest : List Admin)
    (hne : vs ≠ [] ∨ rest ≠ []) :
    Step P host ⟨s, f, vals vs ++ k ++ rest⟩ ⟨s, f, k⟩ := by
  rcases hk with rfl | ⟨a, rfl⟩
  · exact .trapInstrs hne
  · exact .throwRefInstrs hne

/-- Normalize the suffix after a pending trap or exception, preserving values before it. -/
theorem erase_cut_steps {s : Store H} {f : Frame} (vs : List Val) {k : List Admin}
    (hk : k = [.trap] ∨ ∃ a, k = throwing a) (rest : List Admin) :
    Steps P host ⟨s, f, vals vs ++ k ++ rest⟩ ⟨s, f, vals vs ++ k⟩ := by
  by_cases hr : rest = []
  · subst hr
    simpa using (Relation.ReflTransGen.refl : Steps P host
      (⟨s, f, vals vs ++ k⟩ : Config H) ⟨s, f, vals vs ++ k⟩)
  · exact .single (by simpa using Sim.Step.vals_left (kernel_step (P := P) (host := host)
      (s := s) (f := f) hk [] rest (.inr hr)) vs)

/-- Discarding values or a nonempty suffix makes the stutter measure decrease. -/
theorem erase_discard_lt (ws us : List Val) (k r r' : List Admin) (hne : us ≠ [] ∨ r ≠ []) :
    codeSize (vals ws ++ k ++ r') < codeSize (vals (ws ++ us) ++ k ++ (r ++ r')) := by
  simp only [codeSize_append, codeSize_vals, List.length_append]
  rcases hne with hu | hr
  · have := List.length_pos_iff.mpr hu; omega
  · have := codeSize_pos hr; omega

/-- Match a partial discard, including the case where the target has already absorbed its
entire suffix. -/
theorem erase_partial_discard {s : Store H} {f : Frame} (ws us : List Val) {k : List Admin}
    (hk : k = [.trap] ∨ ∃ a, k = throwing a) (r r' targetRest : List Admin)
    (hne : us ≠ [] ∨ r ≠ []) :
    EraseMatched P host ⟨s, f, vals (ws ++ us) ++ k ++ (r ++ r')⟩ ⟨s, f, vals ws ++ k ++ r'⟩
      ⟨s, f, vals (ws ++ us) ++ k ++ targetRest⟩ := by
  refine ⟨⟨s, f, vals ws ++ k⟩, ⟨rfl, rfl, ?_⟩, ?_⟩
  · simpa only [List.append_assoc] using (Erase.refl (vals ws)).append (Erase.cut hk r')
  · by_cases ht : us ≠ [] ∨ targetRest ≠ []
    · exact .inl (.single (by simpa using Sim.Step.vals_left (kernel_step (P := P)
        (host := host) (s := s) (f := f) hk us targetRest ht) ws))
    · obtain ⟨rfl, rfl⟩ : us = [] ∧ targetRest = [] := by simpa using ht
      exact .inr ⟨by simp, erase_discard_lt ws [] k r r' hne⟩

/-- A step of a pending trap that does not discard a suffix: it discards values. -/
theorem erase_trap_redex {s s' : Store H} {f f' : Frame} {ws us : List Val}
    {is' X Y : List Admin} (hst : Step P host ⟨s, f, vals us ++ [.trap]⟩ ⟨s', f', is'⟩) :
    EraseMatched P host ⟨s, f, vals (ws ++ us) ++ [.trap] ++ X⟩ ⟨s', f', vals ws ++ is' ++ X⟩
      ⟨s, f, vals (ws ++ us) ++ [.trap] ++ Y⟩ := by
  obtain ⟨hs, hf, p, w, q, rfl, -, he⟩ := Sim.Step.trap_redex_aux hst us rfl
  have he' : is' = vals (p ++ q) ++ [.trap] := he
  have hs' : s' = s := hs
  have hf' : f' = f := hf
  subst he' hs' hf'
  refine ⟨⟨_, _, vals (ws ++ (p ++ q)) ++ [.trap]⟩, ⟨rfl, rfl, ?_⟩, .inl ?_⟩
  · simpa using (Erase.refl (vals (ws ++ (p ++ q)))).append (.trap X)
  · apply Relation.TransGen.head' (b := ⟨_, _, vals (ws ++ (p ++ q)) ++ [.trap] ++ Y⟩)
    · simpa using Sim.Step.append_right (Sim.Step.vals_left hst ws) Y
    · exact erase_cut_steps _ (.inl rfl) Y

/-- A step of a pending exception that does not discard a suffix: it discards values. -/
theorem erase_throw_redex {s s' : Store H} {f f' : Frame} {U ws us : List Val} {a : Nat}
    {is' X Y : List Admin} (hU : U ++ [.ref (.exn a)] = ws ++ us)
    (hst : Step P host ⟨s, f, vals us ++ [.plain .throwRef]⟩ ⟨s', f', is'⟩) :
    EraseMatched P host ⟨s, f, vals U ++ throwing a ++ X⟩ ⟨s', f', vals ws ++ is' ++ X⟩
      ⟨s, f, vals U ++ throwing a ++ Y⟩ := by
  obtain ⟨hs, hf, hdisj⟩ := Sim.Step.throwRef_redex_aux hst us rfl
  have hs' : s' = s := hs
  have hf' : f' = f := hf
  subst hs' hf'
  rcases hdisj with ⟨p, w, q, a', rfl, -, he⟩ | ⟨u, u', rfl, -⟩
  · have hU' : U ++ [.ref (.exn a)] = (ws ++ p ++ w ++ q) ++ [.ref (.exn a')] := by
      rw [hU]; simp
    obtain ⟨rfl, ha⟩ := List.append_inj' hU' rfl
    have ha' : a = a' := by simpa using ha
    subst ha' he
    refine ⟨⟨_, _, vals (ws ++ (p ++ q)) ++ throwing a⟩, ⟨rfl, rfl, ?_⟩, .inl ?_⟩
    · simpa using (Erase.refl (vals (ws ++ (p ++ q)))).append (.throwRef a X)
    · apply Relation.TransGen.head' (b := ⟨_, _, vals (ws ++ (p ++ q)) ++ throwing a ++ Y⟩)
      · simpa [vals, Val.toAdmin, throwing] using
          Sim.Step.append_right (Sim.Step.vals_left hst ws) Y
      · exact erase_cut_steps _ (.inr ⟨a, rfl⟩) Y
  · have hU' : U ++ [.ref (.exn a)] = (ws ++ u) ++ [.ref .null] := by rw [hU]; simp
    have := (List.append_inj' hU' rfl).2
    simp at this

/-- Any step of a pending trap is matched against an arbitrary other suffix. -/
theorem erase_trap_match {s s' : Store H} {f f' : Frame} {U : List Val} {X es' : List Admin}
    (h : Step P host ⟨s, f, vals U ++ [.trap] ++ X⟩ ⟨s', f', es'⟩) (Y : List Admin) :
    EraseMatched P host ⟨s, f, vals U ++ [.trap] ++ X⟩ ⟨s', f', es'⟩
      ⟨s, f, vals U ++ [.trap] ++ Y⟩ := by
  have h' : Step P host ⟨s, f, vals U ++ Admin.trap :: X⟩ ⟨s', f', es'⟩ := by simpa using h
  rcases Sim.Step.split_head rfl h' with ⟨ws, us, is', rfl, hst, rfl⟩ |
      ⟨_, rfl, rfl, ws, us, r, r', rfl, rfl, hne, rfl⟩ | ⟨hc, _⟩
  · exact erase_trap_redex hst
  · exact erase_partial_discard ws us (.inl rfl) r r' Y hne
  · cases hc

/-- Any step of a pending exception is matched against an arbitrary other suffix. -/
theorem erase_throw_match {s s' : Store H} {f f' : Frame} {U : List Val} {a : Nat}
    {X es' : List Admin} (h : Step P host ⟨s, f, vals U ++ throwing a ++ X⟩ ⟨s', f', es'⟩)
    (Y : List Admin) :
    EraseMatched P host ⟨s, f, vals U ++ throwing a ++ X⟩ ⟨s', f', es'⟩
      ⟨s, f, vals U ++ throwing a ++ Y⟩ := by
  have e : vals U ++ throwing a ++ X = vals (U ++ [.ref (.exn a)]) ++ .plain .throwRef :: X := by
    simp [vals, throwing, Val.toAdmin]
  rcases Sim.Step.split_head rfl (e ▸ h) with ⟨ws, us, is', hU, hst, rfl⟩ | ⟨hc, _⟩ |
      ⟨_, rfl, rfl, ws, us, x, r, r', hU, rfl, hne, rfl⟩
  · exact erase_throw_redex hU hst
  · cases hc
  · obtain ⟨rfl, ha⟩ := List.append_inj' hU rfl
    have ha' : a = x := by simpa using ha
    subst ha'
    exact erase_partial_discard ws us (.inr ⟨a, rfl⟩) r r' Y hne

/-- A pending trap or exception kernel. -/
theorem erase_cut_match {s s' : Store H} {f f' : Frame} {U : List Val} {k X es' : List Admin}
    (hk : k = [.trap] ∨ ∃ a, k = throwing a)
    (h : Step P host ⟨s, f, vals U ++ k ++ X⟩ ⟨s', f', es'⟩) (Y : List Admin) :
    EraseMatched P host ⟨s, f, vals U ++ k ++ X⟩ ⟨s', f', es'⟩ ⟨s, f, vals U ++ k ++ Y⟩ := by
  rcases hk with rfl | ⟨a, rfl⟩
  · exact erase_trap_match h Y
  · exact erase_throw_match h Y

/-! ## Kept heads -/

/-- A kept administrative head takes the same redex step; partial trap and throw discards
use the suffix absorption of `Erase`. -/
theorem erase_keep_match {s s' : Store H} {f f' : Frame} {vs : List Val} {a : Admin}
    {rest rest' es' : List Admin} (ha : a.val? = none) (hr : Erase rest rest')
    (h : Step P host ⟨s, f, vals vs ++ [a] ++ rest⟩ ⟨s', f', es'⟩) :
    EraseMatched P host ⟨s, f, vals vs ++ [a] ++ rest⟩ ⟨s', f', es'⟩
      ⟨s, f, vals vs ++ [a] ++ rest'⟩ := by
  have hs : Step P host ⟨s, f, vals vs ++ a :: rest⟩ ⟨s', f', es'⟩ := by simpa using h
  rcases Sim.Step.split_head ha hs with ⟨ws, us, is', rfl, hh, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, r, r', rfl, rfl, hne, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, x, r, r', rfl, rfl, hne, rfl⟩
  · refine ⟨⟨s', f', vals ws ++ is' ++ rest'⟩, ⟨rfl, rfl, (Erase.refl _).append hr⟩,
      .inl (.single ?_)⟩
    simpa using Sim.Step.append_right (Sim.Step.vals_left hh ws) rest'
  · simpa using erase_partial_discard (P := P) (host := host) ws us (.inl rfl) r r' rest' hne
  · simpa [vals, Val.toAdmin, throwing] using
      erase_partial_discard (P := P) (host := host) (s := s') (f := f')
        ws us (.inr ⟨x, rfl⟩) r r' rest' hne

end Silmaril.Wasm.Dataflow
