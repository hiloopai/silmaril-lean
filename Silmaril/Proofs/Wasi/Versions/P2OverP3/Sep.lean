module

public import Silmaril.Wasi.Versions.P2OverP3.Sep.Defs
public import Silmaril.Wasi.Versions.Stateful.Thms

/-!
# Proofs: sessions are plays

`drive_reach`, `session_reach`, `session_mem`: a session computed by `session` is a reachable
play of the stateful component.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

variable {S : Type} {I X : Set FnName} {h : SBody S I X} {s₀ : S}

/-- Driving a program on matching answers reaches its result. -/
theorem drive_reach (q : (nsig X).Op) :
    ∀ (p : SProg S I) (ns : List (Option (List Val))) {t : List (Move (nsig I) (nsig X))}
      {ms : List (Move (nsig I) (nsig X))} {x : S × Option (List Val)},
      SReach h s₀ t (.run q p) → drive p ns = some (ms, x) →
      SReach h s₀ (t ++ ms) (.run q (.pure x))
  | .pure _, [], _, _, _, ht, hd => by
    simp only [drive, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simpa using ht
  | .pure _, _ :: _, _, _, _, _, hd => nomatch hd
  | .call _ _, [], _, _, _, _, hd => nomatch hd
  | .call m k, n :: ns, t, ms, x, ht, hd => by
    obtain ⟨y, hy, hxy⟩ := Option.map_eq_some_iff.1 hd
    have hms : ms = .inl (.ask m) :: .inl (.ans m n) :: y.1 := (congrArg Prod.fst hxy).symm
    have hx : x = y.2 := (congrArg Prod.snd hxy).symm
    have h2 := (ht.snoc (SStep.call q m k)).snoc (SStep.reply q m k n)
    have h3 := drive_reach q (k n) ns h2 (show drive (k n) ns = some (y.1, y.2) from hy)
    rw [hms, hx]
    simpa using h3

/-- **A session is a reachable play.** -/
theorem session_reach :
    ∀ (s : S) (calls : List ((nsig X).Op × List (Option (List Val))))
      {t ms : List (Move (nsig I) (nsig X))} {s' : S},
      SReach h s₀ t (.idle s) → session h s calls = some (ms, s') → SReach h s₀ (t ++ ms) (.idle s')
  | _, [], _, _, _, ht, hs => by
    simp only [session, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simpa using ht
  | s, (q, ns) :: rest, t, ms, s', ht, hs => by
    simp only [session] at hs
    split at hs
    · rename_i ms1 s1 r hd
      obtain ⟨y, hy, hxy⟩ := Option.map_eq_some_iff.1 hs
      have hms : ms = .inr (.ask q) :: ms1 ++ .inr (.ans q r) :: y.1 :=
        (congrArg Prod.fst hxy).symm
      have hs' : s' = y.2 := (congrArg Prod.snd hxy).symm
      have h1 := drive_reach q (h s q) ns (ht.snoc (SStep.ask s q)) hd
      have h2 := session_reach s1 rest (h1.snoc (SStep.ret q s1 r))
        (show session h s1 rest = some (y.1, y.2) from hy)
      rw [hms, hs']
      simpa using h2
    · exact nomatch hs

/-- **A session is a play of the component.** -/
theorem session_mem {calls : List ((nsig X).Op × List (Option (List Val)))}
    {ms : List (Move (nsig I) (nsig X))} {s' : S} (hs : session h s₀ calls = some (ms, s')) :
    ms ∈ ofSBody h s₀ :=
  ⟨_, by simpa using session_reach s₀ calls SReach.nil hs⟩

end Silmaril.Wasi.Versions.P2OverP3
