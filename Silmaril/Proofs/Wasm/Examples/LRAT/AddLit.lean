module

public import Silmaril.Proofs.Wasm.Examples.LRAT.Shape
public import Silmaril.Proofs.Wasm.Examples.LRAT.GoodInput

@[expose] public section

/-!
# `add_lit` and `end_clause`, every run

`addLit_hwp`: from a store whose view satisfies `Good xs`, every run of the body of `add_lit(x)`
(and of `end_clause`, which is the same body with `x = 0`) falls through with no results, in a
store whose view satisfies `Good (xs ++ [x.toInt])`. Every profile and host relation. The proof
is symbolic execution with the rules of `Silmaril.Proofs.Wasm.Examples.LRAT.Rules` along the six
paths of the code; the invariant steps are `Silmaril.Proofs.Wasm.Examples.LRAT.GoodInput`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- The view of a store satisfies the invariant after the DIMACS stream `xs`. -/
def InvX {H : Type} (X : Fix H) (xs : List Int) (s : Store H) : Prop :=
  ∃ G B, Shape X s G B ∧ Good xs G B

theorem lratX_ok : MiOk lratX := ⟨lrat_mi.1, lrat_mi.2⟩

/-- The postcondition of a body without results, from the view `G`, `B`, that extends the DIMACS
stream by `c`: the final view satisfies `Good (xs ++ c)` whenever `G`, `B` satisfied `Good xs`. -/
def stepPost {H : Type} (X : Fix H) (G : List (BitVec 32)) (B : ByteArray) (c : List Int) :
    Post H := fun s' _ o =>
  o = .normal [] ∧ ∃ G' B', Shape X s' G' B' ∧ ∀ xs, Good xs G B → Good (xs ++ c) G' B'

theorem stepPost_of {H : Type} {X : Fix H} {G G' : List (BitVec 32)} {B B' : ByteArray}
    {c : List Int} {s : Store H} {f : Frame} (hS : Shape X s G' B')
    (h : ∀ xs, Good xs G B → Good (xs ++ c) G' B') :
    stepPost X G B c s f (.normal ([] : List Val).reverse) :=
  ⟨rfl, G', B', hS, h⟩

theorem stepPost_same {H : Type} {X : Fix H} {G : List (BitVec 32)} {B : ByteArray}
    {s : Store H} {f : Frame} (hS : Shape X s G B) :
    stepPost X G B [] s f (.normal ([] : List Val).reverse) :=
  stepPost_of hS fun xs hG => by rw [List.append_nil]; exact hG

variable {H : Type} {P : Profile} {host : HostSemantics H} {X : Fix H}

variable {s : Store H} {t c S cf sid u n x : BitVec 32} {B : ByteArray}

/-- The code of `add_lit(x)` from the view `G`, `B`, extending the stream by `x`. -/
abbrev AddLitHwp (P : Profile) (host : HostSemantics H) (X : Fix H) (s : Store H)
    (G : List (BitVec 32)) (B : ByteArray) (x : BitVec 32) : Prop :=
  HWP P host s (fr X.mi [x, 0, 0, 0, 0, 0]) (vals ([] : List Val).reverse ++ expression addLitBody ++ [])
    (stepPost X G B [x.toInt])

/-- Unfold the body of `add_lit` into a flat instruction list. -/
macro "addLit_unfold" : tactic => `(tactic| simp only [AddLitHwp, addLitBody, validLitCode, expression,
  List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.append_nil])

set_option maxHeartbeats 1000000 in
/-- Input closed: nothing changes. -/
theorem addLit_closed (hX : MiOk X) {m : BitVec 32} (hS : Shape X s [m, t, c, S, cf, sid, u, n] B)
    (hm : ¬ m = 0#32) : AddLitHwp P host X s [m, t, c, S, cf, sid, u, n] B x := by
  addLit_unfold
  wrun [hm]
  exact w_end (stepPost_of hS fun _ hG => hG.extend hm _)

set_option maxHeartbeats 1000000 in
/-- The end of an empty input clause. -/
theorem addLit_endEmpty (hX : MiOk X) (hS : Shape X s [0#32, t, t, S, cf, sid, u, n] B) :
    AddLitHwp P host X s [0#32, t, t, S, cf, sid, u, n] B 0#32 := by
  addLit_unfold
  rw [show (0#32).toInt = 0 from rfl]
  wrun
  exact w_end (stepPost_of (by assumption) fun _ hG => hG.endEmpty)

set_option maxHeartbeats 1000000 in
/-- The end of a nonempty input clause, recorded. -/
theorem addLit_endRecord (hX : MiOk X) (hS : Shape X s [0#32, t, c, S, cf, sid, u, n] B)
    (htc : ¬ t = c) (hn : n.toNat < 1024) :
    AddLitHwp P host X s [0#32, t, c, S, cf, sid, u, n] B 0#32 := by
  addLit_unfold
  rw [show (0#32).toInt = 0 from rfl]
  wrun [htc, hn]
  have ha : (BitVec.ofNat 32 startBase + n * 4#32).toNat = startBase + 4 * n.toNat := by
    simp only [startBase]; bv_omega
  have hb : (BitVec.ofNat 32 lenBase + n * 4#32).toNat = lenBase + 4 * n.toNat := by
    simp only [lenBase]; bv_omega
  simp only [ha, hb] at *
  exact w_end (stepPost_of (by assumption) fun _ hG => hG.endRecord htc hn)

set_option maxHeartbeats 1000000 in
/-- The end of a nonempty input clause, not recorded (no free id). -/
theorem addLit_endDrop (hX : MiOk X) (hS : Shape X s [0#32, t, c, S, cf, sid, u, n] B)
    (htc : ¬ t = c) (hn : ¬ n.toNat < 1024) :
    AddLitHwp P host X s [0#32, t, c, S, cf, sid, u, n] B 0#32 := by
  addLit_unfold
  rw [show (0#32).toInt = 0 from rfl]
  have hn' := eq_false hn
  wrun [htc, hn']
  exact w_end (stepPost_of (by assumption) fun _ hG => hG.endDrop)

set_option maxHeartbeats 1000000 in
/-- A literal appended to the input clause. -/
theorem addLit_append (hX : MiOk X) (hS : Shape X s [0#32, t, c, S, cf, sid, u, n] B)
    (hx : ¬ x = 0#32) (hv : (x + 1023#32).toNat < 2047) (ht : t.toNat < 65536)
    (ht4 : 4 ∣ t.toNat) : AddLitHwp P host X s [0#32, t, c, S, cf, sid, u, n] B x := by
  addLit_unfold
  wrun [hx, hv, ht]
  exact w_end (stepPost_of (by assumption) fun _ hG => hG.append ⟨hx, hv⟩ ht)

set_option maxHeartbeats 1000000 in
/-- No room in the arena: the input closes. -/
theorem addLit_full (hX : MiOk X) (hS : Shape X s [0#32, t, c, S, cf, sid, u, n] B)
    (hx : ¬ x = 0#32) (hv : (x + 1023#32).toNat < 2047) (ht : ¬ t.toNat < 65536) :
    AddLitHwp P host X s [0#32, t, c, S, cf, sid, u, n] B x := by
  addLit_unfold
  have ht' := eq_false ht
  wrun [hx, hv, ht']
  exact w_end (stepPost_of (by assumption) fun _ hG => hG.close hx)

set_option maxHeartbeats 1000000 in
/-- A literal out of range: the input closes. -/
theorem addLit_range (hX : MiOk X) (hS : Shape X s [0#32, t, c, S, cf, sid, u, n] B)
    (hx : ¬ x = 0#32) (hv : ¬ (x + 1023#32).toNat < 2047) :
    AddLitHwp P host X s [0#32, t, c, S, cf, sid, u, n] B x := by
  addLit_unfold
  have hv' := eq_false hv
  wrun [hx, hv']
  exact w_end (stepPost_of (by assumption) fun _ hG => hG.close hx)

/-- **`add_lit(x)` (and `end_clause`, with `x = 0`), every run**: the invariant is kept, the
stream extended by `x`. -/
theorem addLit_hwp (hX : MiOk X) {xs : List Int} {m : BitVec 32}
    (hS : Shape X s [m, t, c, S, cf, sid, u, n] B) (hG : Good xs [m, t, c, S, cf, sid, u, n] B) :
    AddLitHwp P host X s [m, t, c, S, cf, sid, u, n] B x := by
  by_cases hm : m = 0#32
  · subst hm
    by_cases hx : x = 0#32
    · subst hx
      by_cases htc : t = c
      · subst htc; exact addLit_endEmpty hX hS
      · by_cases hn : n.toNat < 1024
        · exact addLit_endRecord hX hS htc hn
        · exact addLit_endDrop hX hS htc hn
    · by_cases hv : (x + 1023#32).toNat < 2047
      · by_cases ht : t.toNat < 65536
        · exact addLit_append hX hS hx hv ht hG.top_dvd
        · exact addLit_full hX hS hx hv ht
      · exact addLit_range hX hS hx hv
  · exact addLit_closed hX hS hm

end Silmaril.Wasm.Examples.LRAT
