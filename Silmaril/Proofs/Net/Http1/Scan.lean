module

public import Silmaril.Net.Http1.Scan.Defs
public import Silmaril.Parse.ByteParse.Thms

/-!
# Scanning runs: laws

`scanWhile` stays in its window and stops exactly after a run of `pred` bytes
(`scanWhile_ge`, `scanWhile_le`, `scanWhile_run`, `scanWhile_stop`, `scanWhile_of_run`), so
`runThen pred` is sound and complete for `Spec.runThen pred`.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse

variable {pred : UInt8 → Bool} {bs : ByteArray} {st : Nat}

theorem scanWhile_ge (i : Nat) : i ≤ scanWhile pred bs st i := by
  fun_induction scanWhile pred bs st i <;> omega

theorem scanWhile_le {i : Nat} (h : i ≤ st) : scanWhile pred bs st i ≤ st := by
  fun_induction scanWhile pred bs st i <;> omega

/-- Every byte between the start and the stop satisfies `pred`. -/
theorem scanWhile_run (i : Nat) : ∀ b ∈ seg bs i (scanWhile pred bs st i), pred b = true := by
  fun_induction scanWhile pred bs st i with
  | case1 i h hp ih =>
    intro b hb
    have hk : i + 1 ≤ scanWhile pred bs st (i + 1) := scanWhile_ge (i + 1)
    have hs : seg bs i (scanWhile pred bs st (i + 1)) =
        bs[i] :: seg bs (i + 1) (scanWhile pred bs st (i + 1)) := seg_cons bs h.2 (by omega)
    rw [hs, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hp
    · exact ih b hb
  | case2 => intro b hb; simp at hb
  | case3 => intro b hb; simp at hb

/-- The byte at the stop, if inside the window, fails `pred`. -/
theorem scanWhile_stop (i : Nat) (h : scanWhile pred bs st i < st ∧ scanWhile pred bs st i < bs.size) :
    pred (bs[scanWhile pred bs st i]'h.2) = false := by
  fun_induction scanWhile pred bs st i with
  | case1 i _ _ ih => exact ih h
  | case2 i _ hp => simpa using hp
  | case3 i hn => exact absurd h hn

/-- On a run `v` of `pred` bytes followed by a byte outside `pred`, the scan stops right
after `v`. -/
theorem scanWhile_of_run (hst : st ≤ bs.size) : ∀ (v : Bytes) (i : Nat),
    seg bs i (i + v.length) = v → (∀ b ∈ v, pred b = true) → (h : i + v.length < st) →
    pred (bs[i + v.length]'(by omega)) = false → scanWhile pred bs st i = i + v.length
  | [], i, _, _, h, hc => by
    have hi : i < st ∧ i < bs.size := ⟨by simpa using h, by simp at h; omega⟩
    simp only [List.length_nil, Nat.add_zero] at hc ⊢
    rw [scanWhile]
    simp [hi.1, hi.2, hc]
  | x :: v, i, hseg, hall, h, hc => by
    have hi : i < st ∧ i < bs.size := ⟨by simp at h; omega, by simp at h; omega⟩
    have hs : seg bs i (i + (x :: v).length) = bs[i] :: seg bs (i + 1) (i + (x :: v).length) :=
      seg_cons bs hi.2 (by simp)
    rw [hs] at hseg
    have hx : bs[i] = x := (List.cons.inj hseg).1
    have hv : seg bs (i + 1) (i + 1 + v.length) = v := by
      have := (List.cons.inj hseg).2
      simpa [Nat.add_assoc, Nat.add_comm 1] using this
    have hpx : pred bs[i] = true := by rw [hx]; exact hall x (by simp)
    have hlen : i + 1 + v.length = i + (x :: v).length := by simp; omega
    have hrec : scanWhile pred bs st (i + 1) = i + 1 + v.length :=
      scanWhile_of_run hst v (i + 1) hv (fun b hb => hall b (by simp [hb])) (by omega)
        (by simpa only [hlen] using hc)
    rw [scanWhile]
    simp only [hi.1, hi.2, and_self, ↓reduceDIte, hpx, ↓reduceIte, hrec, hlen]

theorem sound_runThen (pred : UInt8 → Bool) : Sound (Spec.runThen pred) (runThen pred) := by
  intro bs st i r j hi hs hp
  by_cases h : scanWhile pred bs st i < st ∧ scanWhile pred bs st i < bs.size
  · have hp' : runThen pred bs st i = .ok ((bs.extract i (scanWhile pred bs st i)).data.toList,
        bs[scanWhile pred bs st i]'h.2) (scanWhile pred bs st i + 1) := by
      simp only [runThen, h, and_self, ↓reduceDIte]
    rw [hp'] at hp
    cases hp
    have hge : i ≤ scanWhile pred bs st i := scanWhile_ge i
    have hsplit : seg bs i (scanWhile pred bs st i + 1) =
        seg bs i (scanWhile pred bs st i) ++ [bs[scanWhile pred bs st i]'h.2] := by
      rw [seg_append bs hge (Nat.le_succ _), seg_cons bs h.2 (Nat.lt_succ_self _), seg_self]
    have hrun : ∀ b ∈ (bs.extract i (scanWhile pred bs st i)).data.toList, pred b = true := by
      rw [seg_extract]; exact scanWhile_run i
    refine ⟨by omega, by omega, ?_, hrun, scanWhile_stop i h⟩
    rw [hsplit, seg_extract]
  · have hp' : runThen pred bs st i = .err ⟨scanWhile pred bs st i, .eof⟩ := by
      simp only [runThen, h, ↓reduceDIte]
    rw [hp'] at hp
    cases hp

theorem complete_runThen (pred : UInt8 → Bool) : Complete (Spec.runThen pred) (runThen pred) := by
  rintro l ⟨v, c⟩ bs st i ⟨hlv, hall, hc⟩ hl hs hseg
  simp only at hlv hall hc
  subst hlv
  have hb : i + (v ++ [c]).length ≤ bs.size := by omega
  have hv : seg bs i (i + v.length) = v := seg_split_left bs hb hseg
  have hcs : seg bs (i + v.length) (i + v.length + [c].length) = [c] := seg_split_right bs hb hseg
  simp only [List.length_append, List.length_singleton] at hl hb hcs
  have hk : i + v.length < bs.size := by omega
  have hcb : bs[i + v.length] = c := by
    rw [seg_cons bs hk (by omega), seg_self] at hcs
    exact (List.cons.inj hcs).1
  have hscan : scanWhile pred bs st i = i + v.length :=
    scanWhile_of_run hs v i hv hall (by omega) (by rw [hcb]; exact hc)
  have hin : scanWhile pred bs st i < st ∧ scanWhile pred bs st i < bs.size := by
    rw [hscan]; omega
  simp only [runThen, hin, and_self, ↓reduceDIte]
  simp only [hscan, hcb, seg_extract, hv, List.length_append, List.length_singleton,
    Nat.add_assoc]

/-- The bundle: a run of `pred` bytes and the byte that ends it. -/
@[inline] def Grammar.runThen (pred : UInt8 → Bool) : Grammar (Bytes × UInt8) :=
  ⟨Spec.runThen pred, Http1.runThen pred⟩

instance Grammar.lawful_runThen (pred : UInt8 → Bool) : (Grammar.runThen pred).Lawful :=
  ⟨sound_runThen pred, complete_runThen pred⟩

theorem Grammar.runThen_G {pred : UInt8 → Bool} {v : Bytes} {c : UInt8}
    (hv : ∀ b ∈ v, pred b = true) (hc : pred c = false) :
    (Grammar.runThen pred).G (v ++ [c]) (v, c) := ⟨rfl, hv, hc⟩

theorem runThen_nonEmpty (pred : UInt8 → Bool) : NonEmpty (Grammar.runThen pred).G := by
  rintro l ⟨v, c⟩ ⟨rfl, -, -⟩
  simp

/-! ## Delimited runs -/

/-- A run of `pred` bytes ended by exactly `stop` (consumed, not returned); nonempty when
`ne`. -/
@[inline] def Grammar.delim (what : String) (pred : UInt8 → Bool) (stop : UInt8) (ne : Bool) :
    Grammar Bytes :=
  (Grammar.runThen pred).filterMap what
    (fun r => if r.2 = stop ∧ (ne = true → r.1 ≠ []) then some r.1 else none)

instance Grammar.lawful_delim (what : String) (pred : UInt8 → Bool) (stop : UInt8) (ne : Bool) :
    (Grammar.delim what pred stop ne).Lawful := by
  unfold Grammar.delim; grammar_lawful

theorem Grammar.delim_G_iff {what : String} {pred : UInt8 → Bool} {stop : UInt8} {ne : Bool}
    {l v : Bytes} : (Grammar.delim what pred stop ne).G l v ↔
      l = v ++ [stop] ∧ (∀ b ∈ v, pred b = true) ∧ pred stop = false ∧ (ne = true → v ≠ []) := by
  constructor
  · rintro ⟨⟨v', c⟩, ⟨hl, hv, hc⟩, hf⟩
    have hf' : (if c = stop ∧ (ne = true → v' ≠ []) then some v' else none) = some v := hf
    split at hf'
    · next h =>
      obtain ⟨hcs, hne⟩ := h
      cases hf'
      subst hcs
      exact ⟨hl, hv, hc, hne⟩
    · cases hf'
  · rintro ⟨rfl, hv, hc, hne⟩
    refine ⟨(v, stop), ⟨rfl, hv, hc⟩, ?_⟩
    show (if stop = stop ∧ (ne = true → v ≠ []) then some v else none) = some v
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, hne⟩)

theorem Grammar.delim_G {what : String} {pred : UInt8 → Bool} {stop : UInt8} {ne : Bool}
    {v : Bytes} (hv : ∀ b ∈ v, pred b = true) (hc : pred stop = false) (hne : ne = true → v ≠ []) :
    (Grammar.delim what pred stop ne).G (v ++ [stop]) v :=
  Grammar.delim_G_iff.2 ⟨rfl, hv, hc, hne⟩

/-- The grammar of a literal relates exactly its bytes. -/
theorem Grammar.lit_G_eq : ∀ {l l' : Bytes} {u : Unit}, (Grammar.lit l).G l' u → l' = l
  | [], _, _, h => h.1
  | _ :: _, _, _, ⟨_, _, _, rfl, rfl, h⟩ => by rw [Grammar.lit_G_eq h]; rfl

end Silmaril.Net.Http1
