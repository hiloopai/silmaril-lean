module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.ReadStep

/-!
# Proofs: the read invariant of WASI 0.3 over 0.2

`RdJ c q2 q3` relates the component's input bindings to the state `q2` of the 0.2 read theory
`fsRead2 F` and the state `q3` of the 0.3 read theory `fsReadTh3w F`:

* a 0.3 stream the theory knows (`rest q3 r = some _`) is `0` or bound to a file;
* a live file binding of `r` to the 0.2 stream `is` has the same rest on both sides;
* a file binding at its end has an empty rest; a stdin binding is unknown to the 0.3 theory;
* live bindings have distinct 0.2 streams; handles from `next` on are unknown.

`DFrame`: a change of the state that keeps every binding or kills it (`dead`), with `next` not
decreasing; it keeps the invariant (`RdJ.dframe`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy blocked CopyResult Store)
open Silmaril.Wasi.Versions.P3

/-- Lookup in a binding list. -/
def lk (l : List (Nat × InB)) (r : Nat) : Option InB := (l.find? (·.1 = r)).map (·.2)

theorem inOf_eq (c : Core) (r : Nat) : c.inOf r = lk c.ins r := rfl

/-- Lookup in a list mapped by a key-preserving function. -/
theorem lk_map (h : Nat → InB → InB) (l : List (Nat × InB)) (r : Nat) :
    lk (l.map fun e => (e.1, h e.1 e.2)) r = (lk l r).map (h r) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    by_cases he : e.1 = r
    · simp [lk, he]
    · simpa [lk, he] using ih

/-- Lookup in a list with a new head. -/
theorem lk_cons (r0 : Nat) (ib : InB) (l : List (Nat × InB)) (r : Nat) :
    lk ((r0, ib) :: l) r = if r0 = r then some ib else lk l r := by
  by_cases h : r0 = r <;> simp [lk, h]

/-- The bindings after `setMode`. -/
theorem inOf_setMode (c : Core) (r : Nat) (m : IMode) (r' : Nat) :
    (c.setMode r m).inOf r' =
      if r' = r then (c.inOf r').map fun ib => { ib with mode := m } else c.inOf r' := by
  have hl := lk_map (fun k ib => if k = r then { ib with mode := m } else ib) c.ins r'
  have hmap : c.ins.map (fun e => if e.1 = r then (e.1, { e.2 with mode := m }) else e) =
      c.ins.map (fun e => (e.1, if e.1 = r then { e.2 with mode := m } else e.2)) := by
    apply List.map_congr_left
    intro e _
    split <;> rfl
  simp only [Core.setMode, inOf_eq, hmap, hl]
  split
  · rename_i h; subst h; simp
  · cases lk c.ins r' <;> simp

/-- The bindings after `killIs`. -/
theorem lk_killIs (is : BitVec 32) (l : List (Nat × InB)) (r : Nat) :
    lk (killIs is l) r = (lk l r).map fun ib => if ib.is = is then { ib with mode := .dead } else ib := by
  have hl := lk_map (fun _ ib => if ib.is = is then { ib with mode := .dead } else ib) l r
  have hmap : killIs is l =
      l.map (fun e => (e.1, if e.2.is = is then { e.2 with mode := .dead } else e.2)) := by
    unfold killIs
    apply List.map_congr_left
    intro e _
    split <;> rfl
  rw [hmap, hl]

/-- A change that keeps or kills every binding. -/
structure DFrame (c c' : Core) : Prop where
  next : c.st.next ≤ c'.st.next
  ins : ∀ r, c'.inOf r = c.inOf r ∨ ∃ ib, c.inOf r = some ib ∧ c'.inOf r = some { ib with mode := .dead }

theorem DFrame.of_ins {c c' : Core} (h : c.st.next ≤ c'.st.next) (hi : c'.ins = c.ins) :
    DFrame c c' := ⟨h, fun r => Or.inl (by simp [inOf_eq, hi])⟩

theorem DFrame.trans {c c' c'' : Core} (h : DFrame c c') (h' : DFrame c' c'') : DFrame c c'' := by
  refine ⟨Nat.le_trans h.next h'.next, fun r => ?_⟩
  rcases h'.ins r with h2 | ⟨ib, h2, h3⟩ <;> rcases h.ins r with h1 | ⟨ib', h1, h1'⟩
  · exact Or.inl (h2.trans h1)
  · exact Or.inr ⟨ib', h1, h2.trans h1'⟩
  · exact Or.inr ⟨ib, h1 ▸ h2, h3⟩
  · rw [h1'] at h2
    simp only [Option.some.injEq] at h2
    subst h2
    exact Or.inr ⟨ib', h1, h3⟩

theorem DFrame.setDead (c : Core) (r : Nat) : DFrame c (c.setMode r .dead) := by
  refine ⟨Nat.le_refl _, fun r' => ?_⟩
  rw [inOf_setMode]
  split
  · cases h : c.inOf r' with
    | none => exact Or.inl rfl
    | some ib => exact Or.inr ⟨ib, rfl, rfl⟩
  · exact Or.inl rfl

/-- **The read invariant.** -/
structure RdJ (c : Core) (q2 q3 : RdSt) : Prop where
  pos : 1 ≤ c.st.next
  known : ∀ r bs, rest q3 r = some bs → r = 0 ∨ ∃ ib, c.inOf r = some ib ∧ ib.file = true
  bound : ∀ r ib, c.inOf r = some ib → 0 < r ∧ r < c.st.next
  live : ∀ r ib, c.inOf r = some ib → ib.file = true → ib.mode = .live →
    ∃ bs, rest q3 r = some bs ∧ rest q2 ib.is.toNat = some bs
  eof : ∀ r ib, c.inOf r = some ib → ib.file = true → ib.mode = .eof → rest q3 r = some []
  stdin : ∀ r ib, c.inOf r = some ib → ib.file = false → rest q3 r = none
  uniq : ∀ r ib r' ib', c.inOf r = some ib → c.inOf r' = some ib' → ib.mode = .live →
    ib'.mode = .live → ib.is = ib'.is → r = r'
  fresh : ∀ r, c.st.next ≤ r → rest q3 r = none

/-- The invariant holds initially. -/
theorem RdJ.init (F : BitVec 32 → List (BitVec 8)) :
    RdJ ({} : Core) (fsRead2 F).init (fsReadTh3w F).init := by
  refine ⟨Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intros <;> simp_all [rest, Core.inOf, fsReadTh3w]

/-- A binding after a `DFrame` comes from a binding before it, kept or killed. -/
theorem DFrame.back {c c' : Core} (hf : DFrame c c') (r : Nat) (ib' : InB) (hr : c'.inOf r = some ib') :
    ∃ ib, c.inOf r = some ib ∧ ib'.is = ib.is ∧ ib'.file = ib.file ∧
      (ib'.mode = ib.mode ∨ ib'.mode = .dead) := by
  rcases hf.ins r with h1 | ⟨ib, h1, h2⟩
  · exact ⟨ib', h1 ▸ hr, rfl, rfl, Or.inl rfl⟩
  · rw [h2] at hr
    simp only [Option.some.injEq] at hr
    subst hr
    exact ⟨ib, h1, rfl, rfl, Or.inr rfl⟩

/-- Known 0.3 streams stay bound to files after a `DFrame`. -/
theorem RdJ.dframe_known {c c' : Core} {q2 q3 : RdSt} (h : RdJ c q2 q3) (hf : DFrame c c')
    (r : Nat) (bs : List (BitVec 8)) (hr : rest q3 r = some bs) :
    r = 0 ∨ ∃ ib, c'.inOf r = some ib ∧ ib.file = true := by
  rcases h.known r bs hr with h0 | ⟨ib, hib, hfile⟩
  · exact Or.inl h0
  · rcases hf.ins r with h1 | ⟨ib0, h1, h2⟩
    · exact Or.inr ⟨ib, h1.trans hib, hfile⟩
    · rw [hib] at h1
      simp only [Option.some.injEq] at h1
      subst h1
      exact Or.inr ⟨_, h2, hfile⟩

/-- Live bindings stay unique after a `DFrame`. -/
theorem RdJ.dframe_uniq {c c' : Core} {q2 q3 : RdSt} (h : RdJ c q2 q3) (hf : DFrame c c')
    (r : Nat) (ib' : InB) (r' : Nat) (ib'' : InB) (hr : c'.inOf r = some ib')
    (hr' : c'.inOf r' = some ib'') (hm : ib'.mode = .live) (hm' : ib''.mode = .live)
    (hiseq : ib'.is = ib''.is) : r = r' := by
  obtain ⟨ib, hib, his, -, hmo⟩ := hf.back r ib' hr
  obtain ⟨ib2, hib2, his2, -, hmo2⟩ := hf.back r' ib'' hr'
  have hl1 : ib.mode = .live := hmo.elim (fun e => e ▸ hm) (fun e => by rw [e] at hm; cases hm)
  have hl2 : ib2.mode = .live := hmo2.elim (fun e => e ▸ hm') (fun e => by rw [e] at hm'; cases hm')
  exact h.uniq r ib r' ib2 hib hib2 hl1 hl2 (his.symm.trans (hiseq.trans his2))

/-- **The invariant survives a change that keeps or kills bindings.** -/
theorem RdJ.dframe {c c' : Core} {q2 q3 : RdSt} (h : RdJ c q2 q3) (hf : DFrame c c') :
    RdJ c' q2 q3 := by
  refine ⟨Nat.le_trans h.pos hf.next, h.dframe_known hf, fun r ib' hr => ?_,
    fun r ib' hr hfile hm => ?_, fun r ib' hr hfile hm => ?_, fun r ib' hr hfile => ?_,
    h.dframe_uniq hf, fun r hr => h.fresh r (Nat.le_trans hf.next hr)⟩
  · obtain ⟨ib, hib, -⟩ := hf.back r ib' hr
    obtain ⟨h1, h2⟩ := h.bound r ib hib
    exact ⟨h1, Nat.lt_of_lt_of_le h2 hf.next⟩
  · obtain ⟨ib, hib, his, hfi, hmo⟩ := hf.back r ib' hr
    have hl : ib.mode = .live := hmo.elim (fun e => e ▸ hm) (fun e => by rw [e] at hm; cases hm)
    rw [his]
    exact h.live r ib hib (hfi ▸ hfile) hl
  · obtain ⟨ib, hib, -, hfi, hmo⟩ := hf.back r ib' hr
    have he : ib.mode = .eof := hmo.elim (fun e => e ▸ hm) (fun e => by rw [e] at hm; cases hm)
    exact h.eof r ib hib (hfi ▸ hfile) he
  · obtain ⟨ib, hib, -, hfi, -⟩ := hf.back r ib' hr
    exact h.stdin r ib hib (hfi ▸ hfile)

end Silmaril.Wasi.Versions.P3OverP2

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Wasi
open Silmaril.Wasi.Versions.P3

/-- **The invariant after a change at one binding**: the live binding of `r` to `ib.is` takes the
mode `m'`; the 0.2 state changes only at `ib.is`, the 0.3 state only at `r`. -/
theorem RdJ.at {c c' : Core} {q2 q3 q2' q3' : RdSt} (h : RdJ c q2 q3) {r : Nat} {ib : InB}
    (hr : c.inOf r = some ib) (hlive : ib.mode = .live) (m' : IMode)
    (hn : c'.st.next = c.st.next)
    (hc' : ∀ r'', c'.inOf r'' = if r'' = r then some { ib with mode := m' } else c.inOf r'')
    (h2 : ∀ k, k ≠ ib.is.toNat → rest q2' k = rest q2 k)
    (h3 : ∀ r'', r'' ≠ r → rest q3' r'' = rest q3 r'')
    (hfl : ib.file = true → m' = .live → ∃ bs, rest q3' r = some bs ∧ rest q2' ib.is.toNat = some bs)
    (hfe : ib.file = true → m' = .eof → rest q3' r = some [])
    (hsd : ib.file = false → rest q3' r = none)
    (hkn : ∀ bs, rest q3' r = some bs → ib.file = true) : RdJ c' q2' q3' := by
  have hb := h.bound r ib hr
  refine ⟨hn ▸ h.pos, fun r'' bs hq => ?_, fun r'' ib'' hq => ?_, fun r'' ib'' hq hfile hm => ?_,
    fun r'' ib'' hq hfile hm => ?_, fun r'' ib'' hq hfile => ?_,
    fun r1 ib1 r2 ib2 hq1 hq2 hm1 hm2 his => ?_, fun r'' hr'' => ?_⟩
  · by_cases he : r'' = r
    · subst he; exact Or.inr ⟨{ ib with mode := m' }, by rw [hc']; simp, hkn bs hq⟩
    · rcases h.known r'' bs ((h3 r'' he) ▸ hq) with h0 | ⟨ib0, h1, h2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨ib0, by rw [hc']; simp [he, h1], h2⟩
  · rw [hc'] at hq
    split at hq
    · rename_i he; subst he; rw [hn]; exact hb
    · rw [hn]; exact h.bound r'' ib'' hq
  · rw [hc'] at hq
    split at hq
    · rename_i he; subst he
      simp only [Option.some.injEq] at hq; subst hq
      exact hfl hfile hm
    · rename_i he
      obtain ⟨bs, h1, h1'⟩ := h.live r'' ib'' hq hfile hm
      refine ⟨bs, (h3 r'' he) ▸ h1, ?_⟩
      have hne : ib''.is ≠ ib.is := fun hi => he (h.uniq r'' ib'' r ib hq hr hm hlive hi)
      rw [h2 _ (fun hk => hne (BitVec.eq_of_toNat_eq hk))]
      exact h1'
  · rw [hc'] at hq
    split at hq
    · rename_i he; subst he
      simp only [Option.some.injEq] at hq; subst hq
      exact hfe hfile hm
    · rename_i he; rw [h3 r'' he]; exact h.eof r'' ib'' hq hfile hm
  · rw [hc'] at hq
    split at hq
    · rename_i he; subst he
      simp only [Option.some.injEq] at hq; subst hq
      exact hsd hfile
    · rename_i he; rw [h3 r'' he]; exact h.stdin r'' ib'' hq hfile
  · rw [hc'] at hq1 hq2
    split at hq1 <;> split at hq2
    · rename_i h1 h2; exact h1.trans h2.symm
    · rename_i h1 h2
      simp only [Option.some.injEq] at hq1; subst hq1
      exact absurd (h.uniq r ib r2 ib2 hr hq2 hlive hm2 his).symm (h1 ▸ h2)
    · rename_i h1 h2
      simp only [Option.some.injEq] at hq2; subst hq2
      exact absurd (h.uniq r1 ib1 r ib hq1 hr hm1 hlive his) (h2 ▸ h1)
    · exact h.uniq r1 ib1 r2 ib2 hq1 hq2 hm1 hm2 his
  · have hne : r'' ≠ r := by omega
    rw [h3 r'' hne]
    exact h.fresh r'' (hn ▸ hr'')

/-- How `killIs` changes one binding. -/
def killF (dd : Option (BitVec 32)) (ib : InB) : InB :=
  match dd with
  | some is => if ib.is = is then { ib with mode := .dead } else ib
  | none => ib

/-- A binding left live by `killIs` is unchanged and not of the killed stream. -/
theorem killF_live {dd : Option (BitVec 32)} {ib0 : InB} (hm : (killF dd ib0).mode = .live) :
    killF dd ib0 = ib0 ∧ ∀ is, dd = some is → ib0.is ≠ is := by
  cases dd with
  | none => exact ⟨rfl, fun _ h => by cases h⟩
  | some is =>
    simp only [killF] at hm ⊢
    split at hm
    · simp at hm
    · rename_i hne
      simp only [hne, ite_false]
      exact ⟨trivial, fun is' h' => by cases h'; exact hne⟩

/-- `killIs` keeps the file flag and does not create ends. -/
theorem killF_file (dd : Option (BitVec 32)) (ib0 : InB) :
    (killF dd ib0).file = ib0.file ∧ ((killF dd ib0).mode = .eof → ib0.mode = .eof) := by
  cases dd with
  | none => exact ⟨rfl, id⟩
  | some is =>
    simp only [killF]
    split
    · exact ⟨rfl, fun h => by simp at h⟩
    · exact ⟨rfl, id⟩

/-- The new binding of `finIn`. -/
def newIn (c : Core) (file : Bool) (dd : Option (BitVec 32)) : InB :=
  ⟨dd.getD 0, file, c.st.next + 2, if dd.isSome then .live else .dead⟩

/-- The bindings after `finIn`. -/
theorem finIn_inOf {c : Core} (hroom : c.room = true) (file : Bool) (dd : Option (BitVec 32))
    (r : Nat) : (P3OverP2.finIn c file dd).1.inOf r =
      if c.st.next = r then some (newIn c file dd) else (c.inOf r).map (killF dd) := by
  obtain ⟨-, -, -, -, -, hi⟩ := finIn_room hroom file dd
  rw [inOf_eq, hi, lk_cons]
  split
  · rfl
  · cases dd with
    | none => cases hc : c.inOf r <;> simp_all [inOf_eq, killF]
    | some is => rw [lk_killIs]; rfl

/-- A binding after `finIn` is the new one, or an old one through `killIs`. -/
theorem finIn_inOf_cases {c : Core} (hroom : c.room = true) {file : Bool} {dd : Option (BitVec 32)}
    {r : Nat} {ib : InB} (hq : (P3OverP2.finIn c file dd).1.inOf r = some ib) :
    (r = c.st.next ∧ ib = newIn c file dd) ∨
      (r ≠ c.st.next ∧ ∃ ib0, c.inOf r = some ib0 ∧ ib = killF dd ib0) := by
  rw [finIn_inOf hroom] at hq
  split at hq
  · rename_i he
    exact Or.inl ⟨he.symm, (Option.some.inj hq).symm⟩
  · rename_i he
    cases hc : c.inOf r with
    | none => rw [hc] at hq; cases hq
    | some ib0 =>
      rw [hc] at hq
      exact Or.inr ⟨Ne.symm he, ib0, rfl, (Option.some.inj hq).symm⟩

/-- The 0.3 rests after `finIn`, away from the new end. -/
theorem finIn_h3r {q3 q3' : RdSt} {file : Bool} {r0 : Nat} {bs0 : List (BitVec 8)}
    (h3 : q3' = if file then setRest q3 r0 bs0 else q3) (r : Nat) (hr : r ≠ r0) :
    rest q3' r = rest q3 r := by
  subst h3
  split
  · exact rest_setRest_ne _ _ hr
  · rfl

/-- `known` after `finIn`. -/
theorem RdJ.finIn_known {c : Core} {q2 q3 q3' : RdSt} (h : RdJ c q2 q3) (hroom : c.room = true)
    {file : Bool} {dd : Option (BitVec 32)} {bs0 : List (BitVec 8)}
    (h3 : q3' = if file then setRest q3 c.st.next bs0 else q3) (r : Nat) (bs : List (BitVec 8))
    (hq : rest q3' r = some bs) :
    r = 0 ∨ ∃ ib, (P3OverP2.finIn c file dd).1.inOf r = some ib ∧ ib.file = true := by
  by_cases he : r = c.st.next
  · subst he
    have hf : file = true := by
      subst h3; split at hq
      · assumption
      · rw [h.fresh _ (Nat.le_refl _)] at hq; cases hq
    exact Or.inr ⟨newIn c file dd, by rw [finIn_inOf hroom]; simp, hf⟩
  · rcases h.known r bs ((finIn_h3r h3 r he) ▸ hq) with h0 | ⟨ib, h1, h1f⟩
    · exact Or.inl h0
    · refine Or.inr ⟨killF dd ib, by rw [finIn_inOf hroom]; simp [Ne.symm he, h1], ?_⟩
      rw [(killF_file dd ib).1]; exact h1f

/-- `live` after `finIn`. -/
theorem RdJ.finIn_live {c : Core} {q2 q3 q2' q3' : RdSt} (h : RdJ c q2 q3) (hroom : c.room = true)
    {file : Bool} {dd : Option (BitVec 32)} {bs0 : List (BitVec 8)}
    (h2 : ∀ k, (∀ is, dd = some is → k ≠ is.toNat) → rest q2' k = rest q2 k)
    (h2f : ∀ is, file = true → dd = some is → rest q2' is.toNat = some bs0)
    (h3 : q3' = if file then setRest q3 c.st.next bs0 else q3) (r : Nat) (ib : InB)
    (hq : (P3OverP2.finIn c file dd).1.inOf r = some ib) (hfile : ib.file = true)
    (hm : ib.mode = .live) : ∃ bs, rest q3' r = some bs ∧ rest q2' ib.is.toNat = some bs := by
  rcases finIn_inOf_cases hroom hq with ⟨rfl, rfl⟩ | ⟨he, ib0, hc, rfl⟩
  · cases dd with
    | none => simp [newIn] at hm
    | some is =>
      have hf : file = true := hfile
      refine ⟨bs0, ?_, h2f is hf rfl⟩
      subst h3; simp [hf, rest_setRest_eq]
  · obtain ⟨hk, hdiff⟩ := killF_live hm
    rw [hk] at hm hfile ⊢
    obtain ⟨bs, h1, h1'⟩ := h.live r ib0 hc hfile hm
    refine ⟨bs, (finIn_h3r h3 r he) ▸ h1, ?_⟩
    rw [h2 _ (fun is h' hk => hdiff is h' (BitVec.eq_of_toNat_eq hk))]
    exact h1'

/-- `eof` after `finIn`. -/
theorem RdJ.finIn_eof {c : Core} {q2 q3 q3' : RdSt} (h : RdJ c q2 q3) (hroom : c.room = true)
    {file : Bool} {dd : Option (BitVec 32)} {bs0 : List (BitVec 8)}
    (h3 : q3' = if file then setRest q3 c.st.next bs0 else q3) (r : Nat) (ib : InB)
    (hq : (P3OverP2.finIn c file dd).1.inOf r = some ib) (hfile : ib.file = true)
    (hm : ib.mode = .eof) : rest q3' r = some [] := by
  rcases finIn_inOf_cases hroom hq with ⟨rfl, rfl⟩ | ⟨he, ib0, hc, rfl⟩
  · cases dd <;> simp [newIn] at hm
  · have hm0 : ib0.mode = .eof := (killF_file dd ib0).2 hm
    rw [finIn_h3r h3 r he]
    exact h.eof r ib0 hc ((killF_file dd ib0).1 ▸ hfile) hm0

/-- `stdin` after `finIn`. -/
theorem RdJ.finIn_stdin {c : Core} {q2 q3 q3' : RdSt} (h : RdJ c q2 q3) (hroom : c.room = true)
    {file : Bool} {dd : Option (BitVec 32)} {bs0 : List (BitVec 8)}
    (h3 : q3' = if file then setRest q3 c.st.next bs0 else q3) (r : Nat) (ib : InB)
    (hq : (P3OverP2.finIn c file dd).1.inOf r = some ib) (hfile : ib.file = false) :
    rest q3' r = none := by
  rcases finIn_inOf_cases hroom hq with ⟨rfl, rfl⟩ | ⟨he, ib0, hc, rfl⟩
  · have hf : file = false := hfile
    subst h3
    simp only [hf]
    exact h.fresh _ (Nat.le_refl _)
  · rw [finIn_h3r h3 r he]
    exact h.stdin r ib0 hc ((killF_file dd ib0).1 ▸ hfile)

/-- A live binding after `finIn`: the new one of the stream `dd`, or an old one of another
stream. -/
theorem finIn_live_view {c : Core} (hroom : c.room = true) {file : Bool} {dd : Option (BitVec 32)}
    {r : Nat} {ib : InB} (hq : (P3OverP2.finIn c file dd).1.inOf r = some ib) (hm : ib.mode = .live) :
    (r = c.st.next ∧ dd = some ib.is) ∨
      (r ≠ c.st.next ∧ c.inOf r = some ib ∧ ∀ is, dd = some is → ib.is ≠ is) := by
  rcases finIn_inOf_cases hroom hq with ⟨rfl, rfl⟩ | ⟨he, ib0, hc, rfl⟩
  · cases dd with
    | none => simp [newIn] at hm
    | some is => exact Or.inl ⟨rfl, rfl⟩
  · obtain ⟨hk, hdiff⟩ := killF_live hm
    rw [hk]
    exact Or.inr ⟨he, hc, hdiff⟩

/-- `uniq` after `finIn`: the new binding kills the old live bindings of its stream. -/
theorem RdJ.finIn_uniq {c : Core} {q2 q3 : RdSt} (h : RdJ c q2 q3) (hroom : c.room = true)
    {file : Bool} {dd : Option (BitVec 32)} (r1 : Nat) (ib1 : InB) (r2 : Nat) (ib2 : InB)
    (hq1 : (P3OverP2.finIn c file dd).1.inOf r1 = some ib1)
    (hq2 : (P3OverP2.finIn c file dd).1.inOf r2 = some ib2) (hm1 : ib1.mode = .live)
    (hm2 : ib2.mode = .live) (his : ib1.is = ib2.is) : r1 = r2 := by
  rcases finIn_live_view hroom hq1 hm1 with ⟨h1, h1'⟩ | ⟨h1, h1', h1''⟩ <;>
    rcases finIn_live_view hroom hq2 hm2 with ⟨h2, h2'⟩ | ⟨h2, h2', h2''⟩
  · exact h1.trans h2.symm
  · exact absurd his.symm (h2'' _ h1')
  · exact absurd his (h1'' _ h2')
  · exact h.uniq r1 ib1 r2 ib2 h1' h2' hm1 hm2 his

/-- **The invariant after a new binding** of the fresh readable end `next` to the 0.2 stream of
`dd` (`killIs` kills the old live bindings of that stream). For a file, the 0.3 theory records
`bs0` at `next` and the 0.2 theory at the 0.2 stream. -/
theorem RdJ.finIn {c : Core} {q2 q3 q2' q3' : RdSt} (h : RdJ c q2 q3) (hroom : c.room = true)
    (file : Bool) (dd : Option (BitVec 32)) (bs0 : List (BitVec 8))
    (h2 : ∀ k, (∀ is, dd = some is → k ≠ is.toNat) → rest q2' k = rest q2 k)
    (h2f : ∀ is, file = true → dd = some is → rest q2' is.toNat = some bs0)
    (h3 : q3' = if file then setRest q3 c.st.next bs0 else q3) :
    RdJ (P3OverP2.finIn c file dd).1 q2' q3' := by
  obtain ⟨-, -, hn, -, -, -⟩ := finIn_room hroom file dd
  have hpos : 1 ≤ c.st.next := h.pos
  refine ⟨by omega, h.finIn_known hroom h3, fun r ib hq => ?_, h.finIn_live hroom h2 h2f h3,
    h.finIn_eof hroom h3, h.finIn_stdin hroom h3, h.finIn_uniq hroom, fun r hr => ?_⟩
  · rcases finIn_inOf_cases hroom hq with ⟨rfl, -⟩ | ⟨-, ib0, hc, -⟩
    · rw [hn]; omega
    · have := h.bound r ib0 hc
      rw [hn]; omega
  · rw [hn] at hr
    rw [finIn_h3r h3 r (by omega)]
    exact h.fresh r (by omega)

end Silmaril.Wasi.Versions.P3OverP2
