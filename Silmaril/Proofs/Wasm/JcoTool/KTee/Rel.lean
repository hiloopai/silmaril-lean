module

public import Silmaril.Proofs.Wasm.JcoTool.KTee.Exec

/-!
# The generated tee: the relation, piece by piece

`qOf_congr`, `ORel_congr`: what an output's relation depends on. `trB_feed`, `push_nil`: the
node's side. `relT_of`: assembling the relation of a running machine.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KTee

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Event EventCode blocked)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (NSt OS RV Node NStep rh wh status count)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KTee

abbrev NOut := Silmaril.Wasm.Component.Streams.Net.Out

/-- `Net.Out.onWrite`. -/
abbrev onWr (o : NOut) (p : Nat) : NOut := o.onWrite p

/-! ## The node's side -/

theorem trB_feed (s : Unit) (xs : List Val) : trB.feed s xs = ((), xs.map nrm) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [Tr.feed, trB, Tr.map, List.map_cons]
    have := ih ()
    simp only [trB, Tr.map] at this
    simp [this]

theorem trB_flush (s : Unit) : trB.flush s = [] := rfl

theorem trB_done (s : Unit) : trB.done s = false := rfl

theorem push_nil (o : NOut) : o.push [] = o := by
  rcases o with ⟨st, a⟩
  cases st <;> simp [Silmaril.Wasm.Component.Streams.Net.Out.push]

theorem teeNode_inp (a b c : Nat) : (teeNode a b c).inp = some a := rfl

theorem teeNode_out0 (a b c : Nat) : (teeNode a b c).outs[0]? = some b := rfl

theorem teeNode_out1 (a b c : Nat) : (teeNode a b c).outs[1]? = some c := rfl

theorem teeNode_T (a b c : Nat) : (teeNode a b c).T = trB := rfl

/-! ## The bytes an output has to write -/

theorem qOf_congr {ms ms' : MS} {j : Nat} (hL : ms'.g LENg = ms.g LENg)
    (hO : ms'.g (OFFg j) = ms.g (OFFg j)) (hm : ∀ i, i < ms.g LENg → ms'.m (IN + i) = ms.m (IN + i)) :
    qOf ms' j = qOf ms j := by
  unfold qOf
  rw [hL, hO, slice_congr hm]

theorem ORel_congr {ms ms' : MS} {j : Nat} {o : NOut} (h : ORel ms j o)
    (hb : ms'.m (aO j) = ms.m (aO j)) (hq : qOf ms' j = qOf ms j) : ORel ms' j o := by
  unfold ORel at h ⊢
  rw [hb, hq]
  exact h

/-- Writing a state byte keeps the batch. -/
theorem mem_upd_lo {m : Nat → Nat} {a v : Nat} (ha : a < IN) (i : Nat) :
    upd m a v (IN + i) = m (IN + i) := by
  simp only [upd_apply, show IN + i ≠ a by omega, ↓reduceIte]

theorem qOf_len (ms : MS) (j : Nat) : (qOf ms j).length = ms.g LENg - ms.g (OFFg j) := by
  simp [qOf, slice_length]

theorem qOf_slice (ms : MS) (j : Nat) :
    qOf ms j = (slice ms.m (IN + ms.g (OFFg j)) (ms.g LENg - ms.g (OFFg j))).map u8v := by
  simp [qOf, slice_drop]

theorem qOf_nil {ms : MS} {j : Nat} (h : ms.g LENg ≤ ms.g (OFFg j)) : qOf ms j = [] := by
  rw [← List.length_eq_zero_iff, qOf_len]; omega

/-! ## Assembling the relation -/

theorem relT_live {r w₀ w₁ s : Nat} {ms : MS} {x : NSt Unit} (hlen : x.outs.length = 2)
    (hm : ms.mode = .ready ∨ ms.mode = .waiting s) (hok : okT ms r w₀ w₁ s) (hI : IRel r ms x)
    (hO : ∀ j, j ≤ 1 → ∃ o, x.outs[j]? = some o ∧ ORel ms j o) : RelT r w₀ w₁ s ms x := by
  have hne : ms.mode ≠ .exited := by rcases hm with h | h <;> rw [h] <;> simp
  refine ⟨hlen, ?_⟩
  simp only [hne, ↓reduceIte]
  exact ⟨hm, hok, hI, hO⟩

theorem relT_inv {r w₀ w₁ s : Nat} {ms : MS} {x : NSt Unit} (h : RelT r w₀ w₁ s ms x)
    (hne : ms.mode ≠ .exited) :
    x.outs.length = 2 ∧ (ms.mode = .ready ∨ ms.mode = .waiting s) ∧ okT ms r w₀ w₁ s ∧ IRel r ms x ∧
      ∀ j, j ≤ 1 → ∃ o, x.outs[j]? = some o ∧ ORel ms j o := by
  obtain ⟨hlen, h⟩ := h
  simp only [hne, ↓reduceIte] at h
  exact ⟨hlen, h⟩

/-- The outputs after replacing output `j`. -/
theorem outs_set {l : List NOut} {j k : Nat} {o' : NOut} (hk : k ≠ j) :
    (l.set j o')[k]? = l[k]? := by
  rw [List.getElem?_set]; simp [Ne.symm hk]

theorem outs_set_self {l : List NOut} {j : Nat} {o' : NOut} (hj : j < l.length) :
    (l.set j o')[j]? = some o' := by
  rw [List.getElem?_set]; simp [hj]

/-- An output whose state has the form `⟨st, a⟩`. -/
theorem out_eta (o : NOut) : o = ⟨o.st, o.ack⟩ := rfl

/-! ## The input's relation -/

theorem IRel_congr {r : Nat} {ms ms' : MS} {x x' : NSt Unit} (h : IRel r ms x)
    (hm : ms'.m aRS = ms.m aRS) (hrp : ms'.rp = ms.rp) (hL : ms'.g LENg = ms.g LENg)
    (hrd : x'.rd = x.rd) : IRel r ms' x' := by
  unfold IRel at h ⊢
  rw [hm, hrp, hL, hrd]
  exact h

/-! ## After a write -/

theorem onWS_g_other {j k p : Nat} {g m : Nat → Nat} (hk : k ≠ OFFg j) : (onWS j p g m).1 k = g k := by
  unfold onWS; split <;> simp [upd_apply, hk]

theorem onWS_m_other {j k p : Nat} {g m : Nat → Nat} (hk : k ≠ aO j) : (onWS j p g m).2 k = m k := by
  unfold onWS; split <;> simp [upd_apply, hk]

theorem onWS_off_le {j p : Nat} {g m : Nat → Nat} (hle : g (OFFg j) ≤ g LENg) :
    (onWS j p g m).1 (OFFg j) ≤ (onWS j p g m).1 LENg := by
  have hne := OFFg_ne_LEN j
  unfold onWS; split
  · simp only [upd_apply, ↓reduceIte, Ne.symm hne]
    split <;> omega
  · exact hle

/-- After a `COMPLETED` write of `p / 16` bytes the output has the rest of its bytes to write. -/
theorem qOf_onWS {ms : MS} {j p : Nat} (hj : j ≤ 1) (hs : p % 16 = 0) (rp : Option (Nat × Nat))
    (md : Mode) : qOf ⟨(onWS j p ms.g ms.m).1, (onWS j p ms.g ms.m).2, rp, md⟩ j = (qOf ms j).drop (p / 16) := by
  have hne := OFFg_ne_LEN j
  have hA : aO j < IN := aO_lt j hj
  have hsl : slice (upd ms.m (aO j) 0) IN (ms.g LENg) = slice ms.m IN (ms.g LENg) :=
    slice_congr fun i _ => mem_upd_lo hA i
  simp only [onWS, hs, ↓reduceIte, qOf, upd_apply, Ne.symm hne]
  rw [hsl, List.map_drop, List.map_drop, List.drop_drop]
  split
  · rw [List.drop_eq_nil_of_le (by simp [slice_length]),
      List.drop_eq_nil_of_le (by simp [slice_length]; omega)]
  · rfl

/-- **The output written, by its result**: `onWS` against `Out.onWrite` of a pending write. -/
theorem ORel_onWS {ms : MS} {j p : Nat} {o : NOut} (hj : j ≤ 1) (hq : o.st = .busy (qOf ms j) [])
    (rp : Option (Nat × Nat)) (md : Mode) :
    ORel ⟨(onWS j p ms.g ms.m).1, (onWS j p ms.g ms.m).2, rp, md⟩ j (o.onWrite p) := by
  unfold Silmaril.Wasm.Component.Streams.Net.Out.onWrite
  rw [hq]
  by_cases hs : p % 16 = 0
  · have hst : status p = 0 := hs
    have hb : (onWS j p ms.g ms.m).2 (aO j) = 0 := by simp [onWS, hs, upd_apply]
    simp only [hst, ↓reduceIte, List.append_nil, count]
    exact .inl ⟨hb, by rw [qOf_onWS hj hs]⟩
  · have hst : status p ≠ 0 := hs
    have hb : (onWS j p ms.g ms.m).2 (aO j) = 2 := by simp [onWS, hs, upd_apply]
    simp only [hst, ↓reduceIte]
    exact .inr (.inr (.inl ⟨hb, rfl⟩))

/-- The other output keeps its relation after a write of output `j`. -/
theorem ORel_onWS_other {ms : MS} {j k p : Nat} {o : NOut} (hj : j ≤ 1) (hk : k ≤ 1) (hkj : k ≠ j)
    (h : ORel ms k o) (rp : Option (Nat × Nat)) (md : Mode) :
    ORel ⟨(onWS j p ms.g ms.m).1, (onWS j p ms.g ms.m).2, rp, md⟩ k o := by
  have hoff : OFFg k ≠ OFFg j := by
    unfold OFFg; split_ifs <;> first | decide | omega
  have hao : aO k ≠ aO j := by simp [aO]; omega
  refine ORel_congr h (onWS_m_other hao) (qOf_congr (onWS_g_other (Ne.symm (OFFg_ne_LEN j)))
    (onWS_g_other hoff) fun i _ => ?_)
  exact onWS_m_other (by have := aO_lt j hj; omega)

/-- A state byte written: the relation of the other output is kept. -/
theorem ORel_upd_other {ms : MS} {j k v : Nat} {o : NOut} (hj : j ≤ 1) (hkj : k ≠ j)
    (h : ORel ms k o) (rp : Option (Nat × Nat)) (md : Mode) :
    ORel ⟨ms.g, upd ms.m (aO j) v, rp, md⟩ k o := by
  have hao : aO k ≠ aO j := by simp [aO]; omega
  exact ORel_congr h (by simp [upd_apply, hao]) (qOf_congr rfl rfl fun i _ => mem_upd_lo (aO_lt j hj) i)

/-- The input's state byte written: every output keeps its relation. -/
theorem ORel_upd_RS {ms : MS} {k v : Nat} {o : NOut} (h : ORel ms k o)
    (rp : Option (Nat × Nat)) (md : Mode) : ORel ⟨ms.g, upd ms.m aRS v, rp, md⟩ k o := by
  exact ORel_congr h (by simp [upd_apply, aO_ne_RS]) (qOf_congr rfl rfl fun i _ => mem_upd_lo aRS_lt i)

/-! ## The relation after one output changed -/

/-- The handles and bounds hold for globals that differ only in output `j`'s offset, kept within
the batch. -/
theorem okT_out {ms : MS} {r w₀ w₁ s j : Nat} (hj : j ≤ 1) (hok : okT ms r w₀ w₁ s) {g m : Nat → Nat}
    {rp : Option (Nat × Nat)} {md : Mode} (hg : ∀ k, k ≠ OFFg j → g k = ms.g k)
    (hle : g (OFFg j) ≤ g LENg) : okT ⟨g, m, rp, md⟩ r w₀ w₁ s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hok
  have hO : ∀ k, k = INSR ∨ k = OUTSW ∨ k = W1g ∨ k = WS → g k = ms.g k := fun k hk =>
    hg k (by unfold OFFg; split_ifs <;> rcases hk with rfl | rfl | rfl | rfl <;> decide)
  have eL : g LENg = ms.g LENg := hg _ (OFFg_ne_LEN j).symm
  have h01 : ∀ k, k ≤ 1 → k ≠ j → g (OFFg k) = ms.g (OFFg k) := fun k hk hkj =>
    hg _ (by unfold OFFg; split_ifs <;> first | decide | omega)
  refine ⟨(hO _ (.inl rfl)).trans h1, (hO _ (.inr (.inl rfl))).trans h2,
    (hO _ (.inr (.inr (.inl rfl)))).trans h3, (hO _ (.inr (.inr (.inr rfl)))).trans h4,
    by show g LENg ≤ 256; rw [eL]; exact h5, ?_, ?_⟩
  · show g (OFFg 0) ≤ g LENg
    by_cases h0 : j = 0
    · exact h0 ▸ hle
    · rw [h01 0 (by omega) (Ne.symm h0), eL]; exact h6
  · show g (OFFg 1) ≤ g LENg
    by_cases h1' : j = 1
    · exact h1' ▸ hle
    · rw [h01 1 (by omega) (Ne.symm h1'), eL]; exact h7

/-- **The relation after output `j` changed**: the globals and memory differ only in output
`j`'s offset and state byte, and output `j`'s new state is related. -/
theorem relT_set {r w₀ w₁ s j : Nat} (hj : j ≤ 1) {ms : MS} {x : NSt Unit} {g m : Nat → Nat}
    {rp : Option (Nat × Nat)} {o' : NOut} (hlen : x.outs.length = 2)
    (hok : okT ⟨g, m, rp, .ready⟩ r w₀ w₁ s) (hI : IRel r ms x) (hrp : rp = ms.rp)
    (hOs : ∀ k, k ≤ 1 → ∃ o, x.outs[k]? = some o ∧ ORel ms k o)
    (hg : ∀ k, k ≠ OFFg j → g k = ms.g k) (hm : ∀ k, k ≠ aO j → m k = ms.m k)
    (ho' : ORel ⟨g, m, rp, .ready⟩ j o') :
    RelT r w₀ w₁ s ⟨g, m, rp, .ready⟩ { x with outs := x.outs.set j o' } := by
  have hjl : j < x.outs.length := by omega
  have hIn : ∀ i, m (IN + i) = ms.m (IN + i) := fun i => hm _ (by have := aO_lt j hj; omega)
  refine relT_live (by simp [hlen]) (.inl rfl) hok
    (IRel_congr hI (hm _ (aO_ne_RS j).symm) hrp (hg _ (OFFg_ne_LEN j).symm) rfl) fun k hk => ?_
  by_cases hkj : k = j
  · rw [hkj]; exact ⟨o', outs_set_self hjl, ho'⟩
  · obtain ⟨o, ho, hr⟩ := hOs k hk
    have hao : aO k ≠ aO j := by simp [aO]; omega
    have hoff : OFFg k ≠ OFFg j := by unfold OFFg; split_ifs <;> first | decide | omega
    exact ⟨o, by rw [outs_set hkj]; exact ho, ORel_congr hr (hm _ hao)
      (qOf_congr (hg _ (OFFg_ne_LEN j).symm) (hg _ hoff) fun i _ => hIn i)⟩

end Silmaril.Proofs.Wasm.JcoTool.KTee
