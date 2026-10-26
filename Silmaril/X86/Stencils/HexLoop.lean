module

public import Silmaril.Apps.Sha256sum.Basic
public import Silmaril.Process.CLI.Sha256

/-! # Stencil: a hex output loop

A loop that, for `i < n`, maps byte `d[i]` to its two lower-case hex digits (a 16-entry table
lookup or an arithmetic nibble-to-ASCII) and appends them, one character at a time, through an
*emit* primitive (a direct store into a buffer, a buffered `putc`, …). The stencil keeps the
invariant `emitted = e0 ++ hexLower (d.take i)` and leaves both the emit primitive and the
per-iteration machine proof as parameters.

The proofs are stated with **continuation triples** `Triple K P Q` (`∀ s, P s → (∀ t, Q t → K t)
→ K s`) over an arbitrary state type `σ` and goal `K`. That covers the two shapes in use:

* `Leads` segments of a reactive model (`K := Leads … Post`, e.g. the GNU `sha256sum-min` hex
  loop, `Apps.Sha256sum.Stdout.HexLoop`, whose emit primitive is an inlined buffered
  `out_putc`, `Stdout.PutcSite`);
* run/reachability proofs (`K := fun s => ∃ t, R s t ∧ G t` for a reflexive-transitive `R`,
  `Triple.ofRuns`), the shape of `Process.CLI.Sha256Cli.HexLoop` (direct buffer stores).

Contents:

* `hexPair`, `hexLower_take_succ`: the specification `Apps.Sha256sum.hexLower`, one byte at a
  time.
* `byte`: two emits of `tbl (b / 16)` and `tbl (b % 16)`, for a table `tbl` that agrees with
  `hexDigit` below 16 (`hexTable_getD` for the ASCII table `"0123456789abcdef"`, or
  `tbl := hexDigit` for arithmetic digits), are one emit of `hexPair b`.
* `loop`: `n` iterations of an emit of `hexPair d[i]` emit `hexLower (d.take n)`.
* `hexByte_eq`, `flatMap_hexByte`: the `sha256` filter's spec (`Process.CLI.Sha256.hexByte`, on
  `BitVec 8`) is the same function, so `Sha256Cli.HexReference` and this stencil share the
  specification.

Status: **VERIFIED** (no `sorry`, standard axioms only).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.X86.Stencils.HexLoop

open Silmaril.Apps.Sha256sum (Bytes hexDigit hexLower)

/-! ## Continuation triples -/

/-- `Triple K P Q`: from every state satisfying `P`, the goal `K` holds provided it holds at
every state satisfying `Q`. -/
def Triple {σ : Type _} (K : σ → Prop) (P Q : σ → Prop) : Prop :=
  ∀ s, P s → (∀ t, Q t → K t) → K s

variable {σ : Type _} {K : σ → Prop}

theorem Triple.refl (P : σ → Prop) : Triple K P P := fun _ hp k => k _ hp

theorem Triple.seq {P Q R : σ → Prop} (h₁ : Triple K P Q) (h₂ : Triple K Q R) :
    Triple K P R :=
  fun s hp k => h₁ s hp fun t hq => h₂ t hq k

theorem Triple.mono {P P' Q Q' : σ → Prop} (h : Triple K P Q) (hp : ∀ s, P' s → P s)
    (hq : ∀ s, Q s → Q' s) : Triple K P' Q' :=
  fun s h' k => h s (hp s h') fun t ht => k t (hq t ht)

/-- A run-style segment ("from `P`, `R` reaches `Q`") is a triple for every goal of the form
"`R` reaches `G`", when `R` is transitive. -/
theorem Triple.ofRuns {R : σ → σ → Prop} (trans : ∀ a b c, R a b → R b c → R a c)
    {G : σ → Prop} {P Q : σ → Prop} (h : ∀ s, P s → ∃ t, R s t ∧ Q t) :
    Triple (fun s => ∃ u, R s u ∧ G u) P Q := by
  intro s hp k
  obtain ⟨t, hst, hq⟩ := h s hp
  obtain ⟨u, htu, hg⟩ := k t hq
  exact ⟨u, trans _ _ _ hst htu, hg⟩

/-! ## The specification, a byte at a time -/

/-- The two lower-case digits of a byte. -/
def hexPair (b : UInt8) : Bytes := [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

theorem hexLower_nil : hexLower [] = [] := rfl

theorem hexLower_append (a b : Bytes) : hexLower (a ++ b) = hexLower a ++ hexLower b :=
  List.flatMap_append

theorem hexLower_cons (b : UInt8) (d : Bytes) : hexLower (b :: d) = hexPair b ++ hexLower d :=
  rfl

theorem hexLower_take_succ (d : Bytes) (i : Nat) (hi : i < d.length) :
    hexLower (d.take (i + 1)) = hexLower (d.take i) ++ hexPair d[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, hexLower_append]
  rfl

theorem hexLower_take_length (d : Bytes) : hexLower (d.take d.length) = hexLower d := by
  rw [List.take_length]

/-- The ASCII digit table `"0123456789abcdef"`. -/
def hexTable : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66]

theorem hexTable_length : hexTable.length = 16 := rfl

theorem hexTable_getD : ∀ k < 16, hexTable.getD k 0 = hexDigit k := by decide

theorem hexTable_getElem : ∀ (k : Nat) (h : k < 16), hexTable[k]'h = hexDigit k := by decide

/-- The machine form of the table (`BitVec 8`). -/
def hexTableBits : List (BitVec 8) := hexTable.map UInt8.toBitVec

/-- The high nibble of a byte, as the machine computes it (`shr $4`; `and $0xf`). -/
theorem nibble_hi (b : BitVec 8) : ((b >>> 4) &&& 0xf#8).toNat = b.toNat / 16 := by
  have := b.isLt
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight]
  simp only [Nat.shiftRight_eq_div_pow]
  have h : b.toNat / 2 ^ 4 < 16 := by omega
  rw [show (0xf#8).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt h]
  norm_num

/-- The low nibble of a byte (`and $0xf`). -/
theorem nibble_lo (b : BitVec 8) : (b &&& 0xf#8).toNat = b.toNat % 16 := by
  rw [BitVec.toNat_and, show (0xf#8).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-! ## The stencil -/

/-- **One byte**: an emit of `tbl (b / 16)` followed by an emit of `tbl (b % 16)` is an emit of
`hexPair b`, for any table that agrees with `hexDigit` below 16. -/
theorem byte (tbl : Nat → UInt8) (htbl : ∀ k < 16, tbl k = hexDigit k) (b : UInt8)
    {A B C : Bytes → σ → Prop}
    (hi : ∀ e, Triple K (A e) (B (e ++ [tbl (b.toNat / 16)])))
    (lo : ∀ e, Triple K (B e) (C (e ++ [tbl (b.toNat % 16)]))) (e : Bytes) :
    Triple K (A e) (C (e ++ hexPair b)) := by
  have hb := b.toNat_lt
  have h1 := htbl (b.toNat / 16) (by omega)
  have h2 := htbl (b.toNat % 16) (by omega)
  have := (hi e).seq (lo _)
  rw [h1, h2, List.append_assoc] at this
  exact this

/-- **The loop**: if iteration `i` takes the invariant at `(i, e)` to the invariant at
`(i + 1, e ++ hexPair d[i])`, then `n` iterations take `(0, e0)` to
`(n, e0 ++ hexLower (d.take n))`. -/
theorem loop (d : Bytes) (Inv : Nat → Bytes → σ → Prop) (e0 : Bytes) :
    ∀ (n : Nat) (hn : n ≤ d.length),
    (∀ (i : Nat) (hi : i < n) (e : Bytes),
      Triple K (Inv i e) (Inv (i + 1) (e ++ hexPair (d[i]'(by omega))))) →
    Triple K (Inv 0 e0) (Inv n (e0 ++ hexLower (d.take n)))
  | 0, _, _ => by
    rw [List.take_zero, hexLower_nil, List.append_nil]; exact Triple.refl (K := K) (Inv 0 e0)
  | n + 1, hn, body => by
    have ih := loop d Inv e0 n (by omega) fun i hi e => body i (by omega) e
    have step := body n (by omega) (e0 ++ hexLower (d.take n))
    rw [List.append_assoc, ← hexLower_take_succ d n (by omega)] at step
    exact ih.seq step

/-- The whole loop over all of `d`. -/
theorem loop_all (d : Bytes) (Inv : Nat → Bytes → σ → Prop) (e0 : Bytes)
    (body : ∀ (i : Nat) (hi : i < d.length) (e : Bytes),
      Triple K (Inv i e) (Inv (i + 1) (e ++ hexPair d[i]))) :
    Triple K (Inv 0 e0) (Inv d.length (e0 ++ hexLower d)) := by
  have := loop d Inv e0 d.length le_rfl body
  rwa [hexLower_take_length] at this

/-! ## The `sha256` filter's specification is the same function -/

theorem hexDigit_toBitVec (n : Nat) :
    (hexDigit n).toBitVec = Silmaril.Process.CLI.Sha256.hexDigit n := by
  unfold hexDigit Silmaril.Process.CLI.Sha256.hexDigit
  by_cases h : n < 10
  · simp only [h, ite_true]; rfl
  · simp only [h, ite_false]
    show BitVec.ofNat 8 (87 + n) = BitVec.ofNat 8 (0x61 + (n - 10))
    congr 1; omega

theorem hexByte_eq (b : UInt8) :
    Silmaril.Process.CLI.Sha256.hexByte b = (hexPair b).map UInt8.toBitVec := by
  simp [Silmaril.Process.CLI.Sha256.hexByte, hexPair, hexDigit_toBitVec]

theorem flatMap_hexByte (d : Bytes) :
    d.flatMap Silmaril.Process.CLI.Sha256.hexByte = (hexLower d).map UInt8.toBitVec := by
  induction d with
  | nil => rfl
  | cons b d ih =>
    rw [List.flatMap_cons, ih, hexLower_cons, List.map_append, hexByte_eq]

end Silmaril.X86.Stencils.HexLoop
