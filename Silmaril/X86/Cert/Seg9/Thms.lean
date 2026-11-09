module

public import Silmaril.X86.Cert.Calls9.Thms
public import Silmaril.X86.SegVC9.Thms
import Silmaril.Proofs.X86.Cert.Seg9

/-!
# The writing block kind `seg9`

A **block kind whose block VC is a segment VC** `wpN` (`Silmaril.X86.SegVC`), so that a block
of a generic certificate (`Cert I K`) can be proved with `seg_vc9_var` and variable segment
offsets. Unlike the listing kinds (`ext9`, `store9`), a `seg` block may
write memory anywhere, branch inside the block and leave at several exits; the only
obligations are those `wpN` states (each step executes, and the code stays loaded).

* `SegBlk I`: a block: its entry offset `off`, a listing `L` (offset ↦ instruction, length),
  its exit offsets `exits` and a path budget `K`.
* `Cert.Kinds.seg I h0 code : BlockKind I`, for any `SegVC` instance whose decoder rejects
  `[]` (`h0`) and for the function's code `code`:
  * `check code' o b`: `code' = code`, `o = b.off` and `b.L.valid I code` (decidable);
  * `WP b _ s Q`: for the `base` with `rip = base + off`, and the code loaded there,
    `wpN I code b.L [] (b.exits.map (·, Q)) [] [] base none b.K b.off s`: every path of at
    most `K` listed instructions from the entry reaches an exit, where `Q` holds. No cut
    points, calls or summaries (the shape of `seg_vc9_var`'s equation lemmas);
  * `Admits := BlockKind.Local` (every run predicate containing the code region), as for the
    listing kinds;
  * `sound`: from `Proofs/.../Cert/Seg9.lean` (`seg_runsIn`, a `RunsIn` form of
    `SegVC.path`).
* `Cert.Kinds.seg9 code := seg Open9.isa open9_decode_nil code`, on the `Ext9` open machine.
* `seg_wp`, `seg_check`: the unfoldings of the kind (propositional, for `rw`).
* Block VCs in the variable-offset form: `seg_wp_of` (state the block VC once for the entry
  offset as a variable `o0` with an equation), `nextAt_exits_mem`/`nextAt_exits_not_mem`
  (arriving at an offset: an exit gives `Q`, any other offset continues).
* `Cert.Kinds.segCalls9 code := sum (seg9 code) calls9`: segment blocks mixed with `Ext9`
  code, writing Bir9 listings and call blocks; `Cert.inr` lifts a certificate of the right
  summand (`seg9_of_store9`: every `calls9` certificate, in particular every `store9`
  certificate, is a `segCalls9` certificate with the same checks and VC).
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.SegVC (Isa Listing wpN nextAt)
open Silmaril.X86.Ext (Loaded)
open FnContract (RunsIn InCode runsIn_mono)

/-- **A segment block**: entry offset, listing, exit offsets and path budget. -/
structure SegBlk {σ : Type} (I : Isa σ) where
  off : Nat
  L : Listing I
  exits : List Nat
  K : Nat

namespace Cert.Kinds

variable {σ : Type}

/-- The exits of a segment block as the stops of its segment VC, each with `Q`. -/
abbrev segStops (exits : List Nat) (Q : σ → Prop) : List (Nat × (σ → Prop)) :=
  exits.map fun e => (e, Q)

/-- **Segment blocks** over a `SegVC` instance whose decoder rejects `[]`, for the code
`code`: the block VC is the segment VC `wpN` from the block's entry to its exits. -/
def seg (I : Isa σ) (h0 : I.decode [] = none) (code : List Byte) : BlockKind I where
  B := SegBlk I
  check code' o b := decide (code' = code) && (o == b.off) && b.L.valid I code
  WP b _ s Q := ∀ base : Word, (I.core s).rip = base + BitVec.ofNat 64 b.off →
    Loaded (I.mem s) base code →
    wpN I code b.L [] (segStops b.exits Q) [] [] base none b.K b.off s
  Admits := BlockKind.Local I
  admits_top _ _ _ _ := trivial
  sound {code' base o b R s Q} hok hlv hl hrip hadm hwp := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    obtain ⟨⟨rfl, rfl⟩, hv⟩ := hok
    obtain ⟨t, hr, hq⟩ := Silmaril.Proofs.X86.Cert.Seg9.seg_runsIn h0 hv
      (hwp base hrip hl) hlv hl hrip
    exact ⟨t, runsIn_mono hadm hr, hq⟩

theorem open9_decode_nil : Open9.isa.decode [] = none := by decide

/-- **Segment blocks on the `Ext9` open machine.** -/
def seg9 (code : List Byte) : BlockKind Open9.isa := seg Open9.isa open9_decode_nil code

/-- The check of a segment block (propositional, for `rw`/`simp`). -/
theorem seg_check {I : Isa σ} {h0 : I.decode [] = none} {code code' : List Byte} {o : Nat}
    {b : SegBlk I} :
    (seg I h0 code).check code' o b = (decide (code' = code) && (o == b.off) && b.L.valid I code) :=
  rfl

/-- The WP of a segment block (propositional, for `rw`/`simp`). -/
theorem seg_wp {I : Isa σ} {h0 : I.decode [] = none} {code : List Byte} {b : SegBlk I}
    {R : σ → Prop} {s : σ} {Q : σ → Prop} :
    (seg I h0 code).WP b R s Q = ∀ base : Word, (I.core s).rip = base + BitVec.ofNat 64 b.off →
      Loaded (I.mem s) base code →
      wpN I code b.L [] (segStops b.exits Q) [] [] base none b.K b.off s :=
  rfl

/-- The WP of a `seg9` block. -/
theorem seg9_wp {code : List Byte} {b : SegBlk Open9.isa} {R : MState → Prop} {s : MState}
    {Q : MState → Prop} :
    (seg9 code).WP b R s Q = ∀ base : Word, s.core.rip = base + BitVec.ofNat 64 b.off →
      Loaded s.memory base code →
      wpN Open9.isa code b.L [] (segStops b.exits Q) [] [] base none b.K b.off s :=
  rfl

/-- **A block VC from a variable-offset segment lemma**: it suffices to prove `wpN` at an
offset `o0` known only through an equation, from a budget `K` known only through an
equation (so the elaborator never sees the literal offset in `wpN`). -/
theorem seg_wp_of {I : Isa σ} {h0 : I.decode [] = none} {code : List Byte} {b : SegBlk I}
    {R : σ → Prop} {s : σ} {Q : σ → Prop}
    (h : ∀ (base : Word) (o0 K : Nat), o0 = b.off → K = b.K →
      (I.core s).rip = base + BitVec.ofNat 64 o0 → Loaded (I.mem s) base code →
      wpN I code b.L [] (segStops b.exits Q) [] [] base none K o0 s) :
    (seg I h0 code).WP b R s Q :=
  fun base hrip hl => h base _ _ rfl rfl hrip hl

/-- A segment block's WP does not depend on the run predicate. -/
theorem seg_wp_any {I : Isa σ} {h0 : I.decode [] = none} {code : List Byte} {b : SegBlk I}
    {R R' : σ → Prop} {s : σ} {Q : σ → Prop} (h : (seg I h0 code).WP b R s Q) :
    (seg I h0 code).WP b R' s Q :=
  h

/-! ## Arriving at an offset of a segment block -/

/-- Arriving at an exit: the block's postcondition. -/
theorem nextAt_exits_mem {exits : List Nat} {Q : σ → Prop} {μ : Option Nat}
    {cont : Nat → σ → Prop} {o : Nat} {s : σ} (h : o ∈ exits) :
    nextAt [] (segStops exits Q) μ cont o s = Q s := by
  have : (segStops exits Q).lookup o = some Q := by
    induction exits with
    | nil => cases h
    | cons e es ih =>
      simp only [segStops, List.map_cons, List.lookup_cons] at ih ⊢
      by_cases he : o = e
      · simp [he]
      · have hb : (o == e) = false := by simpa using he
        rw [hb]
        exact ih (by simpa [he] using h)
  simp only [nextAt, List.lookup_nil, this]

/-- Arriving at an offset that is not an exit: the path continues there. -/
theorem nextAt_exits_not_mem {exits : List Nat} {Q : σ → Prop} {μ : Option Nat}
    {cont : Nat → σ → Prop} {o : Nat} {s : σ} (h : o ∉ exits) :
    nextAt [] (segStops exits Q) μ cont o s = cont o s := by
  have : (segStops exits Q).lookup o = none := by
    induction exits with
    | nil => rfl
    | cons e es ih =>
      simp only [segStops, List.map_cons, List.lookup_cons] at ih ⊢
      have he : o ≠ e := fun he => h (he ▸ List.mem_cons_self)
      have hb : (o == e) = false := by simpa using he
      rw [hb]
      exact ih (fun hm => h (List.mem_cons_of_mem _ hm))
  simp only [nextAt, List.lookup_nil, this]

/-! ## Writing blocks: stores, and `Ext9`'s new forms -/

/-- A store that misses the code keeps it loaded (for the `Loaded` obligation of `wpN` after a
writing instruction). -/
theorem loaded_of_storeN {before after : Silmaril.Process.Memory} {base a v : Word}
    {code : List Byte} {k : Nat} (hl : Loaded before base code)
    (hs : Silmaril.X86.Ext.storeN before a k v = some after)
    (hd : base.toNat + code.length ≤ a.toNat ∨ a.toNat + k ≤ base.toNat) :
    Loaded after base code :=
  hl.of_stored (Silmaril.X86.Ext.Stored.of_storeN hs)
    (by rw [Silmaril.X86.Ext.length_leBytes]; exact hd)

/-- A store keeps every permission (for the `Permitted` obligation of a later store). -/
theorem permitted_of_storeN {before after : Silmaril.Process.Memory} {a v : Word} {k : Nat}
    {acc : Silmaril.Process.Access} {start count : Nat}
    (hs : Silmaril.X86.Ext.storeN before a k v = some after)
    (hp : before.Permitted acc start count) : after.Permitted acc start count :=
  (Silmaril.X86.Ext.Stored.of_storeN hs).permitted hp

/-- An `Ext9` new form executes as `execNew` at the next instruction's address (for
`seg_vc9_var`, whose set covers the `Ext8` forms and `imulI` only). -/
theorem exec9_new (i : Ext9.New) (s : State) (m : Silmaril.Process.Memory) (l : Nat) :
    Ext9.exec (.new i) s m l = Ext9.execNew i s m (s.rip + BitVec.ofNat 64 l) :=
  rfl

/-! ## Segment blocks next to the existing `Open9` kinds -/

/-- **Segment blocks, `Ext9` code, writing Bir9 listings and call blocks**, on the `Ext9` open
machine. -/
def segCalls9 (code : List Byte) : BlockKind Open9.isa :=
  BlockKind.sum (seg9 code) calls9

end Cert.Kinds

namespace Cert

variable {σ : Type} {I : Isa σ} {K₁ K₂ : BlockKind I}

/-- A certificate of `K₂` blocks as a certificate of `sum K₁ K₂` blocks. -/
def inr (K₁ : BlockKind I) (F : Cert I K₂) : Cert I (BlockKind.sum K₁ K₂) :=
  ⟨F.code, F.base, F.blocks.map fun b => ⟨b.off, .inr b.blk⟩, F.ann, F.measure⟩

theorem mem_inr {F : Cert I K₂} {b : CBlock K₂} (hb : b ∈ F.blocks) :
    (⟨b.off, .inr b.blk⟩ : CBlock (BlockKind.sum K₁ K₂)) ∈ (F.inr K₁).blocks :=
  List.mem_map.mpr ⟨b, hb, rfl⟩

theorem checked_inr {F : Cert I K₂} (hc : F.checked = true) : (F.inr K₁).checked = true := by
  simp only [checked, inr, List.all_map]
  exact hc

theorem next_inr {F : Cert I K₂} {Q : σ → σ → Prop} {s0 : σ} {μ : Nat} :
    (F.inr K₁).Next Q s0 μ = F.Next Q s0 μ := by
  funext m'
  apply propext
  constructor
  · rintro (hq | ⟨b, hb, hrip, hl, ha, hlt⟩)
    · exact .inl hq
    · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
      exact .inr ⟨b0, hb0, hrip, hl, ha, hlt⟩
  · rintro (hq | ⟨b, hb, hrip, hl, ha, hlt⟩)
    · exact .inl hq
    · exact .inr ⟨_, mem_inr hb, hrip, hl, ha, hlt⟩

theorem vcIn_inr {F : Cert I K₂} {R Q : σ → σ → Prop} (hvc : F.VCIn R Q) :
    (F.inr K₁).VCIn R Q := by
  intro b hb s0 m ha hlv hrip hl
  obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
  show K₂.WP b0.blk (R s0) m ((F.inr K₁).Next Q s0 (F.measure b0.off s0 m))
  rw [next_inr]
  exact hvc b0 hb0 s0 m ha hlv hrip hl

theorem vc_inr {F : Cert I K₂} {Q : σ → σ → Prop} (hvc : F.VC Q) : (F.inr K₁).VC Q :=
  vcIn_inr hvc

/-- **`seg9_of_store9`**: every `calls9` certificate (in particular one of `Ext9` code or of
writing Bir9 listings, `store9`) is a `segCalls9` certificate, with the same checks and VC; so
existing `Open9` certificates and segment blocks can be mixed in one function. -/
theorem seg9_of_store9 {code : List Byte} {F : Cert Open9.isa Cert.Kinds.calls9}
    {Q : MState → MState → Prop} (hc : F.checked = true) (hvc : F.VC Q) :
    (F.inr (Cert.Kinds.seg9 code)).checked = true ∧ (F.inr (Cert.Kinds.seg9 code)).VC Q :=
  ⟨checked_inr hc, vc_inr hvc⟩

end Cert

end Silmaril.X86
