module

public import Silmaril.X86.Partition.Defs
public import Silmaril.X86.Open9.Thms

/-!
# Soundness of the partition checker

Proofs for `Silmaril/X86/Partition/Thms.lean`. The chain is:

1. **Listing** (`decodeFrom_spec`): every listed instruction sits at an offset of the region,
   inside it, and (unless declared unmodelled) is what `decodeAt` reads there.
2. **Fetch** (`fetch_base`, `fetch_new`, `fetch_listed`): in a memory holding the region,
   `Ext8.fetch` at a listed address returns the listed instruction. For a byte form this
   needs that `X86.Ext` cannot decode a longer instruction there, which `decodeAt` checked
   (`Ext.fetch_undecodable_of`).
3. **Machines** (`executes_ext8`, `executes_open`, `executes_open9`): a step of
   `Ext8.stepOpt exit`, `Open.step` or `Open9.step` from a listed, modelled instruction is
   that instruction's execution (`D8.ExecAt`).
4. **Edges**: `Decompile.Decoded.edges_sound` for `X86.Ext` instructions; a byte form retires
   to the next address (`execNew_rip`).
5. **Checker inversion** (`check2_inv`), and the walk lemma (`walk_spec`): every edge of every
   owned instruction passed `Ctx.checkEdge` with the instruction's listed successor.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Partition

open Silmaril.X86.Partition

open Silmaril.X86 (Byte Word MState State fetchWindow maxInstrLength)
open Silmaril.X86.Decompile (Region Edge)
open Silmaril.Process (Memory)

/-! ## The listing -/

/-- What `decodeFrom` lists at an address: an offset into the bytes, inside them, a positive
length, and (for a modelled instruction) what `decodeAt` reads there. -/
def ListedIn (bytes : List Byte) (addr : Nat) (d : D8) : Prop :=
  ∃ off, d.addr = addr + off ∧ off + d.size ≤ bytes.length ∧ 0 < d.size ∧
    (d.item ≠ .unmodelled → decodeAt (bytes.drop off) = some (d.item, d.size)) ∧
    (d.item = .unmodelled → decodeAt (bytes.drop off) = none)

theorem decodeFrom_spec (un : List (Nat × Nat)) :
    ∀ (fuel addr : Nat) (bytes : List Byte) (ds : List D8),
      decodeFrom un fuel addr bytes = .ok ds → ∀ d ∈ ds, ListedIn bytes addr d := by
  intro fuel
  induction fuel with
  | zero =>
    intro addr bytes ds h d hd
    cases bytes with
    | nil => simp [decodeFrom] at h; subst h; cases hd
    | cons b t => simp [decodeFrom] at h
  | succ fuel ih =>
    intro addr bytes ds h d hd
    cases bytes with
    | nil => simp [decodeFrom] at h; subst h; cases hd
    | cons b t =>
      simp only [decodeFrom] at h
      split at h
      · rename_i n hn
        split at h
        · cases h
        · rename_i hlen
          split at h
          · cases h
          · rename_i hdec
            cases hrest : decodeFrom un fuel (addr + n) ((b :: t).drop n) with
            | error e => rw [hrest] at h; cases h
            | ok rest =>
              rw [hrest] at h
              simp only [Except.map, Except.ok.injEq] at h
              subst h
              rcases List.mem_cons.mp hd with rfl | hmem
              · refine ⟨0, by simp, by dsimp only; omega, by dsimp only; omega,
                  fun hne => absurd rfl hne, fun _ => ?_⟩
                simpa using hdec
              · obtain ⟨off, ha, hle, hpos, hm, hu⟩ := ih _ _ _ hrest d hmem
                refine ⟨n + off, by rw [ha]; omega, ?_, hpos, ?_, ?_⟩
                · simp only [List.length_drop] at hle
                  omega
                · intro hne
                  rw [← List.drop_drop]
                  exact hm hne
                · intro hu'
                  rw [← List.drop_drop]
                  exact hu hu'
      · split at h
        · cases h
        · rename_i i n hdec
          split at h
          · cases h
          · rename_i hn0
            cases hrest : decodeFrom un fuel (addr + n) ((b :: t).drop n) with
            | error e => rw [hrest] at h; cases h
            | ok rest =>
              rw [hrest] at h
              simp only [Except.map, Except.ok.injEq] at h
              subst h
              have hle : n ≤ (b :: t).length := by
                unfold decodeAt at hdec
                split at hdec
                · rename_i i' n' he
                  simp only [Option.some.injEq, Prod.mk.injEq] at hdec
                  obtain ⟨-, rfl⟩ := hdec
                  exact (Silmaril.X86.Ext.decode_length he).2.2.2
                · split at hdec
                  · rename_i i' n' he
                    split at hdec
                    · simp only [Option.some.injEq, Prod.mk.injEq] at hdec
                      obtain ⟨-, rfl⟩ := hdec
                      exact Silmaril.X86.Ext8.decodeNew_le he
                    · cases hdec
                  · cases hdec
              rcases List.mem_cons.mp hd with rfl | hmem
              · have hnu : i ≠ .unmodelled := by
                  intro e
                  subst e
                  unfold decodeAt at hdec
                  split at hdec
                  · cases hdec
                  · split at hdec
                    · split at hdec <;> cases hdec
                    · cases hdec
                refine ⟨0, by simp, by simpa using hle, by dsimp only; omega, fun _ => by simpa using hdec,
                  fun e => absurd e hnu⟩
              · obtain ⟨off, ha, hle', hpos, hm, hu⟩ := ih _ _ _ hrest d hmem
                refine ⟨n + off, by rw [ha]; omega, ?_, hpos, ?_, ?_⟩
                · simp only [List.length_drop] at hle'
                  omega
                · intro hne
                  rw [← List.drop_drop]
                  exact hm hne
                · intro hu'
                  rw [← List.drop_drop]
                  exact hu hu'

/-! ## `decodeAt` -/

theorem decodeAt_base {bytes : List Byte} {i : Silmaril.X86.Ext.Instr} {n : Nat}
    (h : decodeAt bytes = some (.base i, n)) : Silmaril.X86.Ext.decode bytes = some (i, n) := by
  unfold decodeAt at h
  split at h
  · rename_i i' n' he
    simp only [Option.some.injEq, Prod.mk.injEq, Item.base.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact he
  · split at h
    · split at h <;> cases h
    · cases h

theorem decodeAt_new {bytes : List Byte} {i : Silmaril.X86.Ext8.New} {n : Nat}
    (h : decodeAt bytes = some (.new i, n)) :
    Silmaril.X86.Ext.decode bytes = none ∧
      Silmaril.X86.Ext8.decodeNew (bytes.take n) = some (i, n) ∧
      isEof (Silmaril.X86.Ext.parseRaw (bytes.take n)) = false ∧ 2 ≤ n ∧ n ≤ maxInstrLength := by
  unfold decodeAt at h
  split at h
  · cases h
  · rename_i hnone
    split at h
    · rename_i i' n' he
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq, Item.new.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hnone, hc.2.2.1, hc.2.2.2, hc.1, hc.2.1⟩
      · cases h
    · cases h

/-! ## Fetch -/

/-- The bytes of a listed instruction, as the memory holds them. -/
theorem fetchBytes_listed {r : Region} {memory : Memory} (hload : r.LoadedIn memory)
    {d : D8} {off : Nat} (ha : d.addr = r.base + off) (hle : off + d.size ≤ r.bytes.length) :
    memory.fetchBytes d.addr d.size = some ((r.bytes.drop off).take d.size) := by
  rw [ha]
  exact hload off d.size hle

theorem fetch_base {memory : Memory} {address n : Nat} {bytes : List Byte}
    {i : Silmaril.X86.Ext.Instr}
    (hf : memory.fetchBytes address n = some (bytes.take n))
    (hd : decodeAt bytes = some (.base i, n)) :
    Silmaril.X86.Ext.fetch memory address = .decoded i n :=
  Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr
    ⟨_, hf, Silmaril.X86.Ext.decode_take (decodeAt_base hd)⟩

theorem fetch_new {memory : Memory} {address n : Nat} {bytes : List Byte}
    {i : Silmaril.X86.Ext8.New}
    (hf : memory.fetchBytes address n = some (bytes.take n))
    (hd : decodeAt bytes = some (.new i, n)) :
    Silmaril.X86.Ext8.fetch memory address = .inr (i, n) := by
  obtain ⟨hnone, hnew, heof, -, h15⟩ := decodeAt_new hd
  have hnone' : Silmaril.X86.Ext.decode (bytes.take n) = none := by
    cases hdt : Silmaril.X86.Ext.decode (bytes.take n) with
    | none => rfl
    | some x =>
      have := Silmaril.X86.Ext.decode_append (bytes.drop n) hdt
      rw [List.take_append_drop, hnone] at this
      cases this
  have hne : Silmaril.X86.Ext.parseRaw (bytes.take n) ≠ .eof := by
    intro e
    rw [e] at heof
    cases heof
  obtain ⟨more, hmore⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow hf
    (limit := maxInstrLength) h15
  have hund : Silmaril.X86.Ext.fetch memory address = .undecodable :=
    Silmaril.X86.Ext.fetch_undecodable_of hmore.symm hnone' hne
  unfold Silmaril.X86.Ext8.fetch
  rw [hund]
  simp only
  rw [← hmore, Silmaril.X86.Ext8.decodeNew_append hnew more]
  simp only [Silmaril.Process.Memory.readWith_permitted hf, ite_true]

/-! ## Step -/

theorem stepOpt_base {exit : Word} {m next : MState} {i : Silmaril.X86.Ext.Instr} {n : Nat}
    (hf : Silmaril.X86.Ext.fetch m.memory m.core.rip.toNat = .decoded i n)
    (hs : Silmaril.X86.Ext8.stepOpt exit m = some next) :
    Silmaril.X86.Ext.exec i m.core m.memory = .ok next.core next.memory := by
  have hstep : Silmaril.X86.Ext8.step exit m = .ext (Silmaril.X86.Ext.step exit m) := by
    unfold Silmaril.X86.Ext8.step Silmaril.X86.Ext8.fetch
    rw [hf]
  unfold Silmaril.X86.Ext8.stepOpt at hs
  rw [hstep] at hs
  split at hs
  · rename_i nx he
    simp only [Silmaril.X86.Ext8.Outcome.ext.injEq] at he
    simp only [Option.some.injEq] at hs
    subst hs
    unfold Silmaril.X86.Ext.step at he
    rw [hf] at he
    simp only at he
    split at he
    · rename_i c mem hx
      split at he
      · cases he
      · cases he
        exact hx
    all_goals cases he
  · rename_i nx he
    cases he
  · cases hs

theorem stepOpt_new {exit : Word} {m next : MState} {i : Silmaril.X86.Ext8.New} {n : Nat}
    (hf : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inr (i, n))
    (hs : Silmaril.X86.Ext8.stepOpt exit m = some next) :
    Silmaril.X86.Ext8.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n) =
      .ok next.core next.memory := by
  unfold Silmaril.X86.Ext8.stepOpt Silmaril.X86.Ext8.step at hs
  rw [hf] at hs
  simp only at hs
  split at hs
  · rename_i nx he
    split at he <;> cases he
  · rename_i nx he
    split at he
    · rename_i c mem hx
      cases he
      simp only [Option.some.injEq] at hs
      subst hs
      exact hx
    · cases he
  · cases hs

/-! ## Edges of the byte forms -/

theorem retire_rip {next : Word} {o : Option (State × Memory)} {c : State} {mem : Memory}
    (h : Silmaril.X86.Ext.retire next o = .ok c mem) : c.rip = next := by
  unfold Silmaril.X86.Ext.retire at h
  split at h
  · cases h; rfl
  · cases h

/-- **A byte form retires to the next address.** None of the forms `X86.Ext8` adds writes
`rip`. -/
theorem execNew_rip {i : Silmaril.X86.Ext8.New} {s c : State} {mem mem' : Memory} {next : Word}
    (h : Silmaril.X86.Ext8.execNew i s mem next = .ok c mem') : c.rip = next := by
  unfold Silmaril.X86.Ext8.execNew at h
  split at h <;> (try dsimp only at h) <;>
    repeat' (first | exact retire_rip h | (cases h) | split at h)

/-! ## Machines that execute the listing -/

/-- A listed, modelled instruction, in a memory that holds the region, is what the fetch
returns at its address. -/
theorem fetch_listed {r : Region} {p : Proposal} {fuel : Nat} {memory : Memory} {d : D8}
    (hload : r.LoadedIn memory) (hd : d ∈ listing r p fuel) (hmod : d.item ≠ .unmodelled) :
    (∀ j, d.item = .base j → Silmaril.X86.Ext.fetch memory d.addr = .decoded j d.size) ∧
      (∀ j, d.item = .new j → Silmaril.X86.Ext8.fetch memory d.addr = .inr (j, d.size)) := by
  unfold listing at hd
  split at hd
  · rename_i ds hdec
    obtain ⟨off, ha, hle, -, hm, -⟩ := decodeFrom_spec _ _ _ _ _ hdec d hd
    have hf := fetchBytes_listed hload ha hle
    refine ⟨fun j hj => fetch_base hf ?_, fun j hj => fetch_new hf ?_⟩
    · rw [← hj]; exact hm hmod
    · rw [← hj]; exact hm hmod
  · cases hd

theorem ofResult_some {x : Silmaril.X86.Ext.Result} {n : MState}
    (h : Silmaril.X86.Open.ofResult x = some n) : x = .ok n.core n.memory := by
  unfold Silmaril.X86.Open.ofResult at h
  split at h
  · cases h; rfl
  · cases h

theorem executes_ext8 {r : Region} {p : Proposal} {fuel : Nat} (exit : Word) :
    Executes r p fuel (Silmaril.X86.Ext8.stepOpt exit) := by
  intro m next d hload hd hrip hmod hs
  obtain ⟨hb, hn⟩ := fetch_listed hload hd hmod
  unfold D8.ExecAt
  cases hitem : d.item with
  | unmodelled => exact absurd hitem hmod
  | base j =>
    have hf := hb j hitem
    rw [← hrip] at hf
    exact stepOpt_base hf hs
  | new j =>
    have hf := hn j hitem
    rw [← hrip] at hf
    exact stepOpt_new hf hs

/-- At a listed, modelled instruction the `Ext8` fetch does not fail. -/
theorem fetch8_listed {r : Region} {p : Proposal} {fuel : Nat} {m : MState} {d : D8}
    (hload : r.LoadedIn m.memory) (hd : d ∈ listing r p fuel) (hrip : m.core.rip.toNat = d.addr)
    (hmod : d.item ≠ .unmodelled) :
    (∀ j, d.item = .base j →
        Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inl (.decoded j d.size)) ∧
      (∀ j, d.item = .new j →
        Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inr (j, d.size)) := by
  obtain ⟨hb, hn⟩ := fetch_listed hload hd hmod
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have hf := hb j hj
    rw [← hrip] at hf
    rw [Silmaril.X86.Ext8.fetch_of_ne_undecodable (by rw [hf]; simp), hf]
  · rw [hrip]; exact hn j hj

theorem executes_open {r : Region} {p : Proposal} {fuel : Nat} :
    Executes r p fuel Silmaril.X86.Open.step := by
  intro m next d hload hd hrip hmod hs
  obtain ⟨hb, hn⟩ := fetch8_listed hload hd hrip hmod
  unfold D8.ExecAt
  cases hitem : d.item with
  | unmodelled => exact absurd hitem hmod
  | base j =>
    simp only [Silmaril.X86.Open.step, hb j hitem] at hs
    exact ofResult_some hs
  | new j =>
    simp only [Silmaril.X86.Open.step, hn j hitem] at hs
    exact ofResult_some hs

theorem executes_open9 {r : Region} {p : Proposal} {fuel : Nat} :
    Executes r p fuel Silmaril.X86.Open9.step := by
  intro m next d hload hd hrip hmod hs
  obtain ⟨hb, hn⟩ := fetch8_listed hload hd hrip hmod
  have hne : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat ≠ .inl .undecodable := by
    cases hitem : d.item with
    | unmodelled => exact absurd hitem hmod
    | base j => rw [hb j hitem]; simp
    | new j => rw [hn j hitem]; simp
  rw [Silmaril.X86.Open9.step_eq_open hne] at hs
  exact executes_open hload hd hrip hmod hs

/-! ## Inverting the checker -/

theorem check2_inv {r : Region} {p : Proposal} {fuel : Nat} (h : check2 r p fuel = none) :
    ∃ ds, decodeListing r p.unmodelled fuel = .ok ds ∧
      tiling (r.base + r.bytes.length) r.base p.layout = none ∧
      (∀ s ∈ p.layout, ∀ o, s.owner = some o → o < p.funcs.length) ∧
      (∀ d ∈ ds, slotCheck p d = none) ∧
      (∀ f ∈ p.funcs, f.exported = true → f.conv.isAbi = true) ∧
      (∀ i < p.funcs.length,
        ((p.funcs[i]?.map fun f => decide (f.entry ∈ (bodiesOf p (annotate p ds)).getD i [])).getD
          false) = true) ∧
      Ctx.walk ⟨p, bodiesOf p (annotate p ds)⟩ (annotate p ds) = none := by
  unfold check2 at h
  split at h
  · cases h
  · rename_i ds hds
    split at h
    · cases h
    · rename_i ht
      split at h
      · cases h
      · rename_i hown
        split at h
        · cases h
        · rename_i hslot
          split at h
          · cases h
          · rename_i hexp
            simp only at h
            split at h
            · cases h
            · rename_i hent
              refine ⟨ds, hds, ht, ?_, ?_, ?_, ?_, h⟩
              · intro s hs o ho
                have := List.find?_eq_none.mp hown s hs
                rw [ho] at this
                simpa using this
              · exact List.findSome?_eq_none_iff.mp hslot
              · intro f hf hx
                have := List.find?_eq_none.mp hexp f hf
                simp only [hx, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at this
                simpa using this
              · intro i hi
                have := List.find?_eq_none.mp hent i (List.mem_range.mpr hi)
                simpa using this

theorem listing_eq {r : Region} {p : Proposal} {fuel : Nat} {ds : List D8}
    (h : decodeListing r p.unmodelled fuel = .ok ds) : listing r p fuel = ds := by
  simp [listing, h]

theorem mem_annotate {p : Proposal} {ds : List D8} {d : D8} {o : Option Nat} :
    (d, o) ∈ annotate p ds ↔ d ∈ ds ∧ p.owner d = o := by
  simp only [annotate, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨d', hd', rfl, rfl⟩
    exact ⟨hd', rfl⟩
  · rintro ⟨hd, rfl⟩
    exact ⟨d, hd, rfl, rfl⟩

theorem mem_bodies {p : Proposal} {ann : List (D8 × Option Nat)} {i t : Nat}
    (h : t ∈ (bodiesOf p ann).getD i []) : ∃ e ∈ ann, e.2 = some i ∧ e.1.addr = t := by
  rw [List.getD_eq_getElem?_getD] at h
  unfold bodiesOf at h
  rw [List.getElem?_map] at h
  by_cases hi : i < p.funcs.length
  · rw [List.getElem?_range hi] at h
    simp only [Option.map_some, Option.getD_some, List.mem_filterMap] at h
    obtain ⟨e, he, hm⟩ := h
    split at hm
    · rename_i heq
      simp only [Option.some.injEq] at hm
      exact ⟨e, he, heq, hm⟩
    · cases hm
  · rw [List.getElem?_eq_none (by simp; omega)] at h
    cases h

theorem isEntry_of_entryOf {p : Proposal} {t j : Nat} (h : p.entryOf t = some j) :
    IsEntry p t := by
  unfold Proposal.entryOf at h
  obtain ⟨hj, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨_, List.getElem_mem hj, by simpa using hp⟩

theorem isEntry_of_isSome {p : Proposal} {t : Nat} (h : (p.entryOf t).isSome = true) :
    IsEntry p t := by
  cases he : p.entryOf t with
  | none => rw [he] at h; cases h
  | some j => exact isEntry_of_entryOf he

/-- The walk saw every owned instruction with its successor. -/
theorem walk_spec (c : Ctx) : ∀ (pre : List (D8 × Option Nat)) (d : D8) (i : Nat)
    (post : List (D8 × Option Nat)), c.walk (pre ++ (d, some i) :: post) = none →
    ∀ e ∈ d.edges, c.checkEdge i d post.head? e = none := by
  intro pre
  induction pre with
  | nil =>
    intro d i post h e he
    simp only [List.nil_append, Ctx.walk] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hf
        exact List.findSome?_eq_none_iff.mp hf e he
  | cons x pre ih =>
    intro d i post h
    obtain ⟨d0, o⟩ := x
    cases o with
    | none =>
      simp only [List.cons_append, Ctx.walk] at h
      exact ih d i post h
    | some i0 =>
      simp only [List.cons_append, Ctx.walk] at h
      split at h
      · cases h
      · split at h
        · cases h
        · exact ih d i post h

/-- The walk refused an unmodelled instruction owned by a `noreturn` function. -/
theorem walk_noreturn_modelled (c : Ctx) : ∀ (pre : List (D8 × Option Nat)) (d : D8) (i : Nat)
    (post : List (D8 × Option Nat)), c.walk (pre ++ (d, some i) :: post) = none →
    c.p.noret i = true → d.item ≠ .unmodelled := by
  intro pre
  induction pre with
  | nil =>
    intro d i post h hnr hu
    simp only [List.nil_append, Ctx.walk, hu, hnr, and_self, ↓reduceIte] at h
    cases h
  | cons x pre ih =>
    intro d i post h
    obtain ⟨d0, o⟩ := x
    cases o with
    | none =>
      simp only [List.cons_append, Ctx.walk] at h
      exact ih d i post h
    | some i0 =>
      simp only [List.cons_append, Ctx.walk] at h
      split at h
      · cases h
      · split at h
        · cases h
        · exact ih d i post h

/-! ## Arithmetic of the fall-through address -/

theorem next_toNat {rip : Word} {addr n : Nat} (h : rip.toNat = addr) :
    (rip + BitVec.ofNat 64 n).toNat = (BitVec.ofNat 64 (addr + n)).toNat := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h]
  omega

/-! ## The main lemmas -/

section

variable {r : Region} {p : Proposal} {fuel : Nat}

/-- The fall-through rule: a checked fall-through lands on the next listed instruction,
owned by the same function. -/
theorem inFn_of_fallthrough {ds : List D8} (hds : decodeListing r p.unmodelled fuel = .ok ds)
    {c : Ctx} {pre post : List (D8 × Option Nat)} {d : D8} {i t : Nat}
    (hsplit : annotate p ds = pre ++ (d, some i) :: post)
    (hce : c.checkEdge i d post.head? (.fallthrough t) = none)
    (hnr : c.callsNoreturn d = false) : InFn r p fuel i t := by
  simp only [Ctx.checkEdge, hnr, Bool.false_eq_true, ite_false] at hce
  cases hpost : post with
  | nil => rw [hpost] at hce; cases hce
  | cons e post' =>
    rw [hpost] at hce
    obtain ⟨d', o⟩ := e
    cases o with
    | none => cases hce
    | some j =>
      simp only [List.head?_cons] at hce
      split at hce
      · rename_i hc
        obtain ⟨rfl, rfl⟩ := hc
        have hm : (d', some j) ∈ annotate p ds := by
          rw [hsplit, hpost]
          simp
        obtain ⟨hd', ho⟩ := mem_annotate.mp hm
        exact ⟨d', by rw [listing_eq hds]; exact hd', rfl, ho⟩
      · cases hce

/-- The jump rule: a checked jump or branch target is an instruction of the function, or a
declared tail call to a function entry. -/
theorem jump_ok {ds : List D8} {d : D8} {i t : Nat}
    (hce : Ctx.checkJump ⟨p, bodiesOf p (annotate p ds)⟩ i d t = none)
    (hds : decodeListing r p.unmodelled fuel = .ok ds) :
    InFn r p fuel i t ∨ (d.addr ∈ p.tailCalls ∧ IsEntry p t) := by
  unfold Ctx.checkJump at hce
  split at hce
  · rename_i hb
    obtain ⟨e, he, ho, ha⟩ := mem_bodies hb
    obtain ⟨d', o⟩ := e
    simp only at ho ha
    subst ho
    obtain ⟨hd', hown⟩ := mem_annotate.mp he
    exact Or.inl ⟨d', by rw [listing_eq hds]; exact hd', ha, hown⟩
  · split at hce
    · rename_i htc
      split at hce
      · rename_i j hj
        exact Or.inr ⟨htc, isEntry_of_entryOf hj⟩
      · cases hce
    · cases hce

theorem callsNoreturn_of_not_call {c : Ctx} {d : D8} (h : d.item.isCall = false) :
    c.callsNoreturn d = false := by
  unfold Ctx.callsNoreturn
  split
  · rename_i rel he
    rw [he] at h
    cases h
  · rfl

/-- **One step.** If the listed instruction `d` of function `i` took `m` to `next`
(`D8.ExecAt`), then `next` is at an instruction of `i`, or `d` was a call and `next` is at a
function entry, or `d` was a declared tail call and `next` is at a function entry, or `d` was
a `ret`. -/
theorem check2_sound_exec (h : check2 r p fuel = none) {m next : MState}
    {d : D8} {i : Nat} (hd : d ∈ listing r p fuel)
    (hown : p.owner d = some i) (hrip : m.core.rip.toNat = d.addr)
    (hexec : d.ExecAt m next) :
    InFn r p fuel i next.core.rip.toNat ∨
      (d.item.isCall = true ∧ IsEntry p next.core.rip.toNat) ∨
      (d.addr ∈ p.tailCalls ∧ IsEntry p next.core.rip.toNat) ∨
      d.item = .base .ret := by
  obtain ⟨ds, hdec, -, -, -, -, -, hwalk⟩ := check2_inv h
  rw [listing_eq hdec] at hd
  obtain ⟨off, -, -, -, hm, -⟩ := decodeFrom_spec _ _ _ _ _ hdec d hd
  have hmem : (d, some i) ∈ annotate p ds := mem_annotate.mpr ⟨hd, hown⟩
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have hedge := walk_spec _ pre d i post
    ((congrArg (Ctx.walk ⟨p, bodiesOf p (annotate p ds)⟩) hsplit).symm.trans hwalk)
  have hmod : d.item ≠ .unmodelled := by
    intro hu; simp only [D8.ExecAt, hu] at hexec
  cases hitem : d.item with
  | unmodelled => exact absurd hitem hmod
  | new j =>
    have hx : Silmaril.X86.Ext8.execNew j m.core m.memory (m.core.rip + BitVec.ofNat 64 d.size) =
        .ok next.core next.memory := by
      simpa only [D8.ExecAt, hitem] using hexec
    have hr := execNew_rip hx
    have hnext : next.core.rip.toNat = d.next := by
      rw [hr, next_toNat hrip]; rfl
    have hce := hedge (.fallthrough d.next) (by simp [D8.edges, hitem])
    refine Or.inl ?_
    rw [hnext]
    exact inFn_of_fallthrough hdec hsplit hce
      (callsNoreturn_of_not_call (by simp [hitem, Item.isCall]))
  | base j =>
    have hdA := hm hmod
    rw [hitem] at hdA
    have hx : Silmaril.X86.Ext.exec j m.core m.memory = .ok next.core next.memory := by
      simpa only [D8.ExecAt, hitem] using hexec
    have hlen : d.size = (Silmaril.X86.Ext.encode j).length :=
      (Silmaril.X86.Ext.decode_length (decodeAt_base hdA)).1
    have hedges : d.edges = (d.toDecoded j).edges := by simp [D8.edges, hitem]
    by_cases hcall : ∃ rel, j = .call rel
    · obtain ⟨rel, rfl⟩ := hcall
      rw [Silmaril.X86.Decompile.exec_call] at hx
      simp only at hx
      split at hx
      · cases hx
      · rename_i t mm _
        simp only [Silmaril.X86.Ext.Result.ok.injEq] at hx
        obtain ⟨hc, -⟩ := hx
        have hadd := Silmaril.X86.Decompile.rip_add_length (d := d.toDecoded (.call rel))
          (s := m.core) hrip hlen
        simp only [D8.toDecoded] at hadd
        have hce := hedge _ (by rw [hedges]; exact Silmaril.X86.Decompile.mem_edges_call rfl)
        have hs : (p.entryOf ((d.toDecoded (.call rel)).relTarget (rel.signExtend 64))).isSome =
            true := by
          simp only [Ctx.checkEdge] at hce
          split at hce
          · assumption
          · cases hce
        have hnr : next.core.rip.toNat = (d.toDecoded (.call rel)).relTarget (rel.signExtend 64) := by
          rw [← hc]
          simp only [Silmaril.X86.Decompile.Decoded.relTarget, D8.toDecoded]
          rw [hadd]
        refine Or.inr (Or.inl ⟨by simp [Item.isCall], ?_⟩)
        rw [hnr]
        exact isEntry_of_isSome hs
    · have hnc : d.item.isCall = false := by
        rw [hitem]
        cases j <;> simp [Item.isCall] at hcall ⊢
      rcases Silmaril.X86.Decompile.Decoded.edges_sound (d := d.toDecoded j) hrip hlen hx with
        hn | hret
      · obtain ⟨e, he, ht⟩ := hn
        rw [← hedges] at he
        have hce := hedge e he
        cases e with
        | fallthrough t =>
          simp only [Silmaril.X86.Decompile.Edge.Target] at ht
          rw [ht]
          exact Or.inl (inFn_of_fallthrough hdec hsplit hce (callsNoreturn_of_not_call hnc))
        | jump t =>
          simp only [Silmaril.X86.Decompile.Edge.Target] at ht
          rw [ht]
          simp only [Ctx.checkEdge] at hce
          rcases jump_ok hce hdec with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (Or.inr (Or.inl h2))
        | branch t =>
          simp only [Silmaril.X86.Decompile.Edge.Target] at ht
          rw [ht]
          simp only [Ctx.checkEdge] at hce
          rcases jump_ok hce hdec with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (Or.inr (Or.inl h2))
        | call t =>
          rw [hedges] at he
          obtain ⟨rel, hrel⟩ := Silmaril.X86.Decompile.instr_of_mem_edges_call he
          exact absurd ⟨rel, hrel⟩ hcall
        | ret => exact absurd ht (by simp [Silmaril.X86.Decompile.Edge.Target])
        | halt => exact absurd ht (by simp [Silmaril.X86.Decompile.Edge.Target])
      · have := Silmaril.X86.Decompile.Decoded.mem_edges_ret_iff.mp hret
        exact Or.inr (Or.inr (Or.inr (congrArg Item.base this)))

/-- **Internal steps stay inside.** A retirement from a listed instruction of `i` that is
modelled, not a call, not a `ret` and not a declared tail call lands on an instruction of
`i`. -/
theorem check2_sound_internal (h : check2 r p fuel = none)
    {step : MState → Option MState} (hx : Executes r p fuel step) {m next : MState}
    {i : Nat} (hint : InternalStep r p fuel i step m next) :
    InFn r p fuel i next.core.rip.toNat := by
  obtain ⟨hload, ⟨d, hd, ha, hown, hmod, hcall, hret, htc⟩, hstep⟩ := hint
  rcases check2_sound_exec h hd hown ha.symm (hx hload hd ha.symm hmod hstep) with
    h1 | h2 | h3 | h4
  · exact h1
  · rw [hcall] at h2; cases h2.1
  · exact absurd h3.1 htc
  · exact absurd h4 hret

/-- **A run of internal steps never leaves the function.** -/
theorem check2_sound_run (h : check2 r p fuel = none)
    {step : MState → Option MState} (hx : Executes r p fuel step) {m final : MState}
    {i : Nat} (hat : InFn r p fuel i m.core.rip.toNat)
    (hrun : InternalRun r p fuel i step m final) : InFn r p fuel i final.core.rip.toNat := by
  induction hrun with
  | refl m => exact hat
  | step hs _ ih => exact ih (check2_sound_internal h hx hs)

/-- **Return sites stay inside.** The instruction after a call of `i` to a function not
declared `noreturn` is an instruction of `i`: when the callee returns there, the caller
continues inside itself. -/
theorem check2_return_site (h : check2 r p fuel = none) {d : D8} {i : Nat} {rel : BitVec 32}
    (hd : d ∈ listing r p fuel) (hown : p.owner d = some i)
    (hi : d.item = .base (.call rel))
    (hnr : ∀ j, p.entryOf ((d.toDecoded (.call rel)).relTarget (rel.signExtend 64)) = some j →
      p.noret j = false) :
    InFn r p fuel i d.next := by
  obtain ⟨ds, hdec, -, -, -, -, -, hwalk⟩ := check2_inv h
  rw [listing_eq hdec] at hd
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem (mem_annotate.mpr ⟨hd, hown⟩)
  have hedge := walk_spec _ pre d i post
    ((congrArg (Ctx.walk ⟨p, bodiesOf p (annotate p ds)⟩) hsplit).symm.trans hwalk)
  have hce := hedge (.fallthrough d.next) (by
    simp only [D8.edges, hi]
    exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
  refine inFn_of_fallthrough hdec hsplit hce ?_
  unfold Ctx.callsNoreturn
  rw [hi]
  simp only
  split
  · rename_i j hj
    exact hnr j hj
  · rfl

/-- A function declared `noreturn` has no `ret`. -/
theorem check2_noreturn_no_ret (h : check2 r p fuel = none) {d : D8} {i : Nat}
    (hd : d ∈ listing r p fuel) (hown : p.owner d = some i) (hnr : p.noret i = true) :
    d.item ≠ .base .ret := by
  intro hi
  obtain ⟨ds, hdec, -, -, -, -, -, hwalk⟩ := check2_inv h
  rw [listing_eq hdec] at hd
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem (mem_annotate.mpr ⟨hd, hown⟩)
  have hedge := walk_spec _ pre d i post
    ((congrArg (Ctx.walk ⟨p, bodiesOf p (annotate p ds)⟩) hsplit).symm.trans hwalk)
  have hce := hedge .ret (by
    simp only [D8.edges, hi]
    exact List.mem_singleton.mpr rfl)
  simp [Ctx.checkEdge, hnr] at hce

/-- A function declared `noreturn` owns no unmodelled instruction. -/
theorem check2_noreturn_modelled (h : check2 r p fuel = none) {d : D8} {i : Nat}
    (hd : d ∈ listing r p fuel) (hown : p.owner d = some i) (hnr : p.noret i = true) :
    d.item ≠ .unmodelled := by
  obtain ⟨ds, hdec, -, -, -, -, -, hwalk⟩ := check2_inv h
  rw [listing_eq hdec] at hd
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem (mem_annotate.mpr ⟨hd, hown⟩)
  exact walk_noreturn_modelled _ pre d i post
    ((congrArg (Ctx.walk ⟨p, bodiesOf p (annotate p ds)⟩) hsplit).symm.trans hwalk) hnr

/-- A declared tail call out of a `noreturn` function enters a `noreturn` function. -/
theorem check2_noreturn_tailcall (h : check2 r p fuel = none) {d : D8} {i t : Nat}
    (hd : d ∈ listing r p fuel) (hown : p.owner d = some i) (hnr : p.noret i = true)
    (he : Edge.jump t ∈ d.edges ∨ Edge.branch t ∈ d.edges) (hout : ¬ InFn r p fuel i t) :
    ∃ j, p.entryOf t = some j ∧ p.noret j = true := by
  obtain ⟨ds, hdec, -, -, -, -, -, hwalk⟩ := check2_inv h
  rw [listing_eq hdec] at hd
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem (mem_annotate.mpr ⟨hd, hown⟩)
  have hedge := walk_spec _ pre d i post
    ((congrArg (Ctx.walk ⟨p, bodiesOf p (annotate p ds)⟩) hsplit).symm.trans hwalk)
  have hce : Ctx.checkJump ⟨p, bodiesOf p (annotate p ds)⟩ i d t = none := by
    rcases he with he | he
    · have := hedge _ he; simpa [Ctx.checkEdge] using this
    · have := hedge _ he; simpa [Ctx.checkEdge] using this
  unfold Ctx.checkJump at hce
  split at hce
  · rename_i hb
    obtain ⟨e, hem, ho, ha⟩ := mem_bodies hb
    obtain ⟨d', o⟩ := e
    simp only at ho ha
    subst ho
    obtain ⟨hd', hown'⟩ := mem_annotate.mp hem
    exact absurd ⟨d', by rw [listing_eq hdec]; exact hd', ha, hown'⟩ hout
  · split at hce
    · split at hce
      · rename_i j hj
        refine ⟨j, hj, ?_⟩
        rw [hnr] at hce
        cases hn : p.noret j
        · rw [hn] at hce; cases hce
        · rfl
      · cases hce
    · cases hce

/-- Every function's entry is an instruction it owns. -/
theorem check2_entry (h : check2 r p fuel = none) {i : Nat} {f : Fn}
    (hf : p.funcs[i]? = some f) : InFn r p fuel i f.entry := by
  obtain ⟨ds, hdec, -, -, -, -, hent, -⟩ := check2_inv h
  have hi : i < p.funcs.length := by
    rcases (List.getElem?_eq_some_iff.mp hf) with ⟨hi, -⟩; exact hi
  have := hent i hi
  rw [hf] at this
  simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at this
  obtain ⟨e, he, ho, ha⟩ := mem_bodies this
  obtain ⟨d', o⟩ := e
  simp only at ho ha
  subst ho
  obtain ⟨hd', hown'⟩ := mem_annotate.mp he
  exact ⟨d', by rw [listing_eq hdec]; exact hd', ha, hown'⟩

/-- An exported function carries a platform ABI. -/
theorem check2_exported_abi (h : check2 r p fuel = none) {f : Fn} (hf : f ∈ p.funcs)
    (hx : f.exported = true) : ∃ a, f.conv = .abi a := by
  obtain ⟨-, -, -, -, -, hexp, -, -⟩ := check2_inv h
  have := hexp f hf hx
  cases hc : f.conv with
  | abi a => exact ⟨a, rfl⟩
  | inferred _ => rw [hc] at this; cases this

/-- Every listed instruction is decoded by the model, except the declared unmodelled ones,
where the model's listing decoder indeed fails. -/
theorem check2_listed (h : check2 r p fuel = none) {d : D8} (hd : d ∈ listing r p fuel) :
    ∃ off, d.addr = r.base + off ∧ off + d.size ≤ r.bytes.length ∧ 0 < d.size ∧
      (d.item ≠ .unmodelled → decodeAt (r.bytes.drop off) = some (d.item, d.size)) ∧
      (d.item = .unmodelled → decodeAt (r.bytes.drop off) = none) := by
  obtain ⟨ds, hdec, -⟩ := check2_inv h
  rw [listing_eq hdec] at hd
  exact decodeFrom_spec _ _ _ _ _ hdec d hd

/-- A listed instruction owned by `i` lies, whole, in a code slot of `i`. -/
theorem owner_slot {d : D8} {i : Nat} (hown : p.owner d = some i) :
    ∃ a b, Slot.code i a b ∈ p.layout ∧ a ≤ d.addr ∧ d.addr + d.size ≤ b := by
  unfold Proposal.owner Proposal.slotOf at hown
  cases hs : p.layout.find? (fun s => decide (s.start ≤ d.addr ∧ d.addr + d.size ≤ s.stop)) with
  | none => rw [hs] at hown; cases hown
  | some s =>
    rw [hs] at hown
    have hmem := List.mem_of_find?_eq_some hs
    have hp := List.find?_some hs
    simp only [decide_eq_true_eq] at hp
    cases s with
    | code o a b =>
      simp only [Option.bind_some, Slot.owner, Option.some.injEq] at hown
      subst hown
      exact ⟨a, b, hmem, hp.1, hp.2⟩
    | padding a b => cases hown

/-- Every listed instruction lies whole in a slot, and an instruction of a padding slot is a
NOP. -/
theorem check2_slot (h : check2 r p fuel = none) {d : D8} (hd : d ∈ listing r p fuel) :
    ∃ s, p.slotOf d = some s ∧ (∀ a b, s = .padding a b → ∃ n, d.item = .base (.nop n)) := by
  obtain ⟨ds, hdec, -, -, hslot, -⟩ := check2_inv h
  rw [listing_eq hdec] at hd
  have := hslot d hd
  unfold slotCheck at this
  split at this
  · cases this
  · rename_i a b hs
    refine ⟨_, hs, fun _ _ _ => ?_⟩
    split at this
    · rename_i n hn; exact ⟨n, hn⟩
    · cases this
  · rename_i o a b hs
    exact ⟨_, hs, fun _ _ e => by cases e⟩

/-! ## The layout -/

theorem tiling_spec (limit : Nat) : ∀ (cursor : Nat) (slots : List Slot),
    tiling limit cursor slots = none →
      (∀ s ∈ slots, cursor ≤ s.start ∧ s.start < s.stop ∧ s.stop ≤ limit) ∧
      slots.Pairwise (fun s s' => s.stop ≤ s'.start) ∧
      (∀ a, cursor ≤ a → a < limit → ∃ s ∈ slots, s.start ≤ a ∧ a < s.stop) := by
  intro cursor slots
  induction slots generalizing cursor with
  | nil =>
    intro h
    simp only [tiling] at h
    split at h
    · cases h
    · refine ⟨by simp, List.Pairwise.nil, fun a h1 h2 => by omega⟩
  | cons s rest ih =>
    intro h
    simp only [tiling] at h
    split at h
    · split at h <;> cases h
    · rename_i hst
      split at h
      · cases h
      · rename_i hok
        have hst' : s.start = cursor := by simpa using hst
        obtain ⟨h1, h2, h3⟩ := ih s.stop h
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · omega
          · have := h1 x hx; omega
        · exact List.Pairwise.cons (fun x hx => (h1 x hx).1) h2
        · intro a ha1 ha2
          by_cases hlt : a < s.stop
          · exact ⟨s, List.mem_cons_self, by omega, hlt⟩
          · obtain ⟨x, hx, hx1, hx2⟩ := h3 a (by omega) ha2
            exact ⟨x, List.mem_cons_of_mem _ hx, hx1, hx2⟩

/-- **The layout tiles the region.** Every slot is non-empty and inside the region, the
slots are in increasing address order without overlap, and every byte of the region is in
a slot. So distinct functions' range sets are disjoint, and disjoint from the padding. -/
theorem check2_layout (h : check2 r p fuel = none) :
    (∀ s ∈ p.layout, r.base ≤ s.start ∧ s.start < s.stop ∧ s.stop ≤ r.base + r.bytes.length) ∧
      p.layout.Pairwise (fun s s' => s.stop ≤ s'.start) ∧
      (∀ a, r.base ≤ a → a < r.base + r.bytes.length → ∃ s ∈ p.layout, s.start ≤ a ∧ a < s.stop) ∧
      (∀ s ∈ p.layout, ∀ o, s.owner = some o → o < p.funcs.length) := by
  obtain ⟨-, -, ht, ho, -⟩ := check2_inv h
  exact ⟨(tiling_spec _ _ _ ht).1, (tiling_spec _ _ _ ht).2.1, (tiling_spec _ _ _ ht).2.2, ho⟩

end

end Silmaril.Proofs.X86.Partition
