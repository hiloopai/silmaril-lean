module

public import Silmaril.X86.Decompile.Edges

/-!
# Partitioning a code region into functions

An agent *proposes* a `Partition` — where the functions are, where the padding
is, which call sites a relocation patches, which undefined symbols may be
called — and `check` *verifies* it. Nothing about the proposal is trusted;
`check` is total and decidable, and every rejection names the offending address
or range so that the proposal can be repaired. `check` does not sort its input:
claims out of address order are `Reject.unordered`, because a checker that
silently reorders a proposal hides the bug that produced the order.

## What acceptance means

`check_sound_step` is the deliverable. From any state whose RIP is a decoded
instruction of an accepted function `f`, in a memory holding the region, one
retirement either

* stays at a decoded instruction of `f`, or
* arrives at the entry of some function of the partition (a call), or
* executed a `ret`, or
* was at a call site the proposal declared relocated.

`check_sound_run` iterates the first case: a run of retirements none of which
is a `call` or a `ret` never leaves `f`.

## Padding

A real `.text` section is not tiled by functions. Between them an assembler
leaves alignment padding — in the pinned `clang -O0` objects, 44 bytes of it,
every run a multi-byte NOP. `Partition.padding` lists those ranges explicitly.
They must lie inside the region, must not overlap any function, and must decode
entirely to `Ext.Instr.nop`. They need no reachability check, and deliberately do not have one.
`check_padding_unreachable` *proves* that no fall-through, jump or branch of an
accepted function reaches a padding byte, because every such target is required
to stay inside the function and a function's extent is disjoint from every
padding run; `check_entry_not_padding` says the same for the entries that calls
are required to reach. A runtime check for either could never fire, and a
branch of a checker that cannot fire is worse than a theorem.

The one gap is deliberate and named: at a call site the proposal declares
relocated, the decoded displacement is a placeholder and its literal target
means nothing, so nothing is claimed about it — which is the same gap
`check_sound_step` records.

## Relocated calls, and the assumptions acceptance makes

In an unlinked object the four displacement bytes of a `call` are zero and the
real target is named by a relocation. Decoding such a `call` literally yields a
target that is simply wrong. The checker therefore never silently resolves a
call: `Partition.relocs` maps the address of a displacement field to what the
relocation says, and

* a relocated call to an internal address must still land on a function entry;
* a relocated call to an undefined symbol must be listed in
  `Partition.externals`, and is recorded in `Accepted.assumedExternal`;
* a call with no covering relocation is resolved literally and must land on a
  function entry.

`Partition.relocs` is proposal data and so is untrusted, exactly like the rest.
A proposal that declares a relocation at every call site escapes every call
check — which is why acceptance records those sites in
`Accepted.relocatedCalls` and why `check_sound_step` has a disjunct naming
them. The guarantee is conditional on the relocation table, and says so.
-/

@[expose] public section

namespace Silmaril.X86.Decompile

open Silmaril.X86 (State MState Word)
open Silmaril.Process (Memory)

/-! ## Proposals -/

/-- One proposed function: a name, an entry address, and an extent in bytes.
The extent is `[entry, entry + size)`; the entry is its first byte. -/
structure FunctionSpec where
  /-- The function's name, for reporting. -/
  name : String
  /-- The address of the function's first byte, which is also its entry. -/
  entry : Nat
  /-- The number of bytes the function occupies. -/
  size : Nat
  deriving DecidableEq, Repr

/-- What a relocated call site really targets. -/
inductive Target where
  /-- An address defined in this region. -/
  | internal (addr : Nat)
  /-- An undefined symbol, bound at link time. -/
  | external (name : String)
  deriving DecidableEq, Repr

/-- A proposed decomposition of a region. -/
structure Partition where
  /-- The proposed functions. -/
  funcs : List FunctionSpec
  /-- Byte ranges `[start, stop)` that belong to no function: inter-function
  alignment padding. -/
  padding : List (Nat × Nat)
  /-- Call sites whose displacement a relocation supplies, keyed by the address
  of the four-byte displacement field, which for every `rel32` instruction of
  the model is `addr + size - 4`. -/
  relocs : List (Nat × Target)
  /-- The undefined symbols the proposal is allowed to call. -/
  externals : List String
  deriving DecidableEq, Repr

/-- A claimed byte range of the region: a function's extent, or a run of
inter-function padding. -/
inductive Claim where
  /-- The extent of a proposed function. -/
  | func (f : FunctionSpec)
  /-- A run of padding, as the half-open range `[start, stop)`. -/
  | padding (start stop : Nat)
  deriving DecidableEq, Repr

/-- The first address a claim covers. -/
def Claim.start : Claim → Nat
  | .func f => f.entry
  | .padding start _ => start

/-- The first address past a claim. -/
def Claim.stop : Claim → Nat
  | .func f => f.entry + f.size
  | .padding _ stop => stop

/-- One claim ends no later than another begins. -/
def Claim.Precedes (c c' : Claim) : Prop := c.stop ≤ c'.start

instance (c c' : Claim) : Decidable (c.Precedes c') := inferInstanceAs (Decidable (_ ≤ _))

/-- A claim covers the half-open range `[start, stop)`. -/
def Claim.Covers (c : Claim) (addr : Nat) : Prop := c.start ≤ addr ∧ addr < c.stop

instance (c : Claim) (addr : Nat) : Decidable (c.Covers addr) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Two claims cover no byte in common. -/
def Claim.Disjoint (c c' : Claim) : Prop := ∀ addr, ¬ (c.Covers addr ∧ c'.Covers addr)

/-- Disjointness does not depend on the order of the two claims. -/
theorem Claim.disjoint_symm {c c' : Claim} (h : c.Disjoint c') : c'.Disjoint c :=
  fun addr hc => h addr ⟨hc.2, hc.1⟩

instance : Std.Symm Claim.Disjoint where symm _ _ h := Claim.disjoint_symm h

/-- A function covers the half-open range `[entry, entry + size)`. -/
def FunctionSpec.Covers (f : FunctionSpec) (addr : Nat) : Prop :=
  f.entry ≤ addr ∧ addr < f.entry + f.size

instance (f : FunctionSpec) (addr : Nat) : Decidable (f.Covers addr) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Merge two lists of claims that are each in increasing address order.
`fuel` bounds the walk; the sum of the lengths always suffices. Merging rather
than sorting keeps `check` reducible in the kernel: `List.mergeSort` is defined
by well-founded recursion and does not reduce. -/
def mergeClaims : Nat → List Claim → List Claim → List Claim
  | 0, xs, _ => xs
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | n + 1, x :: xs, y :: ys =>
    if x.start ≤ y.start then x :: mergeClaims n xs (y :: ys)
    else y :: mergeClaims n (x :: xs) ys

/-- Every claimed range of the partition, in increasing address order: the
function extents and the padding runs. Both `Partition.funcs` and
`Partition.padding` must themselves be listed in increasing address order; a
proposal that lists them otherwise is rejected rather than silently sorted. -/
def Partition.claims (p : Partition) : List Claim :=
  mergeClaims (p.funcs.length + p.padding.length) (p.funcs.map Claim.func)
    (p.padding.map fun q => Claim.padding q.1 q.2)

/-- The entry addresses of the proposed functions. -/
def Partition.entries (p : Partition) : List Nat := p.funcs.map FunctionSpec.entry

/-- `addr` lies in a declared padding run. -/
def Partition.InPadding (p : Partition) (addr : Nat) : Prop :=
  ∃ q ∈ p.padding, q.1 ≤ addr ∧ addr < q.2

instance (p : Partition) (addr : Nat) : Decidable (p.InPadding addr) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-! ## Rejection -/

/-- Why a proposal was rejected. Each case names the offending address or
range, so that the proposing agent can repair the proposal. -/
inductive Reject where
  /-- No instruction of the model starts at this address. -/
  | undecodable (addr : Nat)
  /-- Decoding ran out of fuel before it ran out of bytes. -/
  | outOfFuel
  /-- The byte range `[start, stop)` is claimed by no function and no padding
  run. -/
  | uncovered (start stop : Nat)
  /-- Two claimed ranges overlap. -/
  | overlap (first second : Claim)
  /-- Two claimed ranges are listed out of address order. `check` does not sort
  its input: a checker that silently reorders a proposal hides the bug that
  produced the order. -/
  | unordered (first second : Claim)
  /-- A claimed range is empty, or runs outside the region. -/
  | outside (claim : Claim)
  /-- A function's entry is not the address of a decoded instruction. -/
  | entryNotAligned (f : FunctionSpec)
  /-- A decoded instruction at this address is not contained in any single
  claimed range: a claim boundary falls inside it. -/
  | straddlesClaim (addr : Nat)
  /-- An instruction in a declared padding run is not a NOP. -/
  | paddingNotNop (addr : Nat)
  /-- A jump or branch in `f` leaves `f`'s extent. -/
  | escapingEdge (f : FunctionSpec) (source target : Nat)
  /-- A call does not land on the entry of any function of the partition. -/
  | callToNonEntry (source target : Nat)
  /-- A call reaches an undefined symbol that `Partition.externals` does not
  declare. -/
  | undeclaredExternal (source : Nat) (name : String)
  /-- An edge of `f` stays inside `f` but does not land on an instruction
  boundary. -/
  | misalignedTarget (f : FunctionSpec) (source target : Nat)
  /-- The last instruction of `f` falls through past `f`'s extent. -/
  | fallsOffEnd (f : FunctionSpec) (source : Nat)
  deriving DecidableEq, Repr

/-- A decoding failure, as a rejection. -/
def Reject.ofDecodeError : DecodeError → Reject
  | .undecodable addr => .undecodable addr
  | .outOfFuel => .outOfFuel

/-! ## The accepted decomposition -/

/-- The accepted decomposition: each function with its decoded body, together
with the call sites whose target the decoded bytes do not determine. -/
structure Accepted where
  /-- The region that was checked. -/
  region : Region
  /-- The proposal that was accepted. -/
  partition : Partition
  /-- Each function of the partition with the decoded instructions of its
  extent, in address order. -/
  bodies : List (FunctionSpec × List Decoded)
  /-- The call sites the proposal declared relocated, with what the proposal
  says they target. The checker makes no claim about the successor RIP at
  these addresses. -/
  relocatedCalls : List (Nat × Target)
  /-- The subset of `relocatedCalls` that reach undefined symbols. These are
  the assumptions acceptance makes about the link. -/
  assumedExternal : List (Nat × String)
  deriving DecidableEq, Repr

/-- The decoded body the checker assigned to `f`, or `[]` if `f` is not a
function of the accepted partition. -/
def Accepted.body (acc : Accepted) (f : FunctionSpec) : List Decoded :=
  (acc.bodies.find? fun entry => entry.1 == f).elim [] Prod.snd

/-- RIP is at a decoded instruction of `f`. -/
def Accepted.AtInstruction (acc : Accepted) (f : FunctionSpec) (addr : Nat) : Prop :=
  IsStart (acc.body f) addr

instance (acc : Accepted) (f : FunctionSpec) (addr : Nat) :
    Decidable (acc.AtInstruction f addr) := inferInstanceAs (Decidable (IsStart _ _))

/-- The instruction of `f` at `addr` is `ret`. -/
def Accepted.IsRet (acc : Accepted) (f : FunctionSpec) (addr : Nat) : Prop :=
  ∃ d ∈ acc.body f, d.addr = addr ∧ d.instr = .ret

/-- `addr` is a call site the proposal declared relocated. -/
def Accepted.IsRelocatedCall (acc : Accepted) (addr : Nat) : Prop :=
  ∃ t, (addr, t) ∈ acc.relocatedCalls

/-! ## The checker -/

/-- The decoded instructions whose address lies in `f`'s extent, in address
order. -/
def bodyOf (ds : List Decoded) (f : FunctionSpec) : List Decoded :=
  ds.filter fun d => decide (f.Covers d.addr)

/-- The claim that contains an instruction entirely, if there is one. -/
def claimOf (claims : List Claim) (d : Decoded) : Option Claim :=
  claims.find? fun c => decide (c.start ≤ d.addr ∧ d.addr + d.size ≤ c.stop)

/-- What a relocation says the call at `d` targets, if the proposal declares
one covering its displacement field. -/
def relocTarget (p : Partition) (d : Decoded) : Option Target :=
  (p.relocs.find? fun e => e.1 == d.addr + d.size - 4).map Prod.snd

/-- The claimed ranges must tile `[cursor, limit)`: each one non-empty and
inside the region, none starting before the previous one ends, and none leaving
a gap. `prev` is the previous claim, carried only so that an overlap can name
both ranges. -/
def checkTiling (limit : Nat) : Option Claim → Nat → List Claim → Option Reject
  | _, cursor, [] => if cursor < limit then some (.uncovered cursor limit) else none
  | prev, cursor, c :: rest =>
    if c.stop ≤ c.start ∨ limit < c.stop then some (.outside c)
    else
      match prev with
      | some q =>
        if c.start < q.start then some (.unordered q c)
        else if c.start < cursor then some (.overlap q c)
        else if cursor < c.start then some (.uncovered cursor c.start)
        else checkTiling limit (some c) c.stop rest
      | none =>
        if c.start < cursor then some (.outside c)
        else if cursor < c.start then some (.uncovered cursor c.start)
        else checkTiling limit (some c) c.stop rest

/-- Check one edge of the instruction `d` of the function `f`. -/
def checkEdge (ds : List Decoded) (p : Partition) (f : FunctionSpec) (d : Decoded) :
    Edge → Option Reject
  | .fallthrough t =>
    if ¬ f.Covers t then some (.fallsOffEnd f d.addr)
    else if ¬ IsStart ds t then some (.misalignedTarget f d.addr t)
    else none
  | .jump t =>
    if ¬ f.Covers t then some (.escapingEdge f d.addr t)
    else if ¬ IsStart ds t then some (.misalignedTarget f d.addr t)
    else none
  | .branch t =>
    if ¬ f.Covers t then some (.escapingEdge f d.addr t)
    else if ¬ IsStart ds t then some (.misalignedTarget f d.addr t)
    else none
  | .call t =>
    match relocTarget p d with
    | some (.internal a) =>
      if a ∈ p.entries then none else some (.callToNonEntry d.addr a)
    | some (.external name) =>
      if name ∈ p.externals then none else some (.undeclaredExternal d.addr name)
    | none => if t ∈ p.entries then none else some (.callToNonEntry d.addr t)
  | .ret => none
  | .halt => none

/-- Check every edge of every instruction of `f`. -/
def checkBody (ds : List Decoded) (p : Partition) (f : FunctionSpec) :
    List Decoded → Option Reject
  | [] => none
  | d :: rest =>
    match d.edges.findSome? (checkEdge ds p f d) with
    | some rej => some rej
    | none => checkBody ds p f rest

/-- The call sites the proposal declares relocated, with their declared
targets, in address order. -/
def relocatedCallSites (ds : List Decoded) (p : Partition) : List (Nat × Target) :=
  ds.filterMap fun d =>
    match d.instr, relocTarget p d with
    | .call _, some t => some (d.addr, t)
    | _, _ => none

/-- The relocated call sites that reach undefined symbols. -/
def externalCallSites (ds : List Decoded) (p : Partition) : List (Nat × String) :=
  (relocatedCallSites ds p).filterMap fun e =>
    match e.2 with
    | .external name => some (e.1, name)
    | .internal _ => none

/-- Check a proposed partition. Total, decidable, and informative on failure.
`fuel` bounds the decoding walk; `r.bytes.length` always suffices.

The checks are written as nested `match`es rather than in `do` notation so that
both the kernel and `check_ok_inv` can take them apart one at a time. -/
def check (r : Region) (p : Partition) (fuel : Nat) : Except Reject Accepted :=
  match r.decode fuel with
  | .error e => .error (Reject.ofDecodeError e)
  | .ok ds =>
    match checkTiling (r.base + r.bytes.length) none r.base p.claims with
    | some rej => .error rej
    | none =>
      match p.funcs.find? fun f => !decide (IsStart ds f.entry) with
      | some f => .error (.entryNotAligned f)
      | none =>
        match ds.find? fun d => (claimOf p.claims d).isNone with
        | some d => .error (.straddlesClaim d.addr)
        | none =>
          match ds.find? fun d => decide (p.InPadding d.addr) && !isNop d.instr with
          | some d => .error (.paddingNotNop d.addr)
          | none =>
            match p.funcs.findSome? fun f => checkBody ds p f (bodyOf ds f) with
            | some rej => .error rej
            | none =>
              .ok { region := r, partition := p,
                    bodies := p.funcs.map fun f => (f, bodyOf ds f),
                    relocatedCalls := relocatedCallSites ds p,
                    assumedExternal := externalCallSites ds p }

/-! ## Inverting the checker

Everything below reads a successful `check` back into the facts it established.
`check_ok_inv` is the single inversion; the rest are consequences. -/

/-- Merging two lists of claims keeps exactly their elements, provided the fuel
covers both. -/
theorem mem_mergeClaims : ∀ (n : Nat) (xs ys : List Claim), xs.length + ys.length ≤ n →
    ∀ c, c ∈ mergeClaims n xs ys ↔ c ∈ xs ∨ c ∈ ys := by
  intro n
  induction n with
  | zero =>
    intro xs ys hn c
    cases xs with
    | nil => cases ys with
      | nil => simp [mergeClaims]
      | cons y ys => simp at hn
    | cons x xs => simp at hn
  | succ n ih =>
    intro xs ys hn c
    cases xs with
    | nil => simp [mergeClaims]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeClaims]
      | cons y ys =>
        simp only [mergeClaims]
        split
        · rw [List.mem_cons, ih xs (y :: ys) (by simp at hn ⊢; omega) c]
          simp only [List.mem_cons]
          tauto
        · rw [List.mem_cons, ih (x :: xs) ys (by simp at hn ⊢; omega) c]
          simp only [List.mem_cons]
          tauto

/-- A function's extent is one of the partition's claims. -/
theorem mem_claims_func {p : Partition} {f : FunctionSpec} (hf : f ∈ p.funcs) :
    Claim.func f ∈ p.claims := by
  rw [Partition.claims, mem_mergeClaims _ _ _ (by simp) _]
  exact Or.inl (List.mem_map_of_mem hf)

/-- A padding run is one of the partition's claims. -/
theorem mem_claims_padding {p : Partition} {q : Nat × Nat} (hq : q ∈ p.padding) :
    Claim.padding q.1 q.2 ∈ p.claims := by
  rw [Partition.claims, mem_mergeClaims _ _ _ (by simp) _]
  exact Or.inr (List.mem_map_of_mem hq)

/-- A successful tiling walk: the claims are ordered, each is a non-empty range
inside `[cursor, limit)`, and together they cover it. -/
theorem checkTiling_spec (limit : Nat) :
    ∀ (cs : List Claim) (prev : Option Claim) (cursor : Nat),
      checkTiling limit prev cursor cs = none →
      cs.Pairwise Claim.Precedes ∧
        (∀ c ∈ cs, cursor ≤ c.start ∧ c.start < c.stop ∧ c.stop ≤ limit) ∧
        (∀ a, cursor ≤ a → a < limit → ∃ c ∈ cs, c.Covers a) := by
  intro cs
  induction cs with
  | nil =>
    intro prev cursor h
    simp only [checkTiling] at h
    split at h
    · cases h
    · exact ⟨List.Pairwise.nil, by simp, fun a h1 h2 => by omega⟩
  | cons c rest ih =>
    intro prev cursor h
    simp only [checkTiling] at h
    split at h
    · cases h
    · rename_i hgood
      have hrange : c.start < c.stop ∧ c.stop ≤ limit := ⟨by omega, by omega⟩
      have hstep : c.start = cursor ∧ checkTiling limit (some c) c.stop rest = none := by
        cases prev with
        | none =>
          simp only at h
          split at h
          · cases h
          · split at h
            · cases h
            · rename_i h1 h2
              exact ⟨by omega, h⟩
        | some q =>
          simp only at h
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · rename_i h1 h2 h3
                exact ⟨by omega, h⟩
      obtain ⟨hstart, hrec⟩ := hstep
      obtain ⟨hp, hin, hcov⟩ := ih (some c) c.stop hrec
      refine ⟨List.Pairwise.cons (fun c' hc' => (hin c' hc').1) hp, ?_, ?_⟩
      · intro c' hc'
        rcases List.mem_cons.mp hc' with rfl | hm
        · exact ⟨by omega, hrange.1, hrange.2⟩
        · obtain ⟨h1, h2, h3⟩ := hin c' hm
          exact ⟨by omega, h2, h3⟩
      · intro a h1 h2
        by_cases hlt : a < c.stop
        · exact ⟨c, List.mem_cons_self .., by omega, hlt⟩
        · obtain ⟨c', hc', hcov'⟩ := hcov a (by omega) h2
          exact ⟨c', List.mem_cons_of_mem _ hc', hcov'⟩

/-- Everything a successful `check` established. -/
theorem check_ok_inv {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (h : check r p fuel = .ok acc) :
    ∃ ds, r.decode? fuel = some ds ∧
      checkTiling (r.base + r.bytes.length) none r.base p.claims = none ∧
      (∀ f ∈ p.funcs, IsStart ds f.entry) ∧
      (∀ d ∈ ds, ∃ c ∈ p.claims, c.start ≤ d.addr ∧ d.addr + d.size ≤ c.stop) ∧
      (∀ d ∈ ds, p.InPadding d.addr → isNop d.instr = true) ∧
      (∀ f ∈ p.funcs, checkBody ds p f (bodyOf ds f) = none) ∧
      acc = { region := r, partition := p,
              bodies := p.funcs.map fun f => (f, bodyOf ds f),
              relocatedCalls := relocatedCallSites ds p,
              assumedExternal := externalCallSites ds p } := by
  unfold check at h
  split at h
  · cases h
  · rename_i ds hdec
    refine ⟨ds, Region.decode?_eq_some_iff.mpr hdec, ?_⟩
    split at h
    · cases h
    · rename_i ht
      refine ⟨ht, ?_⟩
      split at h
      · cases h
      · rename_i he
        split at h
        · cases h
        · rename_i hs
          split at h
          · cases h
          · rename_i hn
            split at h
            · cases h
            · rename_i hb
              refine ⟨?_, ?_, ?_, ?_, by cases h; rfl⟩
              · intro f hf
                by_contra hcon
                exact List.find?_eq_none.mp he f hf (by simp [hcon])
              · intro d hd
                cases hco : claimOf p.claims d with
                | none => exact absurd (by simp [hco]) (List.find?_eq_none.mp hs d hd)
                | some c =>
                  exact ⟨c, List.mem_of_find?_eq_some hco, by simpa using List.find?_some hco⟩
              · intro d hd hpad
                by_contra hcon
                have hfalse : isNop d.instr = false := by simpa using hcon
                exact List.find?_eq_none.mp hn d hd (by simp [hpad, hfalse])
              · intro f hf
                exact List.findSome?_eq_none_iff.mp hb f hf

/-! ## Reading the accepted record -/

/-- The body the checker recorded for a function of the partition. -/
theorem body_of_mem {ds : List Decoded} (fs : List FunctionSpec) {f : FunctionSpec}
    (hf : f ∈ fs) :
    ((fs.map fun g => (g, bodyOf ds g)).find? fun e => e.1 == f).elim [] Prod.snd
      = bodyOf ds f := by
  induction fs with
  | nil => cases hf
  | cons g rest ih =>
    rw [List.map_cons, List.find?_cons]
    cases hg : (g == f) with
    | true =>
      have : g = f := by simpa using hg
      subst this
      simp
    | false =>
      rcases List.mem_cons.mp hf with rfl | hm
      · simp at hg
      · simpa using ih hm

/-- An instruction belongs to a function's body exactly when it is decoded and
its address is inside the function's extent. -/
theorem mem_bodyOf {ds : List Decoded} {f : FunctionSpec} {d : Decoded} :
    d ∈ bodyOf ds f ↔ d ∈ ds ∧ f.Covers d.addr := by
  simp [bodyOf, List.mem_filter]

/-- A decoded address inside a function's extent is a body address. -/
theorem isStart_bodyOf {ds : List Decoded} {f : FunctionSpec} {t : Nat}
    (h : IsStart ds t) (hc : f.Covers t) : IsStart (bodyOf ds f) t := by
  simp only [IsStart, starts, List.mem_map] at h ⊢
  obtain ⟨d, hd, rfl⟩ := h
  exact ⟨d, mem_bodyOf.mpr ⟨hd, hc⟩, rfl⟩

/-- A successful body check applies to every edge of every instruction. -/
theorem checkBody_eq_none {ds : List Decoded} {p : Partition} {f : FunctionSpec} :
    ∀ body : List Decoded, checkBody ds p f body = none →
      ∀ d ∈ body, ∀ e ∈ d.edges, checkEdge ds p f d e = none := by
  intro body
  induction body with
  | nil => intro _ d hd; cases hd
  | cons d rest ih =>
    intro h d' hd' e he
    simp only [checkBody] at h
    split at h
    · cases h
    · rename_i hnone
      rcases List.mem_cons.mp hd' with rfl | hm
      · exact List.findSome?_eq_none_iff.mp hnone e he
      · exact ih h d' hm e he

/-- An `Edge.call` is listed only by a `call` instruction. -/
theorem instr_of_mem_edges_call {d : Decoded} {t : Nat} (h : Edge.call t ∈ d.edges) :
    ∃ rel, d.instr = .call rel := by
  obtain ⟨addr, instr, size⟩ := d
  cases instr <;> simp [Decoded.edges] at h ⊢

/-- A relocated call site is recorded. -/
theorem mem_relocatedCallSites {ds : List Decoded} {p : Partition} {d : Decoded}
    {rel : BitVec 32} {t : Target} (hd : d ∈ ds) (hi : d.instr = .call rel)
    (hr : relocTarget p d = some t) : (d.addr, t) ∈ relocatedCallSites ds p := by
  rw [relocatedCallSites, List.mem_filterMap]
  exact ⟨d, hd, by rw [hi] at *; rw [hr]⟩

/-- A checked fall-through, jump or branch target is inside the function and on
an instruction boundary. -/
theorem checkEdge_intra {ds : List Decoded} {p : Partition} {f : FunctionSpec}
    {d : Decoded} {t : Nat}
    (h : checkEdge ds p f d (.fallthrough t) = none ∨ checkEdge ds p f d (.jump t) = none ∨
      checkEdge ds p f d (.branch t) = none) : f.Covers t ∧ IsStart ds t := by
  rcases h with h | h | h <;>
    · simp only [checkEdge] at h
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i h1 h2
          exact ⟨by simpa using h1, by simpa using h2⟩

/-- A checked fall-through, jump or branch target is a body address of the
function it was checked for. -/
theorem isStart_of_checkEdge {ds : List Decoded} {p : Partition} {f : FunctionSpec}
    {d : Decoded} {t : Nat}
    (h : checkEdge ds p f d (.fallthrough t) = none ∨ checkEdge ds p f d (.jump t) = none ∨
      checkEdge ds p f d (.branch t) = none) : IsStart (bodyOf ds f) t :=
  let w := checkEdge_intra h
  isStart_bodyOf w.2 w.1

/-! ## Soundness -/

/-- One retirement from a decoded address goes to a statically listed
successor, unless the instruction was `ret`. -/
theorem step_nextRip {r : Region} {fuel : Nat} {ds : List Decoded} {d : Decoded}
    {exit : Word} {m next : MState} (hds : r.decode? fuel = some ds)
    (hload : r.LoadedIn m.memory) (hd : d ∈ ds) (hrip : m.core.rip.toNat = d.addr)
    (hstep : Ext.stepOpt exit m = some next) :
    d.NextRip next.core.rip.toNat ∨ d.instr = .ret := by
  rw [Ext.stepOpt_eq_some_iff] at hstep
  simp only [Ext.step, hrip, Region.decode?_fetch hds hload hd] at hstep
  split at hstep
  · rename_i core memory hex
    split at hstep
    · cases hstep
    · cases hstep
      exact (Decoded.edges_sound hrip (Region.decode?_size hds d hd) hex).imp id
        Decoded.mem_edges_ret_iff.mp
  all_goals cases hstep

/-- **An accepted partition is a real decomposition.** From any state whose RIP
is a decoded instruction of `f`, in a memory holding the region, one retirement
either stays at a decoded instruction of `f`, or arrives at the entry of some
function of the partition, or executed a `ret`, or was at a call site the
proposal declared relocated — about which nothing is claimed, since the decoded
displacement is a placeholder. -/
theorem check_sound_step {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (h : check r p fuel = .ok acc) {f : FunctionSpec} (hf : f ∈ p.funcs)
    {exit : Word} {m next : MState} (hload : r.LoadedIn m.memory)
    (hat : acc.AtInstruction f m.core.rip.toNat)
    (hstep : Ext.stepOpt exit m = some next) :
    acc.AtInstruction f next.core.rip.toNat ∨
      (∃ g ∈ p.funcs, next.core.rip.toNat = g.entry) ∨
      acc.IsRet f m.core.rip.toNat ∨
      acc.IsRelocatedCall m.core.rip.toNat := by
  obtain ⟨ds, hds, -, -, -, -, hbody, rfl⟩ := check_ok_inv h
  have hbodyeq : ∀ g ∈ p.funcs, Accepted.body
      { region := r, partition := p, bodies := p.funcs.map fun g => (g, bodyOf ds g),
        relocatedCalls := relocatedCallSites ds p,
        assumedExternal := externalCallSites ds p } g = bodyOf ds g := fun g hg =>
    body_of_mem p.funcs hg
  rw [Accepted.AtInstruction, hbodyeq f hf] at hat
  simp only [IsStart, starts, List.mem_map] at hat
  obtain ⟨d, hdb, hdaddr⟩ := hat
  obtain ⟨hdds, hdcov⟩ := mem_bodyOf.mp hdb
  have hedges := checkBody_eq_none (bodyOf ds f) (hbody f hf) d hdb
  rcases step_nextRip hds hload hdds hdaddr.symm hstep with hnext | hret
  · obtain ⟨e, he, ht⟩ := hnext
    have hce := hedges e he
    cases e with
    | fallthrough t =>
      simp only [Edge.Target] at ht
      subst ht
      refine Or.inl ?_
      rw [Accepted.AtInstruction, hbodyeq f hf]
      exact isStart_of_checkEdge (Or.inl hce)
    | jump t =>
      simp only [Edge.Target] at ht
      subst ht
      refine Or.inl ?_
      rw [Accepted.AtInstruction, hbodyeq f hf]
      exact isStart_of_checkEdge (Or.inr (Or.inl hce))
    | branch t =>
      simp only [Edge.Target] at ht
      subst ht
      refine Or.inl ?_
      rw [Accepted.AtInstruction, hbodyeq f hf]
      exact isStart_of_checkEdge (Or.inr (Or.inr hce))
    | call t =>
      simp only [Edge.Target] at ht
      obtain ⟨rel, hrel⟩ := instr_of_mem_edges_call he
      simp only [checkEdge] at hce
      cases hrt : relocTarget p d with
      | some tgt =>
        refine Or.inr (Or.inr (Or.inr ?_))
        rw [Accepted.IsRelocatedCall, ← hdaddr]
        exact ⟨tgt, mem_relocatedCallSites hdds hrel hrt⟩
      | none =>
        rw [hrt] at hce
        simp only at hce
        split at hce
        · rename_i hmem
          refine Or.inr (Or.inl ?_)
          simp only [Partition.entries, List.mem_map] at hmem
          obtain ⟨g, hg, hge⟩ := hmem
          exact ⟨g, hg, by rw [ht, ← hge]⟩
        · cases hce
    | ret => exact absurd ht (by simp [Edge.Target])
    | halt => exact absurd ht (by simp [Edge.Target])
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [Accepted.IsRet, hbodyeq f hf]
    exact ⟨d, hdb, hdaddr, hret⟩

/-- One retirement inside `f` that is neither a call nor a return, in a memory
that still holds the region. Carrying `LoadedIn` in the relation rather than as
a hypothesis of the run is deliberate: an instruction of the function may write
memory, and nothing here proves that it does not write to the code region. -/
def Accepted.InternalStep (acc : Accepted) (f : FunctionSpec) (r : Region) (exit : Word)
    (m next : MState) : Prop :=
  r.LoadedIn m.memory ∧
    (∃ d ∈ acc.body f, d.addr = m.core.rip.toNat ∧ interprocedural d.instr = false) ∧
    Ext.stepOpt exit m = some next

/-- A finite run of internal steps. -/
inductive Accepted.InternalRun (acc : Accepted) (f : FunctionSpec) (r : Region) (exit : Word) :
    MState → MState → Prop where
  /-- The empty run. -/
  | refl (m : MState) : InternalRun acc f r exit m m
  /-- One internal step, then a run. -/
  | step {m mid final : MState} (hstep : acc.InternalStep f r exit m mid)
      (hrest : InternalRun acc f r exit mid final) : InternalRun acc f r exit m final

/-- One internal retirement stays at a decoded instruction of `f`. -/
theorem check_sound_internal {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (h : check r p fuel = .ok acc) {f : FunctionSpec} (hf : f ∈ p.funcs)
    {exit : Word} {m next : MState} (hint : acc.InternalStep f r exit m next) :
    acc.AtInstruction f next.core.rip.toNat := by
  obtain ⟨hload, ⟨d, hdb, hdaddr, hnot⟩, hstep⟩ := hint
  obtain ⟨ds, hds, -, -, -, -, hbody, rfl⟩ := check_ok_inv h
  have hbodyeq : Accepted.body
      { region := r, partition := p, bodies := p.funcs.map fun g => (g, bodyOf ds g),
        relocatedCalls := relocatedCallSites ds p,
        assumedExternal := externalCallSites ds p } f = bodyOf ds f :=
    body_of_mem p.funcs hf
  rw [hbodyeq] at hdb
  obtain ⟨hdds, hdcov⟩ := mem_bodyOf.mp hdb
  have hedges := checkBody_eq_none (bodyOf ds f) (hbody f hf) d hdb
  rcases step_nextRip hds hload hdds hdaddr.symm hstep with hnext | hret
  · obtain ⟨e, he, ht⟩ := hnext
    have hce := hedges e he
    cases e with
    | fallthrough t =>
      simp only [Edge.Target] at ht
      subst ht
      rw [Accepted.AtInstruction, hbodyeq]
      exact isStart_of_checkEdge (Or.inl hce)
    | jump t =>
      simp only [Edge.Target] at ht
      subst ht
      rw [Accepted.AtInstruction, hbodyeq]
      exact isStart_of_checkEdge (Or.inr (Or.inl hce))
    | branch t =>
      simp only [Edge.Target] at ht
      subst ht
      rw [Accepted.AtInstruction, hbodyeq]
      exact isStart_of_checkEdge (Or.inr (Or.inr hce))
    | call t =>
      obtain ⟨rel, hrel⟩ := instr_of_mem_edges_call he
      rw [hrel] at hnot
      exact Bool.noConfusion hnot
    | ret => exact absurd ht (by simp [Edge.Target])
    | halt => exact absurd ht (by simp [Edge.Target])
  · rw [hret] at hnot
    exact Bool.noConfusion hnot

/-- **Control stays inside the function.** Every state reachable from a decoded
instruction of `f` by retirements that are neither calls nor returns has its
RIP at a decoded instruction of `f`. -/
theorem check_sound_run {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (h : check r p fuel = .ok acc) {f : FunctionSpec} (hf : f ∈ p.funcs)
    {exit : Word} {m final : MState} (hat : acc.AtInstruction f m.core.rip.toNat)
    (hrun : acc.InternalRun f r exit m final) :
    acc.AtInstruction f final.core.rip.toNat := by
  induction hrun with
  | refl m => exact hat
  | step hstep _ ih => exact ih (check_sound_internal h hf hstep)

/-! ## What else acceptance says -/

/-- Acceptance decodes the region. -/
theorem check_decodes {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (h : check r p fuel = .ok acc) : ∃ ds, r.decode? fuel = some ds := by
  obtain ⟨ds, hds, -⟩ := check_ok_inv h
  exact ⟨ds, hds⟩

/-- The claimed ranges are listed in strictly increasing address order, each
one ending no later than the next one starts. -/
theorem check_ordered {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (h : check r p fuel = .ok acc) : p.claims.Pairwise Claim.Precedes := by
  obtain ⟨-, -, ht, -⟩ := check_ok_inv h
  exact (checkTiling_spec _ _ _ _ ht).1

/-- No byte of the region is claimed twice. -/
theorem check_disjoint {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (h : check r p fuel = .ok acc) : p.claims.Pairwise Claim.Disjoint :=
  (check_ordered h).imp fun hp _addr hcov =>
    absurd (Nat.lt_of_lt_of_le hcov.1.2 (Nat.le_trans hp hcov.2.1)) (Nat.lt_irrefl _)

/-- Every claimed range is non-empty and inside the region. -/
theorem check_claim_inside {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (h : check r p fuel = .ok acc) {c : Claim} (hc : c ∈ p.claims) :
    r.base ≤ c.start ∧ c.start < c.stop ∧ c.stop ≤ r.base + r.bytes.length := by
  obtain ⟨-, -, ht, -⟩ := check_ok_inv h
  exact (checkTiling_spec _ _ _ _ ht).2.1 c hc

/-- The claimed ranges cover every byte of the region. -/
theorem check_covers {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (h : check r p fuel = .ok acc) {addr : Nat} (hlo : r.base ≤ addr)
    (hhi : addr < r.base + r.bytes.length) : ∃ c ∈ p.claims, c.Covers addr := by
  obtain ⟨-, -, ht, -⟩ := check_ok_inv h
  exact (checkTiling_spec _ _ _ _ ht).2.2 addr hlo hhi

/-- Two distinct claims of an accepted partition cover no byte in common. -/
theorem check_disjoint_of_ne {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (h : check r p fuel = .ok acc) {c c' : Claim} (hc : c ∈ p.claims) (hc' : c' ∈ p.claims)
    (hne : c ≠ c') : c.Disjoint c' :=
  (check_disjoint h).forall hc hc' hne

/-- A function claim of the partition names a function of the partition. -/
theorem func_mem_of_mem_claims {p : Partition} {f : FunctionSpec}
    (h : Claim.func f ∈ p.claims) : f ∈ p.funcs := by
  rw [Partition.claims, mem_mergeClaims _ _ _ (by simp) _] at h
  rcases h with h | h
  · obtain ⟨g, hg, hgf⟩ := List.mem_map.mp h
    cases hgf
    exact hg
  · obtain ⟨q, -, hq⟩ := List.mem_map.mp h
    cases hq

/-- A padding claim of the partition names a declared padding run. -/
theorem padding_mem_of_mem_claims {p : Partition} {a b : Nat}
    (h : Claim.padding a b ∈ p.claims) : ∃ q ∈ p.padding, q.1 = a ∧ q.2 = b := by
  rw [Partition.claims, mem_mergeClaims _ _ _ (by simp) _] at h
  rcases h with h | h
  · obtain ⟨g, -, hg⟩ := List.mem_map.mp h
    cases hg
  · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp h
    cases hqe
    exact ⟨q, hq, rfl, rfl⟩

/-- A byte inside a function's extent is not a padding byte: a function claim
and a padding claim are distinct claims, and an accepted partition's claims are
pairwise disjoint. -/
theorem not_inPadding_of_covers {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (h : check r p fuel = .ok acc) {f : FunctionSpec} (hf : f ∈ p.funcs) {addr : Nat}
    (hc : f.Covers addr) : ¬ p.InPadding addr := by
  rintro ⟨q, hq, hq1, hq2⟩
  refine check_disjoint_of_ne h (mem_claims_func hf) (mem_claims_padding hq) (by simp) addr ?_
  exact ⟨hc, hq1, hq2⟩

/-- A function's entry is never a padding byte. -/
theorem check_entry_not_padding {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (h : check r p fuel = .ok acc) {g : FunctionSpec} (hg : g ∈ p.funcs) :
    ¬ p.InPadding g.entry :=
  not_inPadding_of_covers h hg ⟨Nat.le_refl _, (check_claim_inside h (mem_claims_func hg)).2.1⟩

/-- A decoded instruction that is not a NOP lies in the extent of a function of
the partition: the claim containing it cannot be a padding run, since every
instruction of a padding run is a NOP. -/
theorem func_of_mem_ds {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    {ds : List Decoded} (h : check r p fuel = .ok acc) (hds : r.decode? fuel = some ds)
    {d : Decoded} (hd : d ∈ ds) (hnop : isNop d.instr = false) :
    ∃ f ∈ p.funcs, f.Covers d.addr := by
  obtain ⟨ds', hds', -, -, hclaim, hnopall, -, -⟩ := check_ok_inv h
  rw [hds'] at hds
  cases hds
  obtain ⟨c, hc, h1, h2⟩ := hclaim d hd
  have hpos : 0 < d.size := Region.decode?_size_pos hds' d hd
  cases c with
  | func f => exact ⟨f, func_mem_of_mem_claims hc, h1, by simp only [Claim.stop] at h2; omega⟩
  | padding a b =>
    obtain ⟨q, hq, rfl, rfl⟩ := padding_mem_of_mem_claims hc
    simp only [Claim.start] at h1
    simp only [Claim.stop] at h2
    exact absurd (hnopall d hd ⟨q, hq, h1, by omega⟩) (by simp [hnop])

/-- The instruction at a recorded relocated call site, with what the
relocation says it targets. -/
theorem relocatedCall_inv {ds : List Decoded} {p : Partition} {addr : Nat} {t : Target}
    (hc : (addr, t) ∈ relocatedCallSites ds p) :
    ∃ d ∈ ds, d.addr = addr ∧ (∃ rel, d.instr = .call rel) ∧ relocTarget p d = some t := by
  rw [relocatedCallSites, List.mem_filterMap] at hc
  obtain ⟨d, hd, hmatch⟩ := hc
  revert hmatch
  cases hi : d.instr with
  | call rel =>
    cases hrt : relocTarget p d with
    | none => simp
    | some tgt =>
      simp only [Option.some.injEq, Prod.mk.injEq]
      rintro ⟨rfl, rfl⟩
      exact ⟨d, hd, rfl, ⟨rel, hi⟩, hrt⟩
  | _ => simp

/-- Every `call` instruction lists its own target as an edge. -/
theorem mem_edges_call {d : Decoded} {rel : BitVec 32} (hi : d.instr = .call rel) :
    Edge.call (d.relTarget (rel.signExtend 64)) ∈ d.edges := by
  simp only [Decoded.edges, hi]
  exact List.Mem.head _

/-- A relocated call whose declared target is internal still lands on the entry
of a function of the partition: declaring a relocation does not excuse a call
from the entry rule, it only changes which address the rule is applied to. -/
theorem check_relocated_internal_is_entry {r : Region} {p : Partition} {fuel : Nat}
    {acc : Accepted} (h : check r p fuel = .ok acc) {addr target : Nat}
    (hc : (addr, Target.internal target) ∈ acc.relocatedCalls) :
    ∃ g ∈ p.funcs, target = g.entry := by
  obtain ⟨ds, hds, -, -, -, -, hbody, rfl⟩ := check_ok_inv h
  obtain ⟨d, hd, rfl, ⟨rel, hi⟩, hrt⟩ := relocatedCall_inv hc
  obtain ⟨f, hf, hcov⟩ := func_of_mem_ds h hds hd (by simp [hi, isNop])
  have hce := checkBody_eq_none (bodyOf ds f) (hbody f hf) d (mem_bodyOf.mpr ⟨hd, hcov⟩)
    _ (mem_edges_call hi)
  simp only [checkEdge, hrt] at hce
  split at hce
  · rename_i hmem
    simp only [Partition.entries, List.mem_map] at hmem
    obtain ⟨g, hg, hge⟩ := hmem
    exact ⟨g, hg, hge.symm⟩
  · cases hce

/-- A relocated call whose declared target is an undefined symbol reaches a
symbol the proposal declared, and the site is recorded in `assumedExternal`.
Those records are the whole of what acceptance assumes about the link. -/
theorem check_relocated_external_declared {r : Region} {p : Partition} {fuel : Nat}
    {acc : Accepted} (h : check r p fuel = .ok acc) {addr : Nat} {name : String}
    (hc : (addr, Target.external name) ∈ acc.relocatedCalls) :
    name ∈ p.externals ∧ (addr, name) ∈ acc.assumedExternal := by
  obtain ⟨ds, hds, -, -, -, -, hbody, rfl⟩ := check_ok_inv h
  refine ⟨?_, ?_⟩
  · obtain ⟨d, hd, rfl, ⟨rel, hi⟩, hrt⟩ := relocatedCall_inv hc
    obtain ⟨f, hf, hcov⟩ := func_of_mem_ds h hds hd (by simp [hi, isNop])
    have hce := checkBody_eq_none (bodyOf ds f) (hbody f hf) d (mem_bodyOf.mpr ⟨hd, hcov⟩)
      _ (mem_edges_call hi)
    simp only [checkEdge, hrt] at hce
    split at hce
    · assumption
    · cases hce
  · simp only [externalCallSites, List.mem_filterMap]
    exact ⟨(addr, Target.external name), hc, rfl⟩

/-- **Padding is unreachable.** No fall-through, jump or branch of an accepted
function targets a byte of a declared padding run. This is why `check` has no
padding-reachability rule: every such edge target is required to stay inside
the function, and a function's extent is disjoint from every padding run, so a
runtime check for it could never fire, and a branch of a checker that cannot
fire is worse than a theorem. Calls are covered by `check_entry_not_padding`
together with the entry rule, except at the relocated sites `check_sound_step`
already excludes. -/
theorem check_padding_unreachable {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (h : check r p fuel = .ok acc) {f : FunctionSpec} (hf : f ∈ p.funcs)
    {d : Decoded} (hd : d ∈ acc.body f) {addr : Nat}
    (he : Edge.fallthrough addr ∈ d.edges ∨ Edge.jump addr ∈ d.edges ∨
      Edge.branch addr ∈ d.edges) : ¬ p.InPadding addr := by
  obtain ⟨ds, hds, -, -, -, -, hbody, rfl⟩ := check_ok_inv h
  have hbodyeq : Accepted.body
      { region := r, partition := p, bodies := p.funcs.map fun g => (g, bodyOf ds g),
        relocatedCalls := relocatedCallSites ds p,
        assumedExternal := externalCallSites ds p } f = bodyOf ds f :=
    body_of_mem p.funcs hf
  rw [hbodyeq] at hd
  have hedges := checkBody_eq_none (bodyOf ds f) (hbody f hf) d hd
  refine not_inPadding_of_covers h hf ?_
  rcases he with he | he | he
  · exact (checkEdge_intra (Or.inl (hedges _ he))).1
  · exact (checkEdge_intra (Or.inr (Or.inl (hedges _ he)))).1
  · exact (checkEdge_intra (Or.inr (Or.inr (hedges _ he)))).1

/-- Every instruction of an accepted padding run is a NOP. -/
theorem check_padding_nop {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    {ds : List Decoded} (h : check r p fuel = .ok acc) (hds : r.decode? fuel = some ds)
    {d : Decoded} (hd : d ∈ ds) (hp : p.InPadding d.addr) : isNop d.instr = true := by
  obtain ⟨ds', hds', -, -, -, hnop, -⟩ := check_ok_inv h
  rw [hds'] at hds
  cases hds
  exact hnop d hd hp

end Silmaril.X86.Decompile
