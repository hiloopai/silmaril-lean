module

public import Silmaril.X86.Decompile.Functions

/-!
# Control-flow graph recovery, one function at a time

`Decompile.check` accepts a partition of a code region into functions. This
file is the next rung: an agent *proposes* a control-flow graph for one of
those functions — where the basic blocks are and which block can reach which —
and `checkCfg` *verifies* the proposal against the accepted partition. As with
`check`, nothing about the proposal is trusted, the checker is total and
decidable, and every rejection names the block, address or edge that caused it.

## What a block is here

A `BlockSpec` is a pair of addresses: where the block starts and where its
terminator starts. Both are instruction addresses, and the block is the run of
instructions from the first to the second inclusive. Acceptance means:

* the blocks tile the function — every decoded instruction of the function lies
  in exactly one of them, with no gap and no overlap (`checkCfg_partitions`);
* every instruction strictly inside a block is a retiring instruction, so a
  block really is straight-line code (`checkCfg_interior`);
* the proposal's outgoing edges of a block are *exactly* the intraprocedural
  successors the decoded terminator admits — neither fewer nor more
  (`checkCfg_no_indirect`, `checkCfg_exit`).

## Which edges are CFG edges

`Decoded.edges` lists six kinds of successor. Only three of them are edges of a
control-flow graph:

* `Edge.fallthrough`, `Edge.jump` and `Edge.branch` are CFG edges;
* `Edge.call` is **not**. A call leaves the function, and the partition rung
  already says where it may land (`check_sound_step`); within this function the
  call contributes only its fall-through, which `Decoded.edges` lists
  separately. So a `call` terminates its block and has exactly one CFG
  successor, the instruction after it;
* `Edge.ret` and `Edge.halt` contribute nothing. The target of a `ret` is a
  stack value, not a static datum, and `ud2` does not retire at all. A block
  ending in either has no outgoing edges, which is why `CfgSpec.edges` is a
  list of pairs rather than a total successor function.

`Decoded.cfgTargets` is the resulting projection, and `mem_cfgTargets` is the
equation that justifies calling it exactly the fall-through, jump and branch
targets.

## The arithmetic the checker settles

`Decoded.next` is the fall-through address *as the machine computes it*, modulo
`2 ^ 64`, while the decoded listing chains addresses as plain naturals
(`Region.decode?_chain`). `checkCfg_interior` has to identify the machine's
successor with the next listed instruction, so the two must agree, which they
do exactly when the region ends below `2 ^ 64`.

That is a decidable property of the region, so the checker decides it rather
than passing it on: `CfgReject.regionWraps` is the rejection, and the soundness
statements are free of numeric side conditions. A side condition on a headline
theorem is a side condition every caller has to rediscover, and the next rung
would have to carry it through its own composition.

## What this rung does not do

It does not identify loops, dominators or regions, and it does not merge the
per-function graphs into a call graph. It also makes no claim about
reachability: a block the proposal lists but nothing can reach is accepted, as
it must be, since a function may be entered at a point only an indirect call
names.
-/

@[expose] public section

namespace Silmaril.X86.Decompile

open Silmaril.X86 (Byte State MState Word)
open Silmaril.Process (Memory)

/-! ## Proposals -/

/-- A proposed basic block: the address it starts at and the address of its
terminator. Both are addresses of instructions of the function, and the block
is the run of instructions from the first to the second inclusive. -/
structure BlockSpec where
  /-- The address of the block's first instruction. -/
  start : Nat
  /-- The address of the block's last instruction. -/
  terminator : Nat
  deriving DecidableEq, Repr

/-- A proposed control-flow graph for one function: its blocks in increasing
address order, and the edges between them. An edge is a pair of block start
addresses. -/
structure CfgSpec where
  /-- The function whose control flow is being proposed. -/
  func : FunctionSpec
  /-- The proposed basic blocks, in increasing address order. -/
  blocks : List BlockSpec
  /-- The proposed edges, as pairs of source and target block start
  addresses. -/
  edges : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- A block covers the closed range of addresses `[start, terminator]`: the
terminator is the address of an instruction, not the address past one. -/
def BlockSpec.Covers (b : BlockSpec) (addr : Nat) : Prop :=
  b.start ≤ addr ∧ addr ≤ b.terminator

instance (b : BlockSpec) (addr : Nat) : Decidable (b.Covers addr) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Two blocks cover no address in common. -/
def BlockSpec.Disjoint (b b' : BlockSpec) : Prop := ∀ addr, ¬ (b.Covers addr ∧ b'.Covers addr)

/-- Disjointness does not depend on the order of the two blocks. -/
theorem BlockSpec.disjoint_symm {b b' : BlockSpec} (h : b.Disjoint b') : b'.Disjoint b :=
  fun addr hb => h addr ⟨hb.2, hb.1⟩

instance : Std.Symm BlockSpec.Disjoint where symm _ _ h := BlockSpec.disjoint_symm h

/-- Some block of the proposal covers `addr`. -/
def CfgSpec.InSomeBlock (spec : CfgSpec) (addr : Nat) : Prop := ∃ b ∈ spec.blocks, b.Covers addr

instance (spec : CfgSpec) (addr : Nat) : Decidable (spec.InSomeBlock addr) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-! ## The edges of one instruction that are CFG edges -/

/-- The intraprocedural successors of one instruction: its fall-through, jump
and branch targets. A `call` target is not one of them — the call leaves the
function, and its fall-through is listed separately — and `ret` and `ud2`
contribute none. -/
def Decoded.cfgTargets (d : Decoded) : List Nat :=
  d.edges.filterMap fun e =>
    match e with
    | .fallthrough t => some t
    | .jump t => some t
    | .branch t => some t
    | .call _ => none
    | .ret => none
    | .halt => none

/-- The fall-through targets of one instruction: at most one, and none for a
`jmp`, a `ret` or `ud2`. -/
def Decoded.fallthroughTargets (d : Decoded) : List Nat :=
  d.edges.filterMap fun e =>
    match e with
    | .fallthrough t => some t
    | _ => none

/-- `cfgTargets` lists exactly the fall-through, jump and branch targets. -/
theorem mem_cfgTargets {d : Decoded} {t : Nat} :
    t ∈ d.cfgTargets ↔
      Edge.fallthrough t ∈ d.edges ∨ Edge.jump t ∈ d.edges ∨ Edge.branch t ∈ d.edges := by
  simp only [Decoded.cfgTargets, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, heq⟩
    cases e <;> simp_all
  · rintro (h | h | h)
    exacts [⟨_, h, rfl⟩, ⟨_, h, rfl⟩, ⟨_, h, rfl⟩]

/-- `fallthroughTargets` lists exactly the fall-through targets. -/
theorem mem_fallthroughTargets {d : Decoded} {t : Nat} :
    t ∈ d.fallthroughTargets ↔ Edge.fallthrough t ∈ d.edges := by
  simp only [Decoded.fallthroughTargets, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, heq⟩
    cases e <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩

/-- The intraprocedural successors of the instruction at `addr`, or none when
there is no instruction there. Writing the lookup as a total function keeps
`checkCfg` free of a branch for "the terminator is not an instruction", which
the alignment check has already excluded. -/
def cfgTargetsAt (body : List Decoded) (addr : Nat) : List Nat :=
  ((at? body addr).map Decoded.cfgTargets).getD []

/-- The fall-through targets of the instruction at `addr`, or none when there
is no instruction there. -/
def fallthroughTargetsAt (body : List Decoded) (addr : Nat) : List Nat :=
  ((at? body addr).map Decoded.fallthroughTargets).getD []

/-- Every fall-through target of a block's terminator stays inside the
function: the block does not fall out of its own function. -/
def CfgSpec.TerminatorInside (spec : CfgSpec) (body : List Decoded) (b : BlockSpec) : Prop :=
  ∀ t ∈ fallthroughTargetsAt body b.terminator, spec.func.Covers t

instance (spec : CfgSpec) (body : List Decoded) (b : BlockSpec) :
    Decidable (spec.TerminatorInside body b) := inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- A proposed edge is justified: it leaves a block of the proposal, and the
decoded terminator of that block admits its target. -/
def CfgSpec.EdgeJustified (spec : CfgSpec) (body : List Decoded) (e : Nat × Nat) : Prop :=
  ∃ b ∈ spec.blocks, b.start = e.1 ∧ e.2 ∈ cfgTargetsAt body b.terminator

instance (spec : CfgSpec) (body : List Decoded) (e : Nat × Nat) :
    Decidable (spec.EdgeJustified body e) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-! ## Rejection -/

/-- Why a proposed control-flow graph was rejected. Each case names the block,
address or edge that caused it, so that the proposing agent can repair the
proposal. -/
inductive CfgReject where
  /-- The accepted region runs up to or past `2 ^ 64`, so the fall-through
  address the machine computes need not be the next address of the listing.
  No real code region trips this: it exists so that `Decoded.next`'s modular
  arithmetic and `Region.decode?_chain`'s plain naturals are known to agree,
  and `checkCfg_interior` can be stated without a numeric side condition. It is
  the same fact, one level up, as the strict inequality
  `Region.loadedIn_load` needs — `Memory.checkSpan` requires a start address
  strictly below `Process.addressLimit`, which is `2 ^ 64`. -/
  | regionWraps (limit : Nat)
  /-- The proposal names a function the accepted partition does not contain. -/
  | notAFunction (f : FunctionSpec)
  /-- Two blocks are listed out of address order. `checkCfg` does not sort its
  input, for the same reason `check` does not. -/
  | unordered (first second : BlockSpec)
  /-- A block is empty, or leaves the function's extent. -/
  | blockOutside (b : BlockSpec)
  /-- A block's start or terminator is not the address of an instruction of the
  function. -/
  | blockNotAligned (addr : Nat)
  /-- The instruction occupying `[start, stop)` lies in no block. -/
  | uncovered (start stop : Nat)
  /-- Two blocks share an instruction. -/
  | overlap (first second : BlockSpec)
  /-- An instruction strictly inside a block transfers control, so the block is
  not straight-line code. -/
  | interiorTransfer (block : BlockSpec) (addr : Nat)
  /-- The function's entry is the start of no block. -/
  | noEntryBlock (entry : Nat)
  /-- The decoded terminator of the block starting at `source` admits `target`
  as an intraprocedural successor, and the proposal does not list it. -/
  | missingEdge (source target : Nat)
  /-- The proposal lists an edge no block's decoded terminator admits, or one
  whose source is the start of no block. -/
  | unjustifiedEdge (source target : Nat)
  /-- The proposal lists an edge whose target is the start of no block. -/
  | edgeTargetNotBlockStart (source target : Nat)
  /-- A block's terminator falls through past the function's extent. -/
  | terminatorFallsOut (block : BlockSpec)
  deriving DecidableEq, Repr

/-! ## The accepted graph -/

/-- A checked control-flow graph: the accepted partition it was checked
against, the proposal, and the decoded instructions of each block. -/
structure CheckedCfg where
  /-- The accepted partition the graph was checked against. -/
  accepted : Accepted
  /-- The proposal that was accepted. -/
  spec : CfgSpec
  /-- Each block of the proposal with its decoded instructions, in address
  order. -/
  bodies : List (BlockSpec × List Decoded)
  deriving DecidableEq, Repr

/-- The decoded instructions whose address a block covers, in address order. -/
def blockBody (body : List Decoded) (b : BlockSpec) : List Decoded :=
  body.filter fun d => decide (b.Covers d.addr)

/-- The decoded body the checker assigned to `b`, or `[]` if `b` is not a block
of the accepted graph. -/
def CheckedCfg.body (c : CheckedCfg) (b : BlockSpec) : List Decoded :=
  (c.bodies.find? fun entry => entry.1 == b).elim [] Prod.snd

/-! ## The checker -/

/-- A block must be a non-empty range of addresses inside the function's
extent, and both of its endpoints must be instruction addresses. -/
def checkBlockRange (f : FunctionSpec) (body : List Decoded) (b : BlockSpec) :
    Option CfgReject :=
  if ¬ (f.Covers b.start ∧ f.Covers b.terminator ∧ b.start ≤ b.terminator) then
    some (.blockOutside b)
  else if ¬ IsStart body b.start then some (.blockNotAligned b.start)
  else if ¬ IsStart body b.terminator then some (.blockNotAligned b.terminator)
  else none

/-- Consecutive blocks must be in increasing address order and must not share
an instruction. -/
def checkOrder : List BlockSpec → Option CfgReject
  | [] => none
  | [_] => none
  | b :: b' :: rest =>
    if b'.start < b.start then some (.unordered b b')
    else if b'.start ≤ b.terminator then some (.overlap b b')
    else checkOrder (b' :: rest)

/-- Every instruction of a block other than its terminator must retire to the
following address, so that the block is straight-line code. -/
def checkInterior (b : BlockSpec) : List Decoded → Option CfgReject
  | [] => none
  | d :: rest =>
    if d.addr = b.terminator then checkInterior b rest
    else if retiring d.instr then checkInterior b rest
    else some (.interiorTransfer b d.addr)

/-- Check a proposed control-flow graph against an accepted partition. Total,
decidable, and informative on failure.

The checks are written as nested `match`es rather than in `do` notation so that
both the kernel and `checkCfg_ok_inv` can take them apart one at a time. -/
def checkCfg (acc : Accepted) (spec : CfgSpec) : Except CfgReject CheckedCfg :=
  if 2 ^ 64 ≤ acc.region.base + acc.region.bytes.length then
    .error (.regionWraps (acc.region.base + acc.region.bytes.length))
  else if spec.func ∉ acc.partition.funcs then .error (.notAFunction spec.func)
  else
    let body := acc.body spec.func
    match spec.blocks.findSome? (checkBlockRange spec.func body) with
    | some rej => .error rej
    | none =>
      match checkOrder spec.blocks with
      | some rej => .error rej
      | none =>
        match body.find? fun d => decide (¬ spec.InSomeBlock d.addr) with
        | some d => .error (.uncovered d.addr (d.addr + d.size))
        | none =>
          if spec.func.entry ∉ spec.blocks.map BlockSpec.start then
            .error (.noEntryBlock spec.func.entry)
          else
            match spec.blocks.findSome? fun b => checkInterior b (blockBody body b) with
            | some rej => .error rej
            | none =>
              match spec.blocks.find? fun b =>
                  decide (¬ spec.TerminatorInside body b) with
              | some b => .error (.terminatorFallsOut b)
              | none =>
                match spec.blocks.findSome? fun b =>
                    (cfgTargetsAt body b.terminator).findSome? fun t =>
                      if (b.start, t) ∈ spec.edges then none
                      else some (CfgReject.missingEdge b.start t) with
                | some rej => .error rej
                | none =>
                  match spec.edges.find? fun e =>
                      decide (¬ spec.EdgeJustified body e) with
                  | some e => .error (.unjustifiedEdge e.1 e.2)
                  | none =>
                    match spec.edges.find? fun e =>
                        decide (e.2 ∉ spec.blocks.map BlockSpec.start) with
                    | some e => .error (.edgeTargetNotBlockStart e.1 e.2)
                    | none =>
                      .ok { accepted := acc, spec := spec,
                            bodies := spec.blocks.map fun b => (b, blockBody body b) }

/-! ## Adjacency in a listing

`Region.decode?_chain` says each listed address is the previous one plus the
previous size, and `Region.decode?_addr_pairwise` says the listed addresses
strictly increase. A block needs one more reading of the same walk: two listed
instructions never overlap, so an instruction that starts before a block's
terminator also ends no later than it. -/

/-- No two instructions of a successful walk overlap. -/
theorem decodeFrom_no_overlap : ∀ (fuel addr : Nat) (bytes : List Byte) (ds : List Decoded),
    decodeFrom fuel addr bytes = .ok ds →
    ∀ d ∈ ds, ∀ e ∈ ds, d.addr < e.addr → d.addr + d.size ≤ e.addr := by
  intro fuel
  induction fuel with
  | zero =>
    intro addr bytes ds h
    cases bytes with
    | nil => simp only [decodeFrom, Except.ok.injEq] at h; subst h; simp
    | cons b t => simp [decodeFrom] at h
  | succ fuel ih =>
    intro addr bytes ds h
    cases bytes with
    | nil => simp only [decodeFrom, Except.ok.injEq] at h; subst h; simp
    | cons b t =>
      simp only [decodeFrom] at h
      split at h
      · simp at h
      · rename_i i n hdec
        split at h
        · simp at h
        · rename_i hn0
          cases hrest : decodeFrom fuel (addr + n) ((b :: t).drop n) with
          | error e => rw [hrest] at h; simp [Except.map] at h
          | ok tail =>
            rw [hrest] at h
            simp only [Except.map, Except.ok.injEq] at h
            subst h
            have hn : 0 < n := Nat.pos_of_ne_zero hn0
            have htail : ∀ x ∈ tail, addr + n ≤ x.addr := fun x hx =>
              (decodeFrom_mem fuel (addr + n) ((b :: t).drop n) tail hrest x hx).1
            intro d hdm e hem hlt
            rcases List.mem_cons.mp hdm with rfl | hdt
            · rcases List.mem_cons.mp hem with rfl | het
              · omega
              · simpa using htail e het
            · rcases List.mem_cons.mp hem with rfl | het
              · have := htail d hdt
                simp only at hlt
                omega
              · exact ih (addr + n) _ tail hrest d hdt e het hlt

/-- No two instructions of a decoded region overlap: an instruction that starts
earlier ends no later than the next one starts. -/
theorem Region.decode?_no_overlap {r : Region} {fuel : Nat} {ds : List Decoded}
    (h : r.decode? fuel = some ds) :
    ∀ d ∈ ds, ∀ e ∈ ds, d.addr < e.addr → d.addr + d.size ≤ e.addr :=
  decodeFrom_no_overlap fuel r.base r.bytes ds (Region.decode?_eq_some_iff.mp h)

/-- The addresses of a function's body strictly increase, since the body is a
sublist of the listing. -/
theorem starts_bodyOf_pairwise {ds : List Decoded} (h : (starts ds).Pairwise (· < ·))
    (f : FunctionSpec) : (starts (bodyOf ds f)).Pairwise (· < ·) :=
  List.Pairwise.sublist (List.Sublist.map _ List.filter_sublist) h

/-! ## Inverting the checker

Everything below reads a successful `checkCfg` back into the facts it
established. `checkCfg_ok_inv` is the single inversion; the rest are
consequences. -/

/-- A block that passed `checkBlockRange` is a non-empty range inside the
function whose endpoints are instruction addresses. -/
theorem checkBlockRange_eq_none {f : FunctionSpec} {body : List Decoded} {b : BlockSpec}
    (h : checkBlockRange f body b = none) :
    (f.Covers b.start ∧ f.Covers b.terminator ∧ b.start ≤ b.terminator) ∧
      IsStart body b.start ∧ IsStart body b.terminator := by
  unfold checkBlockRange at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 h2 h3
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

/-- Every instruction of a block that passed `checkInterior`, other than its
terminator, retires. -/
theorem checkInterior_eq_none {b : BlockSpec} : ∀ body : List Decoded,
    checkInterior b body = none → ∀ d ∈ body, d.addr ≠ b.terminator → retiring d.instr = true := by
  intro body
  induction body with
  | nil => intro _ d hd; cases hd
  | cons e rest ih =>
    intro h d hd hne
    simp only [checkInterior] at h
    split at h
    · rcases List.mem_cons.mp hd with rfl | hm
      · exact absurd (by assumption) hne
      · exact ih h d hm hne
    · split at h
      · rcases List.mem_cons.mp hd with rfl | hm
        · assumption
        · exact ih h d hm hne
      · cases h

/-- Everything a successful `checkCfg` established. -/
theorem checkCfg_ok_inv {acc : Accepted} {spec : CfgSpec} {c : CheckedCfg}
    (h : checkCfg acc spec = .ok c) :
    acc.region.base + acc.region.bytes.length < 2 ^ 64 ∧
      spec.func ∈ acc.partition.funcs ∧
      (∀ b ∈ spec.blocks, spec.func.Covers b.start ∧ spec.func.Covers b.terminator ∧
        b.start ≤ b.terminator) ∧
      (∀ b ∈ spec.blocks, IsStart (acc.body spec.func) b.start ∧
        IsStart (acc.body spec.func) b.terminator) ∧
      checkOrder spec.blocks = none ∧
      (∀ d ∈ acc.body spec.func, ∃ b ∈ spec.blocks, b.Covers d.addr) ∧
      (∃ b ∈ spec.blocks, b.start = spec.func.entry) ∧
      (∀ b ∈ spec.blocks, ∀ d ∈ blockBody (acc.body spec.func) b, d.addr ≠ b.terminator →
        retiring d.instr = true) ∧
      (∀ b ∈ spec.blocks, ∀ t ∈ fallthroughTargetsAt (acc.body spec.func) b.terminator,
        spec.func.Covers t) ∧
      (∀ b ∈ spec.blocks, ∀ t ∈ cfgTargetsAt (acc.body spec.func) b.terminator,
        (b.start, t) ∈ spec.edges) ∧
      (∀ e ∈ spec.edges, ∃ b ∈ spec.blocks, b.start = e.1 ∧
        e.2 ∈ cfgTargetsAt (acc.body spec.func) b.terminator) ∧
      (∀ e ∈ spec.edges, e.2 ∈ spec.blocks.map BlockSpec.start) ∧
      c = { accepted := acc, spec := spec,
            bodies := spec.blocks.map fun b => (b, blockBody (acc.body spec.func) b) } := by
  unfold checkCfg at h
  split at h
  · cases h
  · rename_i hwrap
    refine ⟨by omega, ?_⟩
    split at h
    · cases h
    · rename_i hfunc
      refine ⟨by simpa using hfunc, ?_⟩
      simp only at h
      split at h
      · cases h
      · rename_i hrange
        have hrange' := fun b hb =>
          checkBlockRange_eq_none (List.findSome?_eq_none_iff.mp hrange b hb)
        refine ⟨fun b hb => (hrange' b hb).1, fun b hb => (hrange' b hb).2, ?_⟩
        split at h
        · cases h
        · rename_i horder
          refine ⟨horder, ?_⟩
          split at h
          · cases h
          · rename_i hcover
            refine ⟨fun d hd => ?_, ?_⟩
            · have hfind := List.find?_eq_none.mp hcover d hd
              simp only [decide_eq_true_eq, Decidable.not_not] at hfind
              exact hfind
            · split at h
              · cases h
              · rename_i hentry
                refine ⟨?_, ?_⟩
                · have : spec.func.entry ∈ spec.blocks.map BlockSpec.start := by simpa using hentry
                  obtain ⟨b, hb, hbe⟩ := List.mem_map.mp this
                  exact ⟨b, hb, hbe⟩
                · split at h
                  · cases h
                  · rename_i hint
                    refine ⟨fun b hb => checkInterior_eq_none _
                      (List.findSome?_eq_none_iff.mp hint b hb), ?_⟩
                    split at h
                    · cases h
                    · rename_i hfall
                      refine ⟨fun b hb t ht => ?_, ?_⟩
                      · have hfind := List.find?_eq_none.mp hfall b hb
                        simp only [decide_eq_true_eq, Decidable.not_not] at hfind
                        exact hfind t ht
                      · split at h
                        · cases h
                        · rename_i hmiss
                          refine ⟨fun b hb t ht => ?_, ?_⟩
                          · have hb' := List.findSome?_eq_none_iff.mp hmiss b hb
                            have := List.findSome?_eq_none_iff.mp hb' t ht
                            split at this
                            · assumption
                            · cases this
                          · split at h
                            · cases h
                            · rename_i hunj
                              refine ⟨fun e he => ?_, ?_⟩
                              · have hfind := List.find?_eq_none.mp hunj e he
                                simp only [decide_eq_true_eq, Decidable.not_not] at hfind
                                exact hfind
                              · split at h
                                · cases h
                                · rename_i htgt
                                  refine ⟨fun e he => ?_, by cases h; rfl⟩
                                  have hfind := List.find?_eq_none.mp htgt e he
                                  simp only [decide_eq_true_eq, Decidable.not_not] at hfind
                                  exact hfind

/-- The blocks of an accepted graph are pairwise ordered: each one's terminator
lies strictly before the next one's start. -/
theorem checkOrder_pairwise : ∀ bs : List BlockSpec, (∀ b ∈ bs, b.start ≤ b.terminator) →
    checkOrder bs = none → bs.Pairwise fun b b' => b.terminator < b'.start := by
  intro bs
  induction bs with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons b rest ih =>
    intro hrange h
    cases rest with
    | nil => exact List.pairwise_singleton _ _
    | cons b' rest' =>
      simp only [checkOrder] at h
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i h1 h2
          have hrest : ∀ x ∈ b' :: rest', x.start ≤ x.terminator := fun x hx =>
            hrange x (List.mem_cons_of_mem _ hx)
          have hpair := ih hrest h
          refine List.Pairwise.cons (fun x hx => ?_) hpair
          rcases List.mem_cons.mp hx with rfl | hx'
          · omega
          · have hb' : b'.start ≤ b'.terminator := hrest b' (List.mem_cons_self ..)
            have := (List.pairwise_cons.mp hpair).1 x hx'
            omega

/-- The blocks of an accepted graph are pairwise ordered. -/
theorem checkCfg_blocks_ordered {acc : Accepted} {spec : CfgSpec} {c : CheckedCfg}
    (h : checkCfg acc spec = .ok c) :
    spec.blocks.Pairwise fun b b' => b.terminator < b'.start := by
  obtain ⟨-, -, hrange, -, horder, -⟩ := checkCfg_ok_inv h
  exact checkOrder_pairwise spec.blocks (fun b hb => (hrange b hb).2.2) horder

/-- No two blocks of an accepted graph share an instruction. -/
theorem checkCfg_blocks_disjoint {acc : Accepted} {spec : CfgSpec} {c : CheckedCfg}
    (h : checkCfg acc spec = .ok c) : spec.blocks.Pairwise BlockSpec.Disjoint :=
  (checkCfg_blocks_ordered h).imp fun hlt _addr hcov =>
    absurd (Nat.lt_of_le_of_lt hcov.2.1 (Nat.lt_of_le_of_lt hcov.1.2 hlt)) (Nat.lt_irrefl _)

/-- The body the checker recorded for a block of the proposal. -/
theorem body_of_mem_blocks {body : List Decoded} (bs : List BlockSpec) {b : BlockSpec}
    (hb : b ∈ bs) :
    ((bs.map fun x => (x, blockBody body x)).find? fun e => e.1 == b).elim [] Prod.snd
      = blockBody body b := by
  induction bs with
  | nil => cases hb
  | cons x rest ih =>
    rw [List.map_cons, List.find?_cons]
    cases hx : (x == b) with
    | true =>
      have : x = b := by simpa using hx
      subst this
      simp
    | false =>
      rcases List.mem_cons.mp hb with rfl | hm
      · simp at hx
      · simpa using ih hm

/-- The body the checker recorded for a block of the proposal. -/
theorem checkCfg_body {acc : Accepted} {spec : CfgSpec} {c : CheckedCfg}
    (h : checkCfg acc spec = .ok c) {b : BlockSpec} (hb : b ∈ spec.blocks) :
    c.body b = blockBody (acc.body spec.func) b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ := checkCfg_ok_inv h
  exact body_of_mem_blocks spec.blocks hb

/-- An instruction belongs to a block's body exactly when it is an instruction
of the function and the block covers its address. -/
theorem mem_blockBody {body : List Decoded} {b : BlockSpec} {d : Decoded} :
    d ∈ blockBody body b ↔ d ∈ body ∧ b.Covers d.addr := by
  simp [blockBody, List.mem_filter]

/-! ## Soundness

The statements below are at the `Ext.stepOpt` level that `check_sound_step`
uses, so that the two rungs compose without an adapter. -/

/-- The body an accepted partition recorded for one of its functions. -/
theorem check_body_eq {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    {ds : List Decoded} (hacc : check r p fuel = .ok acc) (hds : r.decode? fuel = some ds)
    {f : FunctionSpec} (hf : f ∈ p.funcs) : acc.body f = bodyOf ds f := by
  obtain ⟨ds', hds', -, -, -, -, -, rfl⟩ := check_ok_inv hacc
  rw [hds'] at hds
  cases hds
  exact body_of_mem p.funcs hf

/-- An accepted partition's region is the region it was checked against. -/
theorem check_region_eq {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (hacc : check r p fuel = .ok acc) : acc.region = r ∧ acc.partition = p := by
  obtain ⟨-, -, -, -, -, -, -, rfl⟩ := check_ok_inv hacc
  exact ⟨rfl, rfl⟩

/-- **At a call, control reaches a function entry or a declared relocated
site.** This is the call case of `check_sound_step`, extracted so that
`checkCfg_exit` can reuse it without repeating the inversion. -/
theorem call_edge_entry_or_relocated {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    (hacc : check r p fuel = .ok acc) {f : FunctionSpec} (hf : f ∈ p.funcs) {d : Decoded}
    (hd : d ∈ acc.body f) {t : Nat} (he : Edge.call t ∈ d.edges) :
    (∃ g ∈ p.funcs, t = g.entry) ∨ acc.IsRelocatedCall d.addr := by
  obtain ⟨ds, hds, -, -, -, -, hbody, hacceq⟩ := check_ok_inv hacc
  have hbodyeq := check_body_eq hacc hds hf
  subst hacceq
  rw [hbodyeq] at hd
  obtain ⟨rel, hrel⟩ := instr_of_mem_edges_call he
  have hce := checkBody_eq_none (bodyOf ds f) (hbody f hf) d hd _ he
  simp only [checkEdge] at hce
  cases hrt : relocTarget p d with
  | some tgt =>
    exact Or.inr ⟨tgt, mem_relocatedCallSites (mem_bodyOf.mp hd).1 hrel hrt⟩
  | none =>
    rw [hrt] at hce
    simp only at hce
    split at hce
    · rename_i hmem
      simp only [Partition.entries, List.mem_map] at hmem
      obtain ⟨g, hg, hge⟩ := hmem
      exact Or.inl ⟨g, hg, hge.symm⟩
    · cases hce

/-- `ret` does not retire to the following address. -/
theorem retiring_ret : retiring .ret = false := rfl

/-- **There are no unresolved indirect jumps.** Every intraprocedural successor
the decoded terminator of a block admits is an edge of the proposal, and its
target is the start of a block. This is a theorem rather than an assumption
because the modelled x86 subset has no indirect jump: `Decoded.edges_sound`
says the semantics produce no successor outside `Decoded.edges`, and the
checker has compared the proposal against the whole of that list. -/
theorem checkCfg_no_indirect {acc : Accepted} {spec : CfgSpec} {c : CheckedCfg}
    (h : checkCfg acc spec = .ok c) {b : BlockSpec} (hb : b ∈ spec.blocks)
    {d : Decoded} (hterm : at? (acc.body spec.func) b.terminator = some d) {t : Nat}
    (he : Edge.fallthrough t ∈ d.edges ∨ Edge.jump t ∈ d.edges ∨ Edge.branch t ∈ d.edges) :
    (b.start, t) ∈ spec.edges ∧ ∃ b' ∈ spec.blocks, b'.start = t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hmiss, -, htgt, -⟩ := checkCfg_ok_inv h
  have ht : t ∈ cfgTargetsAt (acc.body spec.func) b.terminator := by
    simp only [cfgTargetsAt, hterm, Option.map_some, Option.getD_some]
    exact mem_cfgTargets.mpr he
  have hedge := hmiss b hb t ht
  refine ⟨hedge, ?_⟩
  obtain ⟨b', hb', hb'start⟩ := List.mem_map.mp (htgt (b.start, t) hedge)
  exact ⟨b', hb', hb'start⟩

/-- **Every instruction of the function belongs to exactly one block.** -/
theorem checkCfg_partitions {acc : Accepted} {spec : CfgSpec} {c : CheckedCfg}
    (h : checkCfg acc spec = .ok c) {d : Decoded} (hd : d ∈ acc.body spec.func) :
    ∃! b, b ∈ spec.blocks ∧ d ∈ c.body b := by
  obtain ⟨-, -, -, -, -, hcov, -⟩ := checkCfg_ok_inv h
  obtain ⟨b, hb, hbc⟩ := hcov d hd
  refine ⟨b, ⟨hb, ?_⟩, ?_⟩
  · rw [checkCfg_body h hb]
    exact mem_blockBody.mpr ⟨hd, hbc⟩
  · rintro b' ⟨hb', hd'⟩
    rw [checkCfg_body h hb'] at hd'
    obtain ⟨-, hbc'⟩ := mem_blockBody.mp hd'
    by_contra hne
    exact (checkCfg_blocks_disjoint h).forall hb' hb hne d.addr ⟨hbc', hbc⟩

/-- **Inside a block, control walks forward.** From a non-terminator
instruction of a block, one retirement reaches the next instruction of the same
block: the instruction is straight-line, so the machine's successor RIP is the
fall-through address, and that address is an instruction of the same block.

No numeric side condition is needed: `checkCfg` rejects a region that runs up
to `2 ^ 64` with `CfgReject.regionWraps`, which is exactly what makes
`Decoded.next` agree with the plain sum here. -/
theorem checkCfg_interior {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    {spec : CfgSpec} {c : CheckedCfg} (hacc : check r p fuel = .ok acc)
    (h : checkCfg acc spec = .ok c)
    {b : BlockSpec} (hb : b ∈ spec.blocks) {d : Decoded} (hd : d ∈ c.body b)
    (hne : d.addr ≠ b.terminator) {exit : Word} {m next : MState}
    (hload : r.LoadedIn m.memory) (hrip : m.core.rip.toNat = d.addr)
    (hstep : Ext.stepOpt exit m = some next) :
    next.core.rip.toNat = d.addr + d.size ∧ IsStart (c.body b) next.core.rip.toNat := by
  obtain ⟨hwrap, hfunc, -, halign, -, -, -, hint, -⟩ := checkCfg_ok_inv h
  obtain ⟨ds, hds, -, -, -, -, hbody, -⟩ := check_ok_inv hacc
  obtain ⟨hregion, hpart⟩ := check_region_eq hacc
  have hf : spec.func ∈ p.funcs := by rw [hpart] at hfunc; exact hfunc
  have hbodyeq : acc.body spec.func = bodyOf ds spec.func := check_body_eq hacc hds hf
  have hd' : d ∈ blockBody (acc.body spec.func) b := by rw [← checkCfg_body h hb]; exact hd
  have hret : retiring d.instr = true := hint b hb d hd' hne
  obtain ⟨hdbody, hdstart, hdterm⟩ := mem_blockBody.mp hd'
  have hdbody' : d ∈ bodyOf ds spec.func := by rw [← hbodyeq]; exact hdbody
  have hdds : d ∈ ds := (mem_bodyOf.mp hdbody').1
  have hedges : d.edges = [Edge.fallthrough d.next] := Decoded.edges_of_retiring hret
  have hce := checkBody_eq_none (bodyOf ds spec.func) (hbody spec.func hf) d hdbody'
    (Edge.fallthrough d.next) (by rw [hedges]; exact List.Mem.head _)
  obtain ⟨hfcov, hfstart⟩ := checkEdge_intra (Or.inl hce)
  have hwithin := Region.decode?_within hds d hdds
  have hnext : d.next = d.addr + d.size := by
    refine Decoded.next_eq_of_lt ?_
    rw [hregion] at hwrap
    omega
  have hripnext : next.core.rip.toNat = d.next := by
    rcases step_nextRip hds hload hdds hrip hstep with ⟨e, he, ht⟩ | hr
    · rw [hedges, List.mem_singleton] at he
      subst he
      exact ht
    · rw [hr, retiring_ret] at hret
      exact Bool.noConfusion hret
  refine ⟨by rw [hripnext, hnext], ?_⟩
  rw [hripnext, hnext, checkCfg_body h hb]
  obtain ⟨w, hw, hwaddr⟩ := List.mem_map.mp (halign b hb).2
  have hwds : w ∈ ds := by
    have : w ∈ bodyOf ds spec.func := by rw [← hbodyeq]; exact hw
    exact (mem_bodyOf.mp this).1
  have hbound : d.addr + d.size ≤ b.terminator := by
    have hlt : d.addr < w.addr := by
      rw [hwaddr]
      omega
    have := Region.decode?_no_overlap hds d hdds w hwds hlt
    omega
  obtain ⟨e, hees, headdr⟩ := List.mem_map.mp hfstart
  have hesize : 0 < d.size := Region.decode?_size_pos hds d hdds
  refine List.mem_map.mpr ⟨e, mem_blockBody.mpr ⟨?_, ?_⟩, by rw [headdr, hnext]⟩
  · rw [hbodyeq]
    refine mem_bodyOf.mpr ⟨hees, ?_⟩
    rw [headdr]
    exact hfcov
  · rw [headdr, hnext]
    exact ⟨by omega, hbound⟩

/-- **A block exits only along its edges.** From a block's terminator, one
retirement reaches the start of a block the proposal lists as a successor of
this one, or enters the entry of a function of the partition (a call), or the
terminator is a call site the proposal declared relocated, or the instruction
was `ret`, whose target is a stack value rather than a static datum. -/
theorem checkCfg_exit {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    {spec : CfgSpec} {c : CheckedCfg} (hacc : check r p fuel = .ok acc)
    (h : checkCfg acc spec = .ok c) {b : BlockSpec} (hb : b ∈ spec.blocks)
    {d : Decoded} (hd : d ∈ c.body b) (hterm : d.addr = b.terminator)
    {exit : Word} {m next : MState} (hload : r.LoadedIn m.memory)
    (hrip : m.core.rip.toNat = d.addr) (hstep : Ext.stepOpt exit m = some next) :
    (∃ t, (b.start, t) ∈ spec.edges ∧ next.core.rip.toNat = t ∧
        ∃ b' ∈ spec.blocks, b'.start = t) ∨
      (∃ g ∈ p.funcs, next.core.rip.toNat = g.entry) ∨
      acc.IsRelocatedCall d.addr ∨ d.instr = .ret := by
  obtain ⟨-, hfunc, -, -, -, -, -, -, -, -, -, -, -⟩ := checkCfg_ok_inv h
  obtain ⟨ds, hds, -, -, -, -, -, -⟩ := check_ok_inv hacc
  obtain ⟨-, hpart⟩ := check_region_eq hacc
  have hf : spec.func ∈ p.funcs := by rw [hpart] at hfunc; exact hfunc
  have hbodyeq : acc.body spec.func = bodyOf ds spec.func := check_body_eq hacc hds hf
  have hd' : d ∈ blockBody (acc.body spec.func) b := by rw [← checkCfg_body h hb]; exact hd
  obtain ⟨hdbody, -⟩ := mem_blockBody.mp hd'
  have hdbody' : d ∈ bodyOf ds spec.func := by rw [← hbodyeq]; exact hdbody
  have hdds : d ∈ ds := (mem_bodyOf.mp hdbody').1
  have hat : at? (acc.body spec.func) b.terminator = some d := by
    rw [← hterm]
    refine at?_eq_some_of_mem ?_ hdbody
    rw [hbodyeq]
    exact starts_bodyOf_pairwise (Region.decode?_addr_pairwise hds) spec.func
  rcases step_nextRip hds hload hdds hrip hstep with ⟨e, he, ht⟩ | hr
  · cases e with
    | fallthrough t =>
      obtain ⟨hedge, b', hb', hb'start⟩ := checkCfg_no_indirect h hb hat (Or.inl he)
      exact Or.inl ⟨t, hedge, ht, b', hb', hb'start⟩
    | jump t =>
      obtain ⟨hedge, b', hb', hb'start⟩ := checkCfg_no_indirect h hb hat (Or.inr (Or.inl he))
      exact Or.inl ⟨t, hedge, ht, b', hb', hb'start⟩
    | branch t =>
      obtain ⟨hedge, b', hb', hb'start⟩ := checkCfg_no_indirect h hb hat (Or.inr (Or.inr he))
      exact Or.inl ⟨t, hedge, ht, b', hb', hb'start⟩
    | call t =>
      rcases call_edge_entry_or_relocated hacc hf hdbody he with ⟨g, hg, hge⟩ | hrel
      · exact Or.inr (Or.inl ⟨g, hg, by rw [show next.core.rip.toNat = t from ht, hge]⟩)
      · exact Or.inr (Or.inr (Or.inl hrel))
    | ret => exact absurd ht (by simp [Edge.Target])
    | halt => exact absurd ht (by simp [Edge.Target])
  · exact Or.inr (Or.inr (Or.inr hr))

/-- **The two rungs compose.** Given an accepted partition and an accepted
control-flow graph for each of its functions, every decoded instruction of
every function lies in a block of that function's graph, and one retirement
from it either stays in the block, leaves along an edge the graph lists, enters
a function entry, sits at a declared relocated call site, or was a `ret`. -/
theorem check_checkCfg_step {r : Region} {p : Partition} {fuel : Nat} {acc : Accepted}
    {spec : FunctionSpec → CfgSpec} {chk : FunctionSpec → CheckedCfg}
    (hacc : check r p fuel = .ok acc) (hspec : ∀ f ∈ p.funcs, (spec f).func = f)
    (hcfg : ∀ f ∈ p.funcs, checkCfg acc (spec f) = .ok (chk f))
    {f : FunctionSpec} (hf : f ∈ p.funcs) {d : Decoded} (hd : d ∈ acc.body f)
    {exit : Word} {m next : MState} (hload : r.LoadedIn m.memory)
    (hrip : m.core.rip.toNat = d.addr) (hstep : Ext.stepOpt exit m = some next) :
    ∃ b ∈ (spec f).blocks, d ∈ (chk f).body b ∧
      (IsStart ((chk f).body b) next.core.rip.toNat ∨
        (∃ t, (b.start, t) ∈ (spec f).edges ∧ next.core.rip.toNat = t ∧
          ∃ b' ∈ (spec f).blocks, b'.start = t) ∨
        (∃ g ∈ p.funcs, next.core.rip.toNat = g.entry) ∨
        acc.IsRelocatedCall d.addr ∨ d.instr = .ret) := by
  have hc := hcfg f hf
  have hdf : d ∈ acc.body (spec f).func := by rw [hspec f hf]; exact hd
  obtain ⟨b, ⟨hb, hdb⟩, -⟩ := checkCfg_partitions hc hdf
  refine ⟨b, hb, hdb, ?_⟩
  by_cases hterm : d.addr = b.terminator
  · rcases checkCfg_exit hacc hc hb hdb hterm hload hrip hstep with h1 | h2 | h3 | h4
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
  · exact Or.inl (checkCfg_interior hacc hc hb hdb hterm hload hrip hstep).2

end Silmaril.X86.Decompile
