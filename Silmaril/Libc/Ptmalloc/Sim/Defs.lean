module

public import Silmaril.Libc.Ptmalloc.Algo.Defs
public import Silmaril.Libc.Ptmalloc.Env.Defs

/-!
# ptmalloc: block simulation (x86 ↔ algorithm, through the representation)

The x86 code is related to the algorithm model **one block at a time**. A block is a piece of
machine code between two cut points; its obligation (`BlockSim`) says: from any machine state
at the block's entry that represents an abstract state `a` (through `R`, built from
`LocalRep`) and satisfies the block's register precondition, the machine reaches one of the
block's exits in a state representing some `a'` with `step a a'` (a leaf operation or a piece
of a body of `Silmaril.Libc.Ptmalloc.Algo`), having written only inside the block's footprint.

* **Generic, proved here**: `Triple` (a total-correctness triple with a footprint over an
  abstract machine `Mach`), `Triple.seq` (sequential composition, footprints joined),
  `Triple.conseq`, `Triple.frame` (a fragment outside the footprint survives: the bridge
  from `Frag.holds_frame` to machine runs). These are the only lemmas a function-level proof
  needs to chain block obligations.
* **Outlining** (`Inlined`): when gcc inlined a helper (`tcache_get`, `tcache_put`,
  `unlink_chunk`, `checked_request2size`), the obligation at each inlined copy is the helper's
  `BlockSim` at that copy's addresses with `step` = the helper's leaf operation, so the
  abstract lemma about the leaf (`Task.algo.leafTcacheGet`, …) is proved once and reused at
  every site.
* **Prologue/epilogue apart from bodies** (`Task.sim.prologueSingle`): the `SINGLE_THREAD_P`
  shortcut (or `arena_get` + the lock) is its own block whose post hands the body an *arbitrary*
  arena address `av` with its invariant; body blocks never mention `main_arena`.
* **Callee contracts** (`Callee`): an external function's contract with an explicit write set,
  so a model fix like M4 (`__tunable_get_val` writes 4 bytes for tunable 0x12) or M8 (the vDSO
  stores its `timespec`) changes one `Callee` value, not the heap proofs.

`Mach` is abstract: the `x86sim` builder instantiates it with `Str9K` (state, `rip`, the
`MemView` of its memory, and the reflexive-transitive closure of `step`) in
`Silmaril.Libc.Ptmalloc.Sim.Str9K`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

open Silmaril.Data

/-- **An abstract machine**: states, the program counter, the memory as a `MemView`, and
reachability (reflexive, transitive). -/
structure Mach where
  St : Type
  pc : St → Nat
  view : St → MemView
  reach : St → St → Prop
  refl : ∀ s, reach s s
  trans : ∀ {s t u}, reach s t → reach t u → reach s u

namespace Mach

variable (M : Mach)

/-- `s'` differs from `s` only on the bytes in `fp` (values and permissions). -/
def Within (fp : Nat → Prop) (s s' : M.St) : Prop :=
  ∀ a, ¬ fp a → (M.view s).byte a = (M.view s').byte a ∧
    (M.view s).writable a = (M.view s').writable a

/-- **A total-correctness triple with a footprint**: from every state satisfying `P` the machine
reaches a state satisfying `Q`, changing only bytes in `fp`. -/
def Triple (P : M.St → Prop) (Q : M.St → Prop) (fp : Nat → Prop) : Prop :=
  ∀ s, P s → ∃ s', M.reach s s' ∧ Q s' ∧ M.Within fp s s'

variable {M}

theorem Triple.conseq {P P' Q Q' : M.St → Prop} {fp fp' : Nat → Prop}
    (h : M.Triple P Q fp) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s)
    (hfp : ∀ a, fp a → fp' a) : M.Triple P' Q' fp' := by
  intro s hs
  obtain ⟨s', hr, hq, hw⟩ := h s (hP s hs)
  exact ⟨s', hr, hQ s' hq, fun a ha => hw a fun h => ha (hfp a h)⟩

/-- **Sequential composition**: footprints join. -/
theorem Triple.seq {P Q R : M.St → Prop} {fp₁ fp₂ : Nat → Prop}
    (h₁ : M.Triple P Q fp₁) (h₂ : M.Triple Q R fp₂) :
    M.Triple P R fun a => fp₁ a ∨ fp₂ a := by
  intro s hs
  obtain ⟨t, hr₁, hq, hw₁⟩ := h₁ s hs
  obtain ⟨u, hr₂, hr, hw₂⟩ := h₂ t hq
  refine ⟨u, M.trans hr₁ hr₂, hr, fun a ha => ?_⟩
  obtain ⟨b1, w1⟩ := hw₁ a fun h => ha (.inl h)
  obtain ⟨b2, w2⟩ := hw₂ a fun h => ha (.inr h)
  exact ⟨b1.trans b2, w1.trans w2⟩

/-- **The frame rule on machine runs**: a fragment whose bytes miss the footprint survives. -/
theorem Triple.frame {P Q : M.St → Prop} {fp : Nat → Prop} (h : M.Triple P Q fp) (f : Frag)
    (hf : ∀ a ∈ f.bytes, ¬ fp a) :
    M.Triple (fun s => P s ∧ f.Holds (M.view s)) (fun s => Q s ∧ f.Holds (M.view s)) fp := by
  intro s ⟨hp, hh⟩
  obtain ⟨s', hr, hq, hw⟩ := h s hp
  exact ⟨s', hr, ⟨hq, Frag.holds_frame hh fun a ha => hw a (hf a ha)⟩, hw⟩

/-- A choice between two triples on a case split of the precondition. -/
theorem Triple.cases {P Q : M.St → Prop} {fp : Nat → Prop} (c : M.St → Prop)
    (h₁ : M.Triple (fun s => P s ∧ c s) Q fp) (h₂ : M.Triple (fun s => P s ∧ ¬ c s) Q fp) :
    M.Triple P Q fp := by
  intro s hs
  by_cases hc : c s
  · exact h₁ s ⟨hs, hc⟩
  · exact h₂ s ⟨hs, hc⟩

end Mach

/-! ## Block obligations -/

/-- **A block**: its entry address, its exits, the machine-side precondition (registers holding
abstract values: `pre a s`), and its footprint at the abstract state `a`. -/
structure Block (M : Mach) (A : Type) where
  entry : Nat
  exits : List Nat
  pre : A → M.St → Prop
  post : A → M.St → Prop
  fp : A → Nat → Prop

/-- **The block simulates `step` through `R`.** -/
def BlockSim {M : Mach} {A : Type} (R : A → M.St → Prop) (step : A → A → Prop) (b : Block M A) :
    Prop :=
  ∀ a, M.Triple (fun s => R a s ∧ b.pre a s ∧ M.pc s = b.entry)
    (fun s' => M.pc s' ∈ b.exits ∧ ∃ a', step a a' ∧ R a' s' ∧ b.post a' s') (b.fp a)

/-- **An inlined copy of a helper**: the helper's block obligation, moved to the copy's entry and
exits, with `step` the helper's leaf operation. The `x86sim` builder proves one `BlockSim` per
copy; the abstract lemma about `step` is shared. -/
def Inlined {M : Mach} {A : Type} (R : A → M.St → Prop) (leaf : A → Option A) (b : Block M A) :
    Prop :=
  BlockSim R (fun a a' => leaf a = some a') b

/-! ## Representation of a body's view on a machine -/

/-- The addresses a body's representation needs (per pin, relocated): struct offsets, statics,
the thread's TLS variables. -/
structure RepAt where
  layout : Layout
  statics : Statics
  tls : TlsAddrs
  env : EnvAddrs

/-- **The abstract state of a block**: the body's view, the surroundings, and the abstract
values of the block's live arguments/results (the block's `pre`/`post` tie them to registers). -/
abbrev AState := Local × Surr × List Nat

/-- **The representation's fragments** of a body's view (the cells `LocalRep` reads). -/
def repFrag (C : Config) (P : RepAt) (l : Local) : Frag :=
  arenaRep C P.layout l.shared.init l.avAddr l.av ++
    threadFrag C P.layout P.tls l.avAddr l.shared.key l.shared.init l.thread ++
    sharedFrag C P.layout P.statics l.shared

/-- **The surroundings are apart from the representation** (X1-2, SL-B, D2): no byte of an
`envFrag` cell is a byte of a `LocalRep` cell or of a heap span. `LocalRep`'s `Nodup` covers
only the heap's own fragments; without this a heap store could clobber an env cell as far as
the predicates say (D2 was such an overlap: an 8-byte `global_max_fast` cell over
`__always_fail_morecore`). An address fact: it does not read memory, and a step that keeps
`x.2.1` and the arena and writes only cells apart from `envFrag` keeps it. -/
def RepApart (C : Config) (P : RepAt) (x : AState) : Prop :=
  ∀ a ∈ (envFrag C P.layout P.env x.2.1).bytes,
    a ∉ (repFrag C P x.1).bytes ∧ ∀ s ∈ spansOf x.1.av, ¬ (s.1 ≤ a ∧ a < s.1 + s.2)

instance (C : Config) (P : RepAt) (x : AState) : Decidable (RepApart C P x) := by
  unfold RepApart; exact inferInstance

/-- **The machine represents the abstract state**: the body's view is well formed (so block
proofs may use e.g. the tcache's alignment, `TcacheWF`), represented, and so are the
surroundings, apart from the representation (`RepApart`). -/
def LocalAt (C : Config) (P : RepAt) (M : Mach) (x : AState) (s : M.St) : Prop :=
  LocalWF C x.1 ∧ LocalRep C P.layout P.statics P.tls x.1 (M.view s) ∧
    (envFrag C P.layout P.env x.2.1).Holds (M.view s) ∧ SurrInv x.2.1 x.1.kernel x.1.shared ∧
    RepApart C P x

/-! ## Callee contracts -/

/-- **An external callee's contract**: from its entry with arguments `args`, it returns having
written only `W args` (plus its own stack window, part of the machine's `Within` by the caller's
choice of `fp`) and established `post`. M4 and M8 are changes to `W` and `post` here. -/
structure Callee (M : Mach) where
  entry : Nat
  pre : M.St → Prop
  W : M.St → Nat → Prop
  post : M.St → M.St → Prop

/-! ## Obligations (owned by `x86sim`; stated generically, instantiated for glibc 2.39 on `Str9K`) -/

/-- **`Task.sim.tcacheGet`**: every inlined copy of `tcache_get` in the pinned `malloc`
simulates `Local.tcacheGet` through `LocalAt` (argument: the bin; result: the payload); its
footprint is the thread's fragment (count, head) and the popped entry's key word. -/
def Task.sim.tcacheGet (C : Config) (P : RepAt) (M : Mach) (copies : List (Block M AState)) :
    Prop :=
  ∀ b ∈ copies, BlockSim (LocalAt C P M)
    (fun x x' => ∃ p l', x.1.tcacheGet C (x.2.2.headD 0) = some (p, l') ∧ x' = (l', x.2.1, [p])) b

/-- **`Task.sim.tcachePut`**: likewise for each inlined `tcache_put` (in `_int_free`, and in
`_int_malloc`'s tcache refills); arguments: chunk address, chunk size, bin. -/
def Task.sim.tcachePut (C : Config) (P : RepAt) (M : Mach) (copies : List (Block M AState)) :
    Prop :=
  ∀ b ∈ copies, BlockSim (LocalAt C P M)
    (fun x x' => ∃ l', x.1.tcachePut (x.2.2.getD 0 0, x.2.2.getD 1 0) (x.2.2.getD 2 0) = some l' ∧
      x' = (l', x.2.1, [])) b

/-- **`Task.sim.prologueSingle`**: the `SINGLE_THREAD_P` shortcut of `__libc_malloc` (and of
`__libc_free`'s arena lookup) hands its body the arena of the post state with its invariant
owned; body obligations are then stated for that arbitrary arena (`Local.avAddr`). -/
def Task.sim.prologueSingle (C : Config) (P : RepAt) (M : Mach) (b : Block M AState) : Prop :=
  BlockSim (LocalAt C P M) (fun x x' => x' = x ∧ x.2.1.singleThreaded = true ∧ x.1.isMain = true) b

/-- The surroundings after a body: `__curbrk` follows a moved break (W12, `surrInv_step`). -/
def surrAfter (e : Surr) (l l' : Local) : Surr :=
  if l'.kernel.brk = l.kernel.brk then e else { e with curbrk := l'.kernel.brk }

/-- **`Task.sim.body`**: a body's x86 code (a list of blocks covering it, entry block first)
simulates the body `f` of the algorithm model: the template for `_int_malloc`, `_int_free`,
`sysmalloc`, …, each proved block by block with `Mach.Triple.seq`. -/
def Task.sim.body (C : Config) (P : RepAt) (M : Mach) (entry : Nat) (exits : List Nat)
    (pre : AState → M.St → Prop) (post : AState → M.St → Prop) (fp : AState → Nat → Prop)
    (f : Local → List Nat → Res (List Nat × Local)) : Prop :=
  BlockSim (LocalAt C P M)
    (fun x x' => ∃ r l', f x.1 x.2.2 = .ok (r, l') ∧ x' = (l', surrAfter x.2.1 x.1 l', r))
    ⟨entry, exits, pre, post, fp⟩

end Silmaril.Libc.Ptmalloc
