module

public import Silmaril.Libc.Alloc.Defs
public import Silmaril.Libc.X86Alloc.Ladder.Bump.Defs

/-!
# The allocator institution: the abstract level

The **signature** of an allocator is a fragment `F : Frag` of the API `malloc`, `calloc`,
`realloc`, `free` (`AFn`): a malloc/free-only allocator (the x86 ladder rungs) has the fragment
`Frag.mf`, a C library has `Frag.all`. Fewer functions is a **looser** signature.

A **model** is an abstract allocator `A : AbsAlloc`: a hidden state, the live blocks it shows
(its visible heap, `Libc.Heap`: block start ↦ requested size), the load-time state, and for each
call (`ACall`) the outcomes it may have: a new state and the returned word, or `none`, a
**safety violation** (the call was undefined: a double free, a free of a non-block, a use after
free).

The **sentences** are the contract of a fragment at a **strength** (`Strength`, ordered
`safe ≤ live ≤ functional`), each under a client discipline `P` (the calls the client makes;
`fun _ => True` for every call) and an implementation invariant `Inv` that the load-time state
establishes and every call keeps (an implementation's invariant: glibc's `heapRep`, a bump
allocator's arena bound):

| strength | `A` meets it on `F` when | parameter |
|---|---|---|
| `safe` (`AbsAlloc.Safe`) | every call of `F` has an outcome, and every outcome is one `allocLoose` allows (failure always allowed) | — |
| `live` (`AbsAlloc.Live`) | safe, and `malloc n` fails only when the capacity model `C` has no room at `α s`, which successful calls and frees move as `C` says | `C : CapModel`, `α : A.St → C.St` |
| `functional` (`AbsAlloc.Functional`) | safe, and `malloc n` returns exactly the reference model's `R.malloc (α s) n`, which moves as `R` says | `R : RefModel`, `α : A.St → R.St` |

`CapModel` and `RefModel` are the abstract models of the x86 allocator shapes
(`Silmaril.Libc.X86Alloc.Spec`), so the strengths of the
institution are the strengths of those shapes. Like the shapes, `live` and `functional` constrain
`malloc` and `free`; `calloc` and `realloc` are constrained at `safe` only (a later refinement).

**Instances.** `AbsAlloc.never` (every allocation fails, `free` releases) is the bottom
allocator: an instance of `safe` on the whole API (`Thms.never_safe`), with no success at all
(`Thms.never_succLe`: below every allocator in the success order `SuccLe`). `AbsAlloc.ofRef R s0`
is the allocator a reference model describes (malloc/free); `bump` is the x86 ladder's rung 02
through its reference model `Ladder.Bump.ref` (`Thms.bump_safe`, `Thms.bump_functional` on
positive requests; `Thms.bump_unsafe_zero`: **not** safe once `malloc (0)` is allowed, because it
returns the same address twice, which `allocLoose`'s freshness forbids), `neverMF` is rung 01's.

The ELF-level reading (a shared allocator file as a model) is `Silmaril.Libc.AllocElf`.
-/

@[expose] public section

namespace Silmaril.Libc

open Silmaril.Libc.X86Alloc (CapModel RefModel)

/-! ## Signatures: fragments of the API -/

/-- The four functions of the allocator API. -/
inductive AFn where
  | malloc | calloc | realloc | free
  deriving DecidableEq, Repr

/-- The function a call calls (`none`: a client access). -/
def ACall.fn : ACall → Option AFn
  | .malloc _ => some .malloc
  | .calloc _ _ => some .calloc
  | .realloc _ _ => some .realloc
  | .free _ => some .free
  | .access _ => none

/-- **A fragment** of the API: the functions a contract covers. -/
abbrev Frag := List AFn

/-- The whole API. -/
def Frag.all : Frag := [.malloc, .calloc, .realloc, .free]

/-- `malloc` and `free` (the x86 ladder). -/
def Frag.mf : Frag := [.malloc, .free]

/-- The call `c` is in the fragment `F` (a client access always is). -/
def ACall.In (F : Frag) (c : ACall) : Prop := ∀ f, c.fn = some f → f ∈ F

/-- Every request is positive (`malloc (0)`, `calloc` with a zero factor and `realloc (p, 0)` are
not made): the client discipline under which a bump allocator is an instance. -/
def PosReq : ACall → Prop
  | .malloc n => 0 < n
  | .calloc k m => 0 < k * m
  | .realloc _ n => 0 < n
  | _ => True

/-! ## Strengths -/

/-- The strength of an allocator contract. -/
inductive Strength where
  | safe | live | functional
  deriving DecidableEq, Repr

/-- Its rank: `safe < live < functional`. -/
def Strength.rank : Strength → Nat
  | .safe => 0
  | .live => 1
  | .functional => 2

instance : LE Strength := ⟨fun a b => a.rank ≤ b.rank⟩

/-! ## Models: abstract allocators -/

/-- **An abstract allocator**: hidden state, its visible heap, the load-time state, and the
allowed outcomes of each call (`none`: a safety violation). -/
structure AbsAlloc where
  St : Type
  heap : St → Heap
  init : St
  step : St → ACall → Option (St × Nat) → Prop

namespace AbsAlloc

variable (A : AbsAlloc)

/-- The visible outcome of an outcome. -/
def out : Option (A.St × Nat) → AOut
  | none => .ub
  | some (t, r) => .ok (A.heap t) r

/-- **`A` meets the relation `T` on the calls of `F` the client makes (`P`), under the
invariant `Inv`**: the load-time state shows the empty heap and satisfies `Inv`; from a state of
`Inv`, every such call has an outcome, every outcome is one `T` allows, and a returning call
keeps `Inv`. -/
structure SatOn (F : Frag) (P : ACall → Prop) (Inv : A.St → Prop) (T : AllocRel) : Prop where
  init : Inv A.init
  empty : A.heap A.init = Heap.empty
  rel : ∀ s c o, Inv s → c.In F → P c → A.step s c o → T (A.heap s) c (A.out o)
  inv : ∀ s c t r, Inv s → c.In F → P c → A.step s c (some (t, r)) → Inv t
  progress : ∀ s c, Inv s → c.In F → P c → ∃ o, A.step s c o

/-- **Safety** (strength `safe`): `A` meets `allocLoose` on `F` under some invariant. -/
def Safe (F : Frag) (P : ACall → Prop := fun _ => True) : Prop :=
  ∃ Inv, A.SatOn F P Inv allocLoose

/-- What liveness adds, under `Inv`: a `malloc` of `F` fails only when `C` has no room at `α s`
(and then leaves `α` unchanged); a success moves `α` by `C.alloc`; a `free` of a live block by
`C.dealloc`. -/
def LiveSteps (F : Frag) (P : ACall → Prop) (Inv : A.St → Prop) (C : CapModel)
    (α : A.St → C.St) : Prop :=
  (∀ s n t r, Inv s → .malloc ∈ F → P (.malloc n) → A.step s (.malloc n) (some (t, r)) →
    (r = 0 → ¬ C.avail (α s) n) ∧ (r ≠ 0 → α t = C.alloc (α s) n (BitVec.ofNat 64 r)) ∧
    (r = 0 → α t = α s)) ∧
  (∀ s p n t r, Inv s → .free ∈ F → P (.free p) → A.heap s p = some n → p ≠ 0 →
    A.step s (.free p) (some (t, r)) → α t = C.dealloc (α s) (BitVec.ofNat 64 p) n)

/-- **Liveness** (strength `live`) for the capacity model `C` along `α`. -/
def Live (F : Frag) (P : ACall → Prop) (C : CapModel) (α : A.St → C.St) : Prop :=
  ∃ Inv, A.SatOn F P Inv allocLoose ∧ A.LiveSteps F P Inv C α

/-- What functional correctness adds, under `Inv`: `malloc n` of `F` returns exactly
`R.malloc (α s) n` and moves `α` by `R.alloc` when it succeeds (not at all when it fails); a
`free` of a live block moves it by `R.dealloc`. -/
def FunSteps (F : Frag) (P : ACall → Prop) (Inv : A.St → Prop) (R : RefModel)
    (α : A.St → R.St) : Prop :=
  (∀ s n t r, Inv s → .malloc ∈ F → P (.malloc n) → A.step s (.malloc n) (some (t, r)) →
    r = (R.malloc (α s) n).toNat ∧ (r ≠ 0 → α t = R.alloc (α s) n) ∧ (r = 0 → α t = α s)) ∧
  (∀ s p n t r, Inv s → .free ∈ F → P (.free p) → A.heap s p = some n → p ≠ 0 →
    A.step s (.free p) (some (t, r)) → α t = R.dealloc (α s) (BitVec.ofNat 64 p) n)

/-- **Functional correctness** (strength `functional`) against the reference model `R`
along `α`. -/
def Functional (F : Frag) (P : ACall → Prop) (R : RefModel) (α : A.St → R.St) : Prop :=
  ∃ Inv, A.SatOn F P Inv allocLoose ∧ A.FunSteps F P Inv R α

/-- `A` succeeds on the call `c` from `s`: some outcome returns a non-null word. -/
def Succeeds (s : A.St) (c : ACall) : Prop := ∃ t r, A.step s c (some (t, r)) ∧ r ≠ 0

end AbsAlloc

/-- **The success order**: every request on which `A` can succeed (from some state with a given
visible heap), `B` can succeed on (from some state with the same visible heap). -/
def AbsAlloc.SuccLe (A B : AbsAlloc) : Prop :=
  ∀ s c, A.Succeeds s c → c.fn ≠ some .free → ∃ s', B.heap s' = A.heap s ∧ B.Succeeds s' c

/-! ## Instances -/

/-- The empty capacity model: nothing is ever available. -/
def capNone : CapModel where
  St := Unit
  avail _ _ := False
  alloc _ _ _ := ()
  dealloc _ _ _ := ()

/-- **The bottom allocator** (`allocNever`): its state is its visible heap; every allocation
fails; `free`, `realloc (p, 0)` and client accesses are as in `allocLoose`. -/
def AbsAlloc.never : AbsAlloc where
  St := Heap
  heap h := h
  init := Heap.empty
  step h c o := match o with
    | none => allocNever h c .ub
    | some (t, r) => allocNever h c (.ok t r)

/-- **The allocator a reference model describes**, on `malloc` and `free`, from the state `s0`:
the hidden state is `R`'s state and the visible heap. `malloc (n)` returns `R.malloc s n`
(failure at `0`); `free (p)` of a live block moves `R` by `R.dealloc` and releases it; `free (0)`
does nothing; any other `free` is a safety violation, as is every `calloc`/`realloc` (outside
the fragment). A client access is as in `allocLoose`. -/
abbrev AbsAlloc.ofRef (R : RefModel) (s0 : R.St) : AbsAlloc where
  St := R.St × Heap
  heap x := x.2
  init := (s0, Heap.empty)
  step x c o := match c with
    | .malloc n =>
      let p := R.malloc x.1 n
      o = if p = 0 then some (x, 0) else some ((R.alloc x.1 n, x.2.add p.toNat n), p.toNat)
    | .free p =>
      if p = 0 then o = some (x, 0)
      else match x.2 p with
        | some n => o = some ((R.dealloc x.1 (BitVec.ofNat 64 p) n, x.2.remove p), 0)
        | none => o = none
    | .access p => (x.2.Owns p ∧ o = some (x, 0)) ∨ (¬ x.2.Owns p ∧ o = none)
    | .calloc _ _ | .realloc _ _ => o = none

/-- Rung 01's model: the reference model that never allocates. -/
abbrev neverRef : RefModel where
  St := Unit
  malloc _ _ := 0
  alloc _ _ := ()
  dealloc _ _ _ := ()

/-- **Rung 01 (`never`)**, through its reference model. -/
abbrev neverMF : AbsAlloc := AbsAlloc.ofRef neverRef ()

/-- Rung 02's reference model `Ladder.Bump.ref` (an x86 bump allocator's
rows are stated against it), with its state type `Nat` visible (`bumpRef_eq`: it is `Ladder.Bump.ref`). -/
abbrev bumpRef : RefModel where
  St := Nat
  malloc := Silmaril.Libc.X86Alloc.Ladder.Bump.ref.malloc
  alloc := Silmaril.Libc.X86Alloc.Ladder.Bump.ref.alloc
  dealloc := Silmaril.Libc.X86Alloc.Ladder.Bump.ref.dealloc

theorem bumpRef_eq : bumpRef = Silmaril.Libc.X86Alloc.Ladder.Bump.ref := rfl

/-- **Rung 02 (`bump`)**, through its reference model, from `used = 0`. -/
abbrev bump : AbsAlloc := AbsAlloc.ofRef bumpRef 0

/-- The bump allocator's invariant: `used ≤ 4096`, and every live block is a positive block
inside `[arena, arena + used)`. -/
def bumpInv (x : Nat × Heap) : Prop :=
  x.1 ≤ Silmaril.Libc.X86Alloc.Ladder.Bump.size ∧
    ∀ a m, x.2 a = some m → Silmaril.Libc.X86Alloc.Ladder.Bump.arena ≤ a ∧
      a + m ≤ Silmaril.Libc.X86Alloc.Ladder.Bump.arena + x.1 ∧ 0 < m

end Silmaril.Libc
