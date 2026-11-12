module

public import Silmaril.Logic.Institution.Morphism
public import Silmaril.Semantics.CPort.Logic.Institution.Bridges.Contracts.Defs
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Discrete.Basic

/-! # Calling conventions as institution comorphisms

An ABI relates a C-level interface institution to a machine-level one. Both are
instances of one *interface-contract institution* (`Logic.inst`):

* a signature (`Iface`) declares symbols, each with a descriptor (a C prototype,
  or a machine call descriptor); signature morphisms are inclusions of
  declarations, so the signature category is a preorder;
* a sentence names one declared symbol and gives a `Contracts.Contract` over the
  descriptor's inputs and observations;
* a model gives each declared symbol a `Contracts.Model`, i.e. a call relation;
* satisfaction is `Contracts.Sat`: every admitted input has an outcome, and every
  outcome meets the postcondition (total correctness for a relation).

The institution notions are the public Silmaril ones (`Inst`, `Inst.CoHom`, rooms
and corridors), pinned by `Silmaril.Semantics.CPort.Logic.Institution.*`. Contracts,
call relations and satisfaction are the imported contract bridge
`Silmaril.Logic.Institution.Bridges.Contracts`.

A `Translation` between two such logics, defined per descriptor, is lifted to an
institution comorphism (`Translation.coHom`). A `Convention` is one particular source
of translations: C prototypes are planned to machine descriptors (`desc`),
C contracts become machine Hoare contracts (`Convention.translate`), and machine call
relations are read back as C call relations (`Convention.reduce`) by quantifying over
*every* machine state that encodes the C arguments. The satisfaction condition
`Convention.sat_translate` therefore says: a machine implementation meets the
translated contract iff its ABI read-back meets the C contract. It needs only
that each argument tuple has at least one encoding (`Convention.inhabited`).

Execution relations are abstract here. Connecting them to an ISA's `Reaches`
relation, symbol addresses and memory footprints is a separate obligation.
-/

@[expose] public section
namespace Silmaril.Machine.Abi

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Bridges

/-- Symbols are linker-level names. -/
abbrev Symbol := String

/-- An interface: the descriptor of each declared symbol. -/
@[ext]
structure Iface (D : Type) where
  decl : Symbol → Option D

namespace Iface

variable {D E : Type}

/-- Inclusion of declarations; descriptors of shared symbols must agree. -/
instance : Preorder (Iface D) where
  le first second := ∀ f d, first.decl f = some d → second.decl f = some d
  le_refl _ _ _ h := h
  le_trans _ _ _ h g f d declared := g f d (h f d declared)

theorem le_def {first second : Iface D} :
    first ≤ second ↔ ∀ f d, first.decl f = some d → second.decl f = some d := Iff.rfl

/-- Translate each declaration by a descriptor map (the ABI's call planner). -/
def map (desc : D → E) (iface : Iface D) : Iface E := ⟨fun f => (iface.decl f).map desc⟩

theorem map_decl {desc : D → E} {iface : Iface D} {f : Symbol} {d : D}
    (declared : iface.decl f = some d) : (iface.map desc).decl f = some (desc d) := by
  simp [map, declared]

theorem map_mono (desc : D → E) : Monotone (map desc) := by
  intro first second le f e declared
  simp only [map, Option.map_eq_some_iff] at declared ⊢
  obtain ⟨d, hd, rfl⟩ := declared
  exact ⟨d, le f d hd, rfl⟩

/-- The signature functor of an ABI comorphism. -/
def mapFunctor (desc : D → E) : Iface D ⥤ Iface E := (map_mono desc).functor

end Iface

/-- A per-symbol contract logic: inputs and observations of each descriptor. -/
structure Logic where
  Desc : Type
  Input : Desc → Type
  Obs : Desc → Type

namespace Logic

variable (L : Logic)

/-- A contract about one declared symbol. -/
structure Sentence (iface : Iface L.Desc) where
  sym : Symbol
  desc : L.Desc
  declared : iface.decl sym = some desc
  contract : Contracts.Contract (L.Input desc) (L.Obs desc)

/-- A call relation for every declared symbol. -/
def Model (iface : Iface L.Desc) : Type :=
  ∀ f d, iface.decl f = some d → Contracts.Model (L.Input d) (L.Obs d)

variable {L}

def Sat {iface : Iface L.Desc} (model : L.Model iface) (sentence : L.Sentence iface) : Prop :=
  Contracts.Sat (model sentence.sym sentence.desc sentence.declared) sentence.contract

def Sentence.widen {small large : Iface L.Desc} (le : small ≤ large)
    (sentence : L.Sentence small) : L.Sentence large :=
  { sentence with declared := le _ _ sentence.declared }

def Model.restrict {small large : Iface L.Desc} (le : small ≤ large)
    (model : L.Model large) : L.Model small :=
  fun f d declared => model f d (le f d declared)

variable (L)

def room (iface : Iface L.Desc) : Room.{0, 0, 0} where
  Sen := L.Sentence iface
  Mod := Cat.of (Discrete (L.Model iface))
  Sat model sentence := Sat model.as sentence

/-- Extending an interface keeps sentences and restricts models. -/
def corridor {small large : Iface L.Desc} (le : small ≤ large) :
    L.room small ⟶ L.room large where
  sen := Sentence.widen le
  mod := Discrete.functor fun model => Discrete.mk (Model.restrict le model)
  sat _ _ := Iff.rfl

/-- The interface-contract institution of a logic, as a room functor. -/
def functor : Iface L.Desc ⥤ Room.{0, 0, 0} where
  obj := L.room
  map σ := L.corridor σ.le
  map_id _ := Room.hom_ext rfl (Functor.ext (fun _ => rfl) (fun _ _ _ => Discrete.hom_eq))
  map_comp _ _ := Room.hom_ext rfl (Functor.ext (fun _ => rfl) (fun _ _ _ => Discrete.hom_eq))

/-- The bundled institution. -/
def inst : Inst.{0, 0, 0, 0, 0} := ⟨Iface L.Desc, L.functor⟩

end Logic

/-- A descriptor-wise translation of contracts and reduction of call relations
whose satisfaction condition holds pointwise. -/
structure Translation (A B : Logic) where
  desc : A.Desc → B.Desc
  sen : ∀ d, Contracts.Contract (A.Input d) (A.Obs d) →
    Contracts.Contract (B.Input (desc d)) (B.Obs (desc d))
  red : ∀ d, Contracts.Model (B.Input (desc d)) (B.Obs (desc d)) →
    Contracts.Model (A.Input d) (A.Obs d)
  sat : ∀ d model contract,
    Contracts.Sat model (sen d contract) ↔ Contracts.Sat (red d model) contract

namespace Translation

variable {A B : Logic} (T : Translation A B)

def senAt (iface : Iface A.Desc) (sentence : A.Sentence iface) :
    B.Sentence (iface.map T.desc) :=
  ⟨sentence.sym, T.desc sentence.desc, Iface.map_decl sentence.declared,
    T.sen sentence.desc sentence.contract⟩

def modAt (iface : Iface A.Desc) (model : B.Model (iface.map T.desc)) : A.Model iface :=
  fun f d declared => T.red d (model f (T.desc d) (Iface.map_decl declared))

/-- The component corridor `I_C(Σ) → I_M(ΦΣ)`. -/
def corridor (iface : Iface A.Desc) :
    A.room iface ⟶ B.room (iface.map T.desc) where
  sen := T.senAt iface
  mod := Discrete.functor fun model => Discrete.mk (T.modAt iface model)
  sat _ sentence := T.sat sentence.desc _ sentence.contract

/-- The translation is natural in interface inclusions. -/
def rho : A.functor ⟶ Iface.mapFunctor T.desc ⋙ B.functor where
  app := T.corridor
  naturality _ _ _ := Room.hom_ext rfl
    (Functor.ext (fun _ => rfl) (fun _ _ _ => Discrete.hom_eq))

/-- The institution comorphism determined by a descriptor-wise translation. -/
def coHom : Inst.CoHom A.inst B.inst := ⟨Iface.mapFunctor T.desc, T.rho⟩

end Translation

/-- A C prototype vocabulary: argument tuples and result values of prototypes. -/
structure Vocab where
  Proto : Type
  Args : Proto → Type
  Ret : Proto → Type

/-- C observations: `some r` is an ABI-conforming return of `r`; `none` is a
return that breaks the ABI's return discipline or has no decodable result. -/
def Vocab.logic (V : Vocab) : Logic := ⟨V.Proto, V.Args, fun p => Option (V.Ret p)⟩

/-- Machine logic over states `St`: inputs are entry states, observations final states. -/
def machineLogic (St D : Type) : Logic := ⟨D, fun _ => St, fun _ => St⟩

/-- Named calling conventions and profiles. The tag is metadata for linkers; the
semantic content is the `Convention` that carries it. -/
inductive Tag where
  /-- AMD64 System V LP64; `vectors` is 0 (SSE), 1 (AVX), 2 (AVX-512). -/
  | sysv (vectors : Nat) (redZone : Bool)
  | sysvX32
  | win64
  | other (name : String)
  deriving DecidableEq, Repr

/-- A calling convention for C prototypes `V` over machine states `St`, with
machine call descriptors `D`. -/
structure Convention (V : Vocab) (St D : Type) where
  tag : Tag
  /-- Classification and call planning. -/
  desc : V.Proto → D
  /-- `Entry p a s`: entry state `s` places arguments `a` as `p` requires. -/
  Entry : (p : V.Proto) → V.Args p → St → Prop
  /-- Control, stack and preserved-state obligations of a return. -/
  Return : V.Proto → St → St → Prop
  /-- `ResultAt p s s' r`: final state `s'` (entered at `s`) returns `r`. -/
  ResultAt : (p : V.Proto) → St → St → V.Ret p → Prop
  /-- Every argument tuple has an encoding. -/
  inhabited : ∀ p a, ∃ s, Entry p a s

namespace Convention

variable {V : Vocab} {St D : Type} (A : Convention V St D)

/-- What a C caller observes of a machine return. -/
def Observe (p : V.Proto) (s s' : St) : Option (V.Ret p) → Prop
  | some r => A.Return p s s' ∧ A.ResultAt p s s' r
  | none => ¬ (A.Return p s s' ∧ ∃ r, A.ResultAt p s s' r)

theorem observe_total (p : V.Proto) (s s' : St) : ∃ o, A.Observe p s s' o := by
  by_cases h : A.Return p s s' ∧ ∃ r, A.ResultAt p s s' r
  · obtain ⟨ret, r, at_⟩ := h
    exact ⟨some r, ret, at_⟩
  · exact ⟨none, h⟩

/-- Sentence translation: the machine Hoare contract of a C contract. -/
def translate (p : V.Proto) (c : Contracts.Contract (V.Args p) (Option (V.Ret p))) :
    Contracts.Contract St St where
  pre s := ∃ a, A.Entry p a s ∧ c.pre a
  post s s' := ∀ a, A.Entry p a s → c.pre a → ∀ o, A.Observe p s s' o → c.post a o

/-- Model reduction: the demonic read-back over every encoding of the arguments.
An argument tuple has outcomes only if every encoding of it has a successor. -/
def reduce (p : V.Proto) (model : Contracts.Model St St) :
    Contracts.Model (V.Args p) (Option (V.Ret p)) :=
  fun a => {o | (∀ s, A.Entry p a s → (model s).Nonempty) ∧
    ∃ s, A.Entry p a s ∧ ∃ s' ∈ model s, A.Observe p s s' o}

/-- The satisfaction condition: ABI correctness of a machine implementation is
C-level correctness of its read-back. -/
theorem sat_translate (p : V.Proto) (model : Contracts.Model St St)
    (c : Contracts.Contract (V.Args p) (Option (V.Ret p))) :
    Contracts.Sat model (A.translate p c) ↔ Contracts.Sat (A.reduce p model) c := by
  constructor
  · intro machine a pre
    have progress : ∀ s, A.Entry p a s → (model s).Nonempty :=
      fun s entry => (machine s ⟨a, entry, pre⟩).1
    refine ⟨?_, ?_⟩
    · obtain ⟨s, entry⟩ := A.inhabited p a
      obtain ⟨s', step⟩ := progress s entry
      obtain ⟨o, observed⟩ := A.observe_total p s s'
      exact ⟨o, progress, s, entry, s', step, observed⟩
    · rintro o ⟨-, s, entry, s', step, observed⟩
      exact (machine s ⟨a, entry, pre⟩).2 s' step a entry pre o observed
  · rintro source s ⟨a, entry, pre⟩
    obtain ⟨⟨o, progress, -⟩, -⟩ := source a pre
    refine ⟨progress s entry, ?_⟩
    intro s' step a' entry' pre' o' observed
    obtain ⟨⟨_, progress', -⟩, post⟩ := source a' pre'
    exact post o' ⟨progress', s, entry', s', step, observed⟩

/-- The descriptor-wise translation of an ABI. -/
def translation : Translation V.logic (machineLogic St D) where
  desc := A.desc
  sen := A.translate
  red := A.reduce
  sat := A.sat_translate

/-- The ABI as an institution comorphism from C interfaces to machine interfaces. -/
def coHom : Inst.CoHom V.logic.inst (machineLogic St D).inst := A.translation.coHom

/-- Two conventions agree on a prototype when they place arguments and observe
returns identically. This is the semantic link-compatibility condition. -/
def Agree (B : Convention V St D) (p : V.Proto) : Prop :=
  (∀ a s, A.Entry p a s ↔ B.Entry p a s) ∧
    ∀ s s' o, A.Observe p s s' o ↔ B.Observe p s s' o

/-- A thunk adapts a caller using `A` to a callee using `B`: `enter` runs from the
caller's entry state to the callee's entry, `leave` from the callee's return to
the caller's return. Both are execution relations of the thunk code. -/
structure Thunk {V : Vocab} {St D : Type} (A B : Convention V St D) (p : V.Proto) where
  enter : St → Set St
  leave : St → St → Set St

/-- The machine relation of the callee reached through the thunk. -/
def Thunk.wrap {A B : Convention V St D} {p : V.Proto} (t : Thunk A B p)
    (model : Contracts.Model St St) : Contracts.Model St St :=
  fun s => {s₃ | ∃ s₁ ∈ t.enter s, ∃ s₂ ∈ model s₁, s₃ ∈ t.leave s s₂}

/-- Thunk correctness: it re-encodes the arguments, always progresses, and the
caller's observation of the adapted return is one the callee produced. -/
structure Thunk.Correct {A B : Convention V St D} {p : V.Proto} (t : Thunk A B p) : Prop where
  enter_entry : ∀ a s, A.Entry p a s → ∀ s₁ ∈ t.enter s, B.Entry p a s₁
  enter_progress : ∀ a s, A.Entry p a s → (t.enter s).Nonempty
  leave_progress : ∀ a s, A.Entry p a s → ∀ s₂, (t.leave s s₂).Nonempty
  observe : ∀ a s, A.Entry p a s → ∀ s₁ ∈ t.enter s, ∀ s₂ s₃, s₃ ∈ t.leave s s₂ →
    ∀ o, A.Observe p s s₃ o → B.Observe p s₁ s₂ o

end Convention

end Silmaril.Machine.Abi
