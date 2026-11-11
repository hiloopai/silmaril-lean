module

public import Silmaril.Cli.Behaviour.Defs
public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.EqToHom

/-!
# The CLI institution: interfaces, specifications as sentences, programs as models

A command-line program is seen through an **interface** (`Sig`): what it is given (`In`) and
what can be seen of a terminating run (`Out`). A **sentence** of an interface is a
specification `In → Out → Prop` (`Sen`, the observations allowed per input; at the full
interface exactly `Silmaril.Cli.Spec`), a **model** is a program semantics `Run : In → Out → Prop`
(`Model`: the observations of its terminating runs, possibly nondeterministic), and
**satisfaction** is partial correctness: every run on `i` satisfies the spec at `i`
(`Model.Sat M φ`, which is refinement `M.Run ≤ φ`).

## Morphisms

A morphism `h : A ⟶ B` (`Hom`) says how `B` refines `A`'s view:

* `h.inp a b`: the input `b` of `B` stands for the input `a` of `A` (a relation: a default
  expansion `b = e a`, or every extension `p b = a`);
* `h.out : B.Out → A.Out`: what `A` sees of an observation of `B` (a projection).

Sentences translate forwards (`Hom.sen`: on `b`, for every `a` it stands for, the projected
observation is allowed), models backwards (`Hom.mod`: the reduct, runs on the inputs that stand
for `a`, projected). The satisfaction condition `M ⊨ h.sen φ ↔ h.mod M ⊨ φ` holds for every
morphism (`Hom.sat_sen_iff`), and the interfaces with these morphisms form a category, so this is
an institution (`inst : Sig ⥤ Room`, `classic`).

## Observation levels

The standard interfaces form a chain (`Level`, ordered by `Level.rank`):

| level | input (`Level.In`) | observation (`Level.Out`) |
|---|---|---|
| `L0` (`status`) | nothing (`Unit`) | the exit code |
| `L1` (`stream`) | stdin | stdout and exit code (`Out1`) |
| `L2` (`command`) | program name, arguments, stdin (`In2`) | stdout, stderr, exit code (`Spec.Out`) |
| `L3` (`full`) | `Silmaril.Cli.Input` (+ environment, roots, files) | `Silmaril.Cli.Obs` (+ consumption, reads, files, refusals, file log) |

Each level embeds into the full invocation with default values for what it does not see
(`Level.embed`: no arguments, program name `"prog"`, empty environment, no roots, no files) and
projects the full observation (`Level.outProj`). The morphism `Level.hom L L'` reads an input of
`L` as its default expansion at `L'` and projects observations; `Level.homAll L L'` reads it as
**every** extension (a uniform claim: e.g. an `L1` filter that ignores its arguments). A
refusal-aware level is `L3` itself: `Obs.refused` is observed there, and `Spec.orRefused` is the
usual allowance.

So a hello-world claim lives at `L1` (`stdout = "hello\n"`, exit `0`), a stdin filter such as
`sha256sum < f` at `L1`, `sha256sum FILE` at `L3`; `(Level.hom L1 L3).sen φ` is the `L1` claim
as a full `Silmaril.Cli.Spec`, and a model satisfies it iff its `L1` reduct satisfies `φ`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Institution

open CategoryTheory Silmaril.Logic.Institution

/-! ## Interfaces, sentences, models -/

/-- **An interface** (a signature of the institution): the inputs of a CLI program and the
observations of its terminating runs. -/
structure Sig : Type 1 where
  /-- What the program is given. -/
  In : Type
  /-- What can be seen of a terminating run. -/
  Out : Type

/-- **A sentence**: a specification, the observations allowed for each input. Refinement
(entailment between single sentences) is `≤`. -/
abbrev Sen (A : Sig) : Type := A.In → A.Out → Prop

/-- **A model**: a CLI program semantics, the observations of its terminating runs on each input
(nondeterministic, partial correctness: nonterminating runs are not observations). -/
@[ext] structure Model (A : Sig) : Type where
  /-- `Run i o`: some terminating run on `i` is observed as `o`. -/
  Run : A.In → A.Out → Prop

instance (A : Sig) : PartialOrder (Model A) :=
  PartialOrder.lift Model.Run fun _ _ h => Model.ext h

/-- **Satisfaction** (partial correctness): every observation of a run on `i` is allowed by `φ`
at `i`. -/
def Model.Sat {A : Sig} (M : Model A) (φ : Sen A) : Prop := ∀ i o, M.Run i o → φ i o

/-- **A morphism of interfaces** `A ⟶ B`: which inputs of `B` stand for an input of `A`, and
what `A` sees of an observation of `B`. -/
@[ext] structure Hom (A B : Sig) : Type where
  /-- `inp a b`: the input `b` of `B` stands for the input `a` of `A`. -/
  inp : A.In → B.In → Prop
  /-- What `A` sees of an observation of `B`. -/
  out : B.Out → A.Out

namespace Hom

variable {A B C : Sig}

/-- The identity: an input stands for itself, the observation is kept. -/
def id (A : Sig) : Hom A A := ⟨Eq, _root_.id⟩

/-- Composition: relational on inputs, functional (backwards) on observations. -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨fun a c => ∃ b, f.inp a b ∧ g.inp b c, f.out ∘ g.out⟩

/-- **Sentence translation**: on an input `b`, for every input `a` it stands for, `φ` allows
the projected observation. -/
def sen (h : Hom A B) (φ : Sen A) : Sen B := fun b o => ∀ a, h.inp a b → φ a (h.out o)

/-- **The reduct of a model**: its runs on the inputs that stand for `a`, projected. -/
def mod (h : Hom A B) (M : Model B) : Model A :=
  ⟨fun a o => ∃ b o', h.inp a b ∧ M.Run b o' ∧ h.out o' = o⟩

/-- **The satisfaction condition.** -/
theorem sat_sen_iff (h : Hom A B) (M : Model B) (φ : Sen A) :
    M.Sat (h.sen φ) ↔ (h.mod M).Sat φ := by
  constructor
  · rintro H a _ ⟨b, o', hab, hr, rfl⟩
    exact H b o' hr a hab
  · intro H b o hr a hab
    exact H a _ ⟨b, o, hab, hr, rfl⟩

theorem mod_mono (h : Hom A B) {M N : Model B} (hMN : M ≤ N) : h.mod M ≤ h.mod N := by
  rintro a o ⟨b, o', hab, hr, he⟩
  exact ⟨b, o', hab, hMN b o' hr, he⟩

theorem sen_mono (h : Hom A B) {φ ψ : Sen A} (hφ : φ ≤ ψ) : h.sen φ ≤ h.sen ψ :=
  fun _ _ H a hab => hφ a _ (H a hab)

end Hom

instance : Category Sig where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext
    · funext a c; apply propext
      exact ⟨fun ⟨_, h, h'⟩ => h ▸ h', fun h => ⟨a, rfl, h⟩⟩
    · rfl
  comp_id f := by
    apply Hom.ext
    · funext a c; apply propext
      exact ⟨fun ⟨_, h, h'⟩ => h' ▸ h, fun h => ⟨c, h, rfl⟩⟩
    · rfl
  assoc f g k := by
    apply Hom.ext
    · funext a d; apply propext
      exact ⟨fun ⟨c, ⟨b, h1, h2⟩, h3⟩ => ⟨b, h1, c, h2, h3⟩,
        fun ⟨b, h1, c, h2, h3⟩ => ⟨c, ⟨b, h1, h2⟩, h3⟩⟩
    · rfl

/-! ## The institution -/

/-- The room of an interface: its sentences, its models (ordered by inclusion of runs), and
satisfaction. -/
def room (A : Sig) : Room.{0, 0, 0} := ⟨Sen A, Cat.of (Model A), fun M φ => M.Sat φ⟩

/-- The corridor of a morphism: sentence translation, model reduct, the satisfaction
condition. -/
def corridor {A B : Sig} (h : A ⟶ B) : room A ⟶ room B :=
  ⟨Hom.sen h, (Monotone.functor (f := Hom.mod h) fun _ _ hMN => Hom.mod_mono h hMN :
    Model B ⥤ Model A), fun M φ => Hom.sat_sen_iff h M φ⟩

theorem Hom.sen_id (A : Sig) : Hom.sen (𝟙 A) = _root_.id := by
  funext φ b o; apply propext
  exact ⟨fun H => H b rfl, fun H a hab => hab ▸ H⟩

theorem Hom.sen_comp {A B C : Sig} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.sen (f ≫ g) = Hom.sen g ∘ Hom.sen f := by
  funext φ c o; apply propext
  exact ⟨fun H b hbc a hab => H a ⟨b, hab, hbc⟩, fun H a ⟨b, hab, hbc⟩ => H b hbc a hab⟩

theorem Hom.mod_id (A : Sig) (M : Model A) : Hom.mod (𝟙 A) M = M := by
  apply Model.ext; funext a o; apply propext
  exact ⟨fun ⟨_, _, hab, hr, he⟩ => hab ▸ he ▸ hr, fun hr => ⟨a, o, rfl, hr, rfl⟩⟩

theorem Hom.mod_comp {A B C : Sig} (f : A ⟶ B) (g : B ⟶ C) (M : Model C) :
    Hom.mod (f ≫ g) M = Hom.mod f (Hom.mod g M) := by
  apply Model.ext; funext a o; apply propext
  constructor
  · rintro ⟨c, o', ⟨b, hab, hbc⟩, hr, rfl⟩
    exact ⟨b, g.out o', hab, ⟨c, o', hbc, hr, rfl⟩, rfl⟩
  · rintro ⟨b, _, hab, ⟨c, o', hbc, hr, rfl⟩, rfl⟩
    exact ⟨c, o', ⟨b, hab, hbc⟩, hr, rfl⟩

/-- **The CLI institution**, as a functor into rooms. -/
def inst : Sig ⥤ Room.{0, 0, 0} where
  obj := room
  map h := corridor h
  map_id A := Room.hom_ext (Hom.sen_id A)
    (CategoryTheory.Functor.ext (fun M => Hom.mod_id A M) (fun _ _ _ => rfl))
  map_comp f g := Room.hom_ext (Hom.sen_comp f g)
    (CategoryTheory.Functor.ext (fun M => Hom.mod_comp f g M) (fun _ _ _ => rfl))

/-- The institution in the classic presentation. -/
def classic : ClassicInstitution.{1, 0, 0, 0, 0} Sig := ClassicInstitution.ofRoomFunctor inst

/-! ## Observation levels -/

/-- **The standard observation levels**, coarsest first. -/
inductive Level where
  /-- `L0`: the exit code of a run given nothing. -/
  | status
  /-- `L1`: stdin to stdout and exit code. -/
  | stream
  /-- `L2`: program name, arguments and stdin to stdout, stderr and exit code. -/
  | command
  /-- `L3`: the full `Silmaril.Cli.Input` and `Silmaril.Cli.Obs`. -/
  | full
deriving DecidableEq, Repr, Inhabited

namespace Level

@[inherit_doc] scoped notation "L0" => Level.status
@[inherit_doc] scoped notation "L1" => Level.stream
@[inherit_doc] scoped notation "L2" => Level.command
@[inherit_doc] scoped notation "L3" => Level.full

/-- The position of a level in the chain. -/
def rank : Level → Nat
  | .status => 0 | .stream => 1 | .command => 2 | .full => 3

theorem rank_injective : Function.Injective rank := by
  intro a b h; cases a <;> cases b <;> first | rfl | (simp [rank] at h)

instance : LinearOrder Level := LinearOrder.lift' rank rank_injective

theorem le_iff_rank {a b : Level} : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl

end Level

/-- The observation of `L1`: stdout and the exit code. -/
structure Out1 where
  /-- Stdout. -/
  stdout : Bytes := []
  /-- The exit code. -/
  exit : ExitCode := 0

/-- The input of `L2`: program name, arguments, stdin. -/
structure In2 where
  /-- The program name (`argv[0]`). -/
  prog : String := "prog"
  /-- The arguments, without the program name. -/
  args : List String := []
  /-- Standard input. -/
  stdin : Bytes := []

namespace Level

/-- The inputs of a level. -/
@[reducible] def In : Level → Type
  | .status => Unit
  | .stream => Bytes
  | .command => In2
  | .full => Input

/-- The observations of a level. -/
@[reducible] def Out : Level → Type
  | .status => ExitCode
  | .stream => Out1
  | .command => Spec.Out
  | .full => Obs

/-- **The interface of a level.** -/
abbrev sig (L : Level) : Sig := ⟨L.In, L.Out⟩

/-- The default expansion of an input of the level to a full invocation. -/
def embed : (L : Level) → L.In → Input
  | .status, _ => {}
  | .stream, s => { stdin := s }
  | .command, i => { prog := i.prog, args := i.args, stdin := i.stdin }
  | .full, i => i

/-- What the level sees of a full invocation. -/
def inProj : (L : Level) → Input → L.In
  | .status, _ => ()
  | .stream, i => i.stdin
  | .command, i => { prog := i.prog, args := i.args, stdin := i.stdin }
  | .full, i => i

/-- What the level sees of a full observation. -/
def outProj : (L : Level) → Obs → L.Out
  | .status, o => o.exit
  | .stream, o => { stdout := o.stdout, exit := o.exit }
  | .command, o => { stdout := o.stdout, stderr := o.stderr, exit := o.exit }
  | .full, o => o

/-- The default full observation with what the level sees (no file, nothing consumed). -/
def outEmbed : (L : Level) → L.Out → Obs
  | .status, c => { exit := c, fs := Fs.empty }
  | .stream, o => { stdout := o.stdout, exit := o.exit, fs := Fs.empty }
  | .command, o => { stdout := o.stdout, stderr := o.stderr, exit := o.exit, fs := Fs.empty }
  | .full, o => o

/-- **The level morphism by default expansion**: an input of `L` stands for its default
expansion at `L'`; `L` sees its part of an observation of `L'`. A functor on `L ≤ L'`
(`Thms`). -/
def hom (L L' : Level) : L.sig ⟶ L'.sig :=
  ⟨fun a b => b = L'.inProj (L.embed a), fun o => L.outProj (L'.outEmbed o)⟩

/-- **The uniform level morphism**: an input of `L` stands for every input of `L'` that
extends it (`L` sees it). A sentence translated along it holds whatever `L'` adds. -/
def homAll (L L' : Level) : L.sig ⟶ L'.sig :=
  ⟨fun a b => L.inProj (L'.embed b) = a, fun o => L.outProj (L'.outEmbed o)⟩

/-- A sentence of `L` as a full `Silmaril.Cli.Spec` (default expansion). -/
def lift {L : Level} (φ : Sen L.sig) : Spec := (hom L .full).sen φ

/-- A sentence of `L` as a full `Silmaril.Cli.Spec` that holds on every extension of the input. -/
def liftAll {L : Level} (φ : Sen L.sig) : Spec := (homAll L .full).sen φ

/-- The level-`L` reduct of a full model (default expansion). -/
def reduct (L : Level) (M : Model Level.full.sig) : Model L.sig := (hom L .full).mod M

end Level

/-! ## Standard sentences -/

namespace Sen

open Level

/-- `L0`: the run exits with `c`. -/
def exits (c : ExitCode) : Sen Level.status.sig :=
  fun (_ : Unit) (o : ExitCode) => o = c

/-- `L1`: **a stream filter**: stdout is `f stdin`, exit `0`. -/
def filter (f : Bytes → Bytes) : Sen Level.stream.sig :=
  fun (s : Bytes) (o : Out1) => o.stdout = f s ∧ o.exit = 0

/-- `L1`: **prints `out` and succeeds**, whatever stdin holds (hello world). -/
def prints (out : Bytes) : Sen Level.stream.sig := filter fun _ => out

/-- `L2`: **a command**: the observation is `f` of the invocation. -/
def command (f : In2 → Spec.Out) : Sen Level.command.sig :=
  fun (i : In2) (o : Spec.Out) =>
  o.stdout = (f i).stdout ∧ o.stderr = (f i).stderr ∧ o.exit = (f i).exit

/-- `L1`: **a judged problem** (leetcode style, stdin to stdout): stdout is an answer `ok`
accepts for the input on stdin, exit `0`. -/
def judge (ok : Bytes → Bytes → Prop) : Sen Level.stream.sig :=
  fun (s : Bytes) (o : Out1) => ok s o.stdout ∧ o.exit = 0

end Sen

end Silmaril.Cli.Institution
