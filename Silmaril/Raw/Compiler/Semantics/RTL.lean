module

public import Silmaril.Compiler.Semantics.RTLRename.Defs
public import Silmaril.Compiler.Mir.SSA.Defs
public import Silmaril.Machine.CBackend.RTL.ToLir.Defs
public import Silmaril.Machine.CBackend.RTL.Construct.Defs
public import Silmaril.Machine.CBackend.RTL.Sequentialize.Defs
public import Silmaril.Machine.CBackend.Lift.Ssa.Defs
public import Mathlib.Data.Nat.Pairing

@[expose] public section

/-!
# RTL and RTL.SSA as languages of the zoo

`rtlLang` and `ssaLang` are the closed programs of `Machine.RTL` and `Machine.RTL.SSA` (a
function table, the entry function, its arguments and the initial memory) observed through
the same `Mir.LirOutcome`s as `Mir.lang` and `Mir.lirLang`: the returned values and final
memory, the trap and its memory, divergence, or undefined. As in Mir, a run that gets stuck
allows every outcome (`Mir.ubClose`), and a program that does not start has none.

Every pass of the RTL family changes the register type (the maximal SSA construction lands
in `Name R`, sequentialization in `R ⊕ Nat`), so a program of the zoo carries its register
type, as a code `RegTy` closed under both. `RegTy.enc` encodes every register type
injectively into `Nat`, the register type of the zoo's Lir programs.

The passes, each at the identity of observations and each sound by an existing simulation
theorem of `Machine/RTL` or `Machine/Lift`, plus `Machine.RTL.behaves_rename_iff`:

| pass | from → to | soundness |
| --- | --- | --- |
| `normalize` | `rtlLang` (endo) | `behaves_rename_iff` |
| `lowerLir` | `rtlLang → Mir.lirLang` | `toLir_behaves_iff` |
| `construct` | `rtlLang → ssaLang` | `construct_behaves` (maximal SSA) |
| `erase` | `ssaLang → rtlLang` | `Lift.erase_behaves` |
| `sequentialize` | `ssaLang` (endo) | `sequentializeProg_behaves` |

`roundTrip : RoundTrip rtlLang ssaLang` is `construct` and `erase`, so every SSA optimization
`E : EndoPass ssaLang` conjugates to an RTL optimization, and `optimizeAndLower_sound` is the
end-to-end theorem of RTL → RTL.SSA → (E) → RTL → Lir for **every** `E`, from the parts alone.
`sequentialize` is a real SSA optimization: run before `erase`, it makes every transfer
sequential, which `erase` checks.
-/

namespace Silmaril.Compile.Semantics

open Silmaril.Machine
open Silmaril.Compile.Category
open Silmaril.Compile.Mir (LirOutcome ubClose lirLang ubClose_mono ubClose_of_undefined)
open CategoryTheory

/-! ## Register types -/

/-- Codes of register types: `Nat`, closed under the maximal SSA construction's names and
under sequentialization's fresh parameters. -/
inductive RegTy where
  | nat
  | name (t : RegTy)
  | sum (t : RegTy)
  deriving DecidableEq, Repr

/-- The register type of a code. -/
@[reducible] def RegTy.denote : RegTy → Type
  | .nat => Nat
  | .name t => RTL.Name t.denote
  | .sum t => t.denote ⊕ Nat

instance RegTy.decEq : (t : RegTy) → DecidableEq t.denote
  | .nat => inferInstanceAs (DecidableEq Nat)
  | .name t =>
    letI := RegTy.decEq t
    inferInstanceAs (DecidableEq (RTL.Name t.denote))
  | .sum t =>
    letI := RegTy.decEq t
    inferInstanceAs (DecidableEq (t.denote ⊕ Nat))

/-- Encode the names of the maximal SSA construction, given an encoding of `R`. -/
def nameEnc {R : Type} (e : R → Nat) : RTL.Name R → Nat
  | .arg r => 4 * e r
  | .init r => 4 * e r + 1
  | .param n r => 4 * Nat.pair n (e r) + 2
  | .result n r => 4 * Nat.pair n (e r) + 3

theorem nameEnc_injective {R : Type} {e : R → Nat} (he : Function.Injective e) :
    Function.Injective (nameEnc e) := by
  have hp : ∀ {n n' : Nat} {r r' : R}, Nat.pair n (e r) = Nat.pair n' (e r') → n = n' ∧ r = r' :=
    fun h => ⟨(Nat.pair_eq_pair.mp h).1, he (Nat.pair_eq_pair.mp h).2⟩
  intro x y h
  rcases x with r | r | ⟨n, r⟩ | ⟨n, r⟩ <;> rcases y with r' | r' | ⟨n', r'⟩ | ⟨n', r'⟩ <;>
    simp only [nameEnc] at h
  all_goals first
    | omega
    | (obtain rfl := he (by omega : e r = e r'); rfl)
    | (obtain ⟨rfl, rfl⟩ := hp (by omega : Nat.pair n (e r) = Nat.pair n' (e r')); rfl)

/-- An injective encoding of every register type into `Nat`. -/
def RegTy.enc : (t : RegTy) → t.denote → Nat
  | .nat => id
  | .name t => nameEnc t.enc
  | .sum t => Sum.elim (fun r => 2 * t.enc r) (fun n => 2 * n + 1)

theorem RegTy.enc_injective : (t : RegTy) → Function.Injective t.enc
  | .nat => Function.injective_id
  | .name t => nameEnc_injective t.enc_injective
  | .sum t => by
    have ih := t.enc_injective
    rintro (x | x) (y | y) h <;> simp only [RegTy.enc, Sum.elim_inl, Sum.elim_inr] at h
    · rw [ih (by omega : t.enc x = t.enc y)]
    · omega
    · omega
    · rw [show x = y by omega]

/-! ## Observations -/

/-- The observation of an RTL behaviour. -/
def obsRtl : RTL.Behavior → LirOutcome
  | .returned vs m => .returned (vs, m)
  | .trapped m => .trapped m
  | .stuck => .undefined
  | .diverges => .diverges

/-- The observation of an RTL.SSA behaviour. -/
def obsSsa (b : RTL.SSA.Behavior) : LirOutcome := obsRtl (Lift.behaviorOfSsa b)

theorem obsRtl_eq_undefined {b : RTL.Behavior} : obsRtl b = .undefined ↔ b = .stuck := by
  cases b <;> simp [obsRtl]

theorem behaviorOfSsa_surjective : Function.Surjective Lift.behaviorOfSsa := by
  intro b
  cases b
  exacts [⟨.returned _ _, rfl⟩, ⟨.trapped _, rfl⟩, ⟨.stuck, rfl⟩, ⟨.diverges, rfl⟩]

theorem behaviorOfSsa_toSSA (b : RTL.Behavior) : Lift.behaviorOfSsa b.toSSA = b := by
  cases b <;> rfl

theorem toLirBehavior_surjective : Function.Surjective RTL.toLirBehavior := by
  intro b
  cases b
  exacts [⟨.returned _ _, rfl⟩, ⟨.trapped _, rfl⟩, ⟨.stuck, rfl⟩, ⟨.diverges, rfl⟩]

theorem toOutcome_toLirBehavior (b : RTL.Behavior) :
    (RTL.toLirBehavior b).toOutcome = obsRtl b := by
  cases b <;> rfl

/-! ## The languages -/

/-- A closed RTL program: a function table over some register type, the entry function, its
arguments and the initial memory. -/
structure RtlProg where
  ty : RegTy
  prog : RTL.Prog ty.denote
  entry : RTL.FuncId
  args : List Lir.Word
  mem : Lir.Memory

/-- A closed RTL.SSA program. -/
structure SsaProg where
  ty : RegTy
  prog : RTL.SSA.Prog ty.denote
  entry : RTL.FuncId
  args : List Lir.Word
  mem : Lir.Memory

/-- The observations of an RTL run from `s`. -/
def rtlObs {R : Type} [DecidableEq R] (p : RTL.Prog R) (s : RTL.State R) : Set LirOutcome :=
  {o | ∃ b, RTL.Behaves p s b ∧ obsRtl b = o}

/-- The observations of an RTL.SSA run from `s`. -/
def ssaObs {R : Type} [DecidableEq R] (p : RTL.SSA.Prog R) (s : RTL.SSA.State R) :
    Set LirOutcome :=
  {o | ∃ b, RTL.SSA.Behaves p s b ∧ obsSsa b = o}

/-- The behaviours of a closed RTL program, closed under undefined behaviour; none if it does
not start. -/
def RtlProg.beh (q : RtlProg) : Set LirOutcome :=
  match q.prog.start q.entry q.args q.mem with
  | some s => ubClose (rtlObs q.prog s)
  | none => ∅

/-- The behaviours of a closed RTL.SSA program. -/
def SsaProg.beh (q : SsaProg) : Set LirOutcome :=
  match q.prog.start q.entry q.args q.mem with
  | some s => ubClose (ssaObs q.prog s)
  | none => ∅

/-- RTL as a language of the zoo. -/
def rtlLang : Language.{0} := ⟨PUnit, RtlProg, fun _ => ⟨⟩, LirOutcome, RtlProg.beh⟩

/-- RTL.SSA as a language of the zoo. -/
def ssaLang : Language.{0} := ⟨PUnit, SsaProg, fun _ => ⟨⟩, LirOutcome, SsaProg.beh⟩

/-! ## The behaviour inclusions behind every pass -/

theorem undefined_mem_rtlObs {R : Type} [DecidableEq R] {p : RTL.Prog R} {s : RTL.State R} :
    .undefined ∈ rtlObs p s ↔ RTL.Behaves p s .stuck := by
  refine ⟨fun ⟨b, hb, he⟩ => obsRtl_eq_undefined.mp he ▸ hb, fun h => ⟨_, h, rfl⟩⟩

/-- The behaviours of a closed RTL program starting at `s`. -/
theorem RtlProg.beh_of_start {q : RtlProg} {s : RTL.State q.ty.denote}
    (h : q.prog.start q.entry q.args q.mem = some s) : q.beh = ubClose (rtlObs q.prog s) := by
  simp [RtlProg.beh, h]

theorem SsaProg.beh_of_start {q : SsaProg} {s : RTL.SSA.State q.ty.denote}
    (h : q.prog.start q.entry q.args q.mem = some s) : q.beh = ubClose (ssaObs q.prog s) := by
  simp [SsaProg.beh, h]

/-! ## Renaming into `Nat` and lowering to Lir -/

/-- The same program with its registers encoded into `Nat`. -/
def RtlProg.normalize (q : RtlProg) : RtlProg :=
  ⟨.nat, q.prog.rename q.ty.enc, q.entry, q.args, q.mem⟩

theorem RtlProg.beh_normalize (q : RtlProg) : q.normalize.beh = q.beh := by
  unfold RtlProg.beh RtlProg.normalize
  simp only
  rw [RTL.Prog.start_rename q.ty.enc_injective]
  cases q.prog.start q.entry q.args q.mem with
  | none => rfl
  | some s =>
    simp only [Option.map_some]
    congr 1
    ext o
    exact exists_congr fun b => and_congr (RTL.behaves_rename_iff q.ty.enc_injective) Iff.rfl

/-- The closed Lir program of a closed RTL program: its registers encoded into `Nat`, then
`RTL.toLir`, one Lir block per node. -/
def RtlProg.toLir (q : RtlProg) : Mir.LirProgram :=
  ⟨RTL.toLir (q.prog.rename q.ty.enc), q.entry, q.args, q.mem⟩

/-- **Lowering to Lir refines**: from `RTL.toLir_behaves_iff` on a run that does not get
stuck, and from `ubClose` on one that does. -/
theorem lirBeh_toLir_subset (p : RTL.Prog Nat) (f : RTL.FuncId) (args : List Lir.Word)
    (mem : Lir.Memory) :
    Mir.LirProgram.beh ⟨RTL.toLir p, f, args, mem⟩ ⊆ RtlProg.beh ⟨.nat, p, f, args, mem⟩ := by
  intro o ho
  unfold Mir.LirProgram.beh at ho
  unfold RtlProg.beh
  simp only at ho ⊢
  cases hs : p.start f args mem with
  | none =>
    have : (RTL.toLir p).start f args mem = none := by
      unfold Lir.Prog.start
      rw [RTL.toLir_enter]
      unfold RTL.Prog.start at hs
      cases he : p.enter f args <;> simp_all
    simp only [this] at ho
    exact (ho : False).elim
  | some s =>
    rw [RTL.toLir_start hs] at ho
    simp only
    by_cases hst : RTL.Behaves p s .stuck
    · exact Or.inr (undefined_mem_rtlObs.mpr hst)
    · refine ubClose_mono ?_ ho
      intro o' ho'
      obtain ⟨b', rfl, hb'⟩ := Lir.beh_iff.mp ho'
      obtain ⟨b, rfl⟩ := toLirBehavior_surjective b'
      exact ⟨b, (RTL.toLir_behaves_iff hst).mp hb', (toOutcome_toLirBehavior b).symm⟩

theorem RtlProg.beh_toLir_subset (q : RtlProg) : q.toLir.beh ⊆ q.beh := by
  rw [← q.beh_normalize]
  exact lirBeh_toLir_subset _ _ _ _

/-! ## Construction, erasure, sequentialization -/

/-- The side conditions of the maximal SSA construction, and a start state. -/
def RtlProg.Constructible (q : RtlProg) : Prop :=
  q.prog.WellFormedSig ∧ q.prog.Constructible ∧ (q.prog.start q.entry q.args q.mem).isSome

instance (q : RtlProg) : Decidable q.Constructible := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The maximal SSA construction of a closed RTL program. -/
def RtlProg.construct (q : RtlProg) : SsaProg :=
  ⟨.name q.ty, RTL.constructProg q.prog, q.entry, q.args, q.mem⟩

/-- The maximal SSA construction, when its side conditions hold. -/
def RtlProg.construct? (q : RtlProg) : Option SsaProg :=
  if q.Constructible then some q.construct else none

/-- **The maximal SSA construction refines**: from `RTL.construct_behaves` on a run that does
not get stuck (where the construction, which zeroes unwritten registers, is more defined). -/
theorem RtlProg.beh_construct {q : RtlProg} (h : q.Constructible) : q.construct.beh ⊆ q.beh := by
  obtain ⟨hsig, hc, hs⟩ := h
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨s₀, -, hs₀, -, -⟩ := RTL.construct_start_steps hsig hs
  rw [q.beh_of_start hs, SsaProg.beh_of_start (q := q.construct) hs₀]
  by_cases hst : RTL.Behaves q.prog s .stuck
  · rw [ubClose_of_undefined (undefined_mem_rtlObs.mpr hst)]
    exact Set.subset_univ _
  · refine ubClose_mono ?_
    rintro o ⟨b', hb', rfl⟩
    refine ⟨Lift.behaviorOfSsa b', ?_, rfl⟩
    refine (RTL.construct_behaves hsig hc hs hs₀ hst).mpr ?_
    rwa [show (Lift.behaviorOfSsa b').toSSA = b' by cases b' <;> rfl]

/-- The side conditions of erasure: well-formed, every transfer sequential, and a start
state. -/
def SsaProg.Erasable (q : SsaProg) : Prop :=
  q.prog.WellFormed ∧ (∀ fn ∈ q.prog.funcs, Lift.SequentialTransfers fn) ∧
    (q.prog.start q.entry q.args q.mem).isSome

instance (q : SsaProg) : Decidable q.Erasable :=
  inferInstanceAs (Decidable (_ ∧ (∀ _ ∈ _, _) ∧ _))

/-- Erasure of a closed RTL.SSA program: block arguments become moves. -/
def SsaProg.erase (q : SsaProg) : RtlProg :=
  ⟨q.ty, Lift.eraseProg q.prog, q.entry, q.args, q.mem⟩

/-- Erasure, when its side conditions hold. -/
def SsaProg.erase? (q : SsaProg) : Option RtlProg :=
  if q.Erasable then some q.erase else none

/-- **Erasure refines** (it preserves and reflects every behaviour): `Lift.erase_behaves`. -/
theorem SsaProg.beh_erase {q : SsaProg} (h : q.Erasable) : q.erase.beh ⊆ q.beh := by
  obtain ⟨hwf, hseq, hs⟩ := h
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨t, ht, hiff⟩ := Lift.erase_behaves hwf hseq hs
  rw [q.beh_of_start hs, RtlProg.beh_of_start (q := q.erase) ht]
  refine ubClose_mono ?_
  rintro o ⟨b, hb, rfl⟩
  obtain ⟨b', rfl⟩ := behaviorOfSsa_surjective b
  exact ⟨b', (hiff b').mpr hb, rfl⟩

/-- Sequentialization of a closed RTL.SSA program: fresh block parameters, copied into the
originals at the top of each block. -/
def SsaProg.sequentialize (q : SsaProg) : SsaProg :=
  ⟨.sum q.ty, RTL.SSA.sequentializeProg q.prog, q.entry, q.args, q.mem⟩

/-- **Sequentialization preserves behaviours exactly**: `sequentializeProg_behaves`. -/
theorem SsaProg.beh_sequentialize (q : SsaProg) : q.sequentialize.beh = q.beh := by
  cases hs : q.prog.start q.entry q.args q.mem with
  | none =>
    have he : q.prog.enter q.entry q.args = none := by
      unfold RTL.SSA.Prog.start at hs
      simpa using hs
    have : (RTL.SSA.sequentializeProg q.prog).start q.entry q.args q.mem = none := by
      unfold RTL.SSA.Prog.start
      rw [RTL.SSA.seq_enter_none _ _ _ he]
      rfl
    unfold SsaProg.beh SsaProg.sequentialize
    simp only [this, hs]
  | some s =>
    obtain ⟨t, ht, hiff⟩ := RTL.SSA.sequentializeProg_behaves q.prog hs
    rw [q.beh_of_start hs, SsaProg.beh_of_start (q := q.sequentialize) ht]
    congr 1
    ext o
    exact exists_congr fun b => and_congr (hiff b).symm Iff.rfl

/-! ## The passes -/

/-- RTL → Lir. -/
def lowerConv : rtlLang ⟶ lirLang := ⟨id, Eq⟩
/-- RTL → RTL.SSA. -/
def up : rtlLang ⟶ ssaLang := ⟨id, Eq⟩
/-- RTL.SSA → RTL. -/
def down : ssaLang ⟶ rtlLang := ⟨id, Eq⟩

theorem up_down : up ≫ down = 𝟙 rtlLang := Convention.ext rfl Relation.eq_comp

/-- **Lowering RTL to Lir**, a pass at the identity of observations. -/
def lowerLir : Pass lowerConv where
  run q := some q.toLir
  sound q q' h := by
    cases h
    exact (valid_iff_beh _ _ _).2 ⟨rfl, fun o ho => ⟨o, q.beh_toLir_subset ho, rfl⟩⟩

/-- **The maximal SSA construction**, as a pass: it fails on programs outside its side
conditions. -/
def constructPass : Pass up where
  run := RtlProg.construct?
  sound q q' h := by
    unfold RtlProg.construct? at h
    split at h
    · cases h
      exact (valid_iff_beh _ _ _).2 ⟨rfl, fun o ho => ⟨o, RtlProg.beh_construct ‹_› ho, rfl⟩⟩
    · cases h

/-- **Erasure out of SSA**, as a pass: it fails on non-sequential transfers. -/
def erasePass : Pass down where
  run := SsaProg.erase?
  sound q q' h := by
    unfold SsaProg.erase? at h
    split at h
    · cases h
      exact (valid_iff_beh _ _ _).2 ⟨rfl, fun o ho => ⟨o, SsaProg.beh_erase ‹_› ho, rfl⟩⟩
    · cases h

/-- RTL → RTL.SSA → RTL is a round trip. -/
def roundTrip : RoundTrip rtlLang ssaLang where
  lift := constructPass
  lower := erasePass
  le_id := le_of_eq up_down

/-- **Sequentialization, a real SSA optimization**: it preserves behaviours, and afterwards
every transfer is sequential, so erasure accepts it. -/
def sequentializePass : EndoPass ssaLang :=
  ⟨SsaProg.sequentialize, fun q => ⟨rfl, (SsaProg.beh_sequentialize q).subset⟩⟩

/-! ## End to end -/

/-- Optimize RTL in SSA form with any `E`, then lower to Lir. -/
def optimizeAndLower (E : EndoPass ssaLang) : Pass (𝟙 rtlLang ≫ lowerConv) :=
  roundTrip.conj E ≫ₚ lowerLir

/-- **End-to-end validity for every SSA optimization.** Constructing SSA, running any
endo-pass `E` on RTL.SSA, erasing and lowering to Lir is a valid compilation from RTL to Lir
at the identity of observations; nothing about `E` is used beyond its own refinement lemma. -/
theorem optimizeAndLower_sound (E : EndoPass ssaLang) {q : RtlProg} {q' : Mir.LirProgram}
    (h : (optimizeAndLower E).run q = some q') : Valid lowerConv q q' := by
  have := (optimizeAndLower E).sound q q' h
  rwa [Category.id_comp] at this

/-- The same as an explicit pipeline value: RTL → RTL.SSA → RTL.SSA → RTL → Lir. -/
def pipeline (E : EndoPass ssaLang) :=
  Pipeline.cons constructPass <| Pipeline.cons E.toPass <| Pipeline.cons erasePass <|
    Pipeline.cons lowerLir (Pipeline.nil lirLang)

theorem pipeline_sound (E : EndoPass ssaLang) {q : RtlProg} {q' : Mir.LirProgram}
    (h : (pipeline E).run q = some q') : Valid lowerConv q q' := by
  have := (pipeline E).sound h
  have e : up ≫ 𝟙 ssaLang ≫ down ≫ lowerConv ≫ 𝟙 lirLang = lowerConv := by
    rw [Category.comp_id, Category.id_comp, ← Category.assoc, up_down, Category.id_comp]
  rwa [e] at this

/-- The instance at sequentialization. -/
example {q : RtlProg} {q' : Mir.LirProgram} (h : (pipeline sequentializePass).run q = some q') :
    Valid lowerConv q q' :=
  pipeline_sound _ h

end Silmaril.Compile.Semantics
