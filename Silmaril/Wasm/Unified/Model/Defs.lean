module

public import Silmaril.Wasm.Unified.Sig.Defs
public import Mathlib.Logic.Relation

/-!
# Opcode interpretations: models of feature signatures

A model of a feature signature `S` interprets every opcode of `S` and nothing else.

* `Alg O`: an **opcode algebra** over an opcode type `O`: carriers `I` (meanings of
  instructions) and `D` (meanings of instruction sequences), the empty sequence and sequencing,
  and for each opcode a meaning `op o imms blocks handlers : I` built from its immediates, the
  meanings of its nested blocks and its handler table. Code is evaluated by the fold
  `Alg.evalCode` (structural recursion through the blocks). `Alg.comap f` precomposes the
  opcode meanings with a renaming `f`; `Alg.evalCode_comap` (the homomorphism lemma) says
  evaluating renamed code is evaluating in the precomposed algebra.
* `Model In B S`: an algebra over `S.Op` together with **validation** `ok : D → Prop` and a
  **behaviour** `run : D → In → Set B` (observations `B` of running on inputs `In`). The step
  relation enters through `run`: `Model.stepRun` builds it from a small-step machine (finite
  outcomes of the reflexive-transitive closure, and a divergence observation for infinite
  runs).
* `Model.obs M (c, i)`: the observations of a call: the behaviours of `c` on `i`, if `c`
  validates (invalid code is rejected and has no behaviours).
* `Model.reduct σ M'`: the **reduct** along a signature morphism `σ : S ⟶ S'`: interpret an
  opcode `o` of `S` as `M'` interprets `σ o`. Opcodes of `S'` outside the image of `σ` are
  forgotten. `Model.obs_reduct`: observations of the reduct are observations of renamed code.
* `Model.update M o v`: the model differing from `M` on the one opcode `o` (an erratum, a
  variant). See `Silmaril.Wasm.Unified.Model.Thms` for what it cannot change.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified

open CategoryTheory

/-- An **opcode algebra**: meanings of instructions and sequences, sequencing, and a meaning for
every opcode as a function of its immediates, block meanings and handler table. -/
structure Alg (O : Type) where
  /-- Meanings of instructions. -/
  I : Type
  /-- Meanings of instruction sequences. -/
  D : Type
  /-- The empty sequence. -/
  nil : D
  /-- Sequencing: an instruction followed by a sequence. -/
  cons : I → D → D
  /-- The meaning of each opcode. -/
  op : O → List Imm → List D → List Handler → I

namespace Alg

variable {O O' O'' : Type}

mutual
/-- The meaning of an instruction. -/
def evalInstr (A : Alg O) : UInstr O → A.I
  | .op o imms bs hs => A.op o imms (A.evalBlocks bs) hs
/-- The meaning of an instruction sequence. -/
def evalCode (A : Alg O) : UCode O → A.D
  | [] => A.nil
  | i :: c => A.cons (A.evalInstr i) (A.evalCode c)
/-- The meanings of a list of blocks. -/
def evalBlocks (A : Alg O) : List (UCode O) → List A.D
  | [] => []
  | b :: bs => A.evalCode b :: A.evalBlocks bs
end

/-- Precompose the opcode meanings with a renaming. -/
def comap (f : O → O') (A : Alg O') : Alg O :=
  { A with op := fun o => A.op (f o) }

/-- Change the meaning of one opcode (e.g. a spec erratum). -/
def update [DecidableEq O] (A : Alg O) (o : O) (v : List Imm → List A.D → List Handler → A.I) :
    Alg O :=
  { A with op := Function.update A.op o v }

theorem comap_id (A : Alg O) : A.comap id = A := rfl

theorem comap_comap (f : O → O') (g : O' → O'') (A : Alg O'') :
    (A.comap g).comap f = A.comap (g ∘ f) := rfl

mutual
/-- **Homomorphism lemma** (instructions). -/
theorem evalInstr_comap (f : O → O') (A : Alg O') :
    (i : UInstr O) → (A.comap f).evalInstr i = A.evalInstr (i.map f)
  | .op o imms bs hs => by
    rw [evalInstr, UInstr.map, evalInstr, evalBlocks_comap]
    rfl
/-- **Homomorphism lemma**: evaluating in the precomposed algebra is evaluating renamed code. -/
theorem evalCode_comap (f : O → O') (A : Alg O') :
    (c : UCode O) → (A.comap f).evalCode c = A.evalCode (UInstr.mapCode f c)
  | [] => rfl
  | i :: c => by
    rw [evalCode, UInstr.mapCode, evalCode, evalInstr_comap, evalCode_comap]
    rfl
/-- **Homomorphism lemma** (blocks). -/
theorem evalBlocks_comap (f : O → O') (A : Alg O') :
    (bs : List (UCode O)) → (A.comap f).evalBlocks bs = A.evalBlocks (UInstr.mapBlocks f bs)
  | [] => rfl
  | b :: bs => by
    rw [evalBlocks, UInstr.mapBlocks, evalBlocks, evalCode_comap, evalBlocks_comap]
    rfl
end

end Alg

/-- A **model** of a feature signature: an interpretation of its opcodes (an opcode algebra),
validation of meanings, and the behaviours of running a meaning on an input. -/
structure Model (In B : Type) (S : FSig) where
  /-- The interpretation of the opcodes of `S`. -/
  alg : Alg S.Op
  /-- Validation. -/
  ok : alg.D → Prop
  /-- Behaviours (the step semantics, read off as observations). -/
  run : alg.D → In → Set B

namespace Model

variable {In B : Type} {S S' S'' : FSig}

/-- Change the meaning of one opcode, keeping carriers, validation and behaviours. -/
def update [DecidableEq S.Op] (M : Model In B S) (o : S.Op)
    (v : List Imm → List M.alg.D → List Handler → M.alg.I) : Model In B S :=
  ⟨M.alg.update o v, M.ok, M.run⟩

/-- The observations of a call: behaviours of validated code. -/
def obs (M : Model In B S) (x : S.Code × In) : Set B :=
  {b | M.ok (M.alg.evalCode x.1) ∧ b ∈ M.run (M.alg.evalCode x.1) x.2}

/-- **The reduct** along a signature morphism: interpret `o` as `σ o`. -/
def reduct (σ : S ⟶ S') (M : Model In B S') : Model In B S :=
  { M with alg := M.alg.comap σ.f }

theorem reduct_id (M : Model In B S) : M.reduct (𝟙 S) = M := rfl

theorem reduct_comp (σ : S ⟶ S') (τ : S' ⟶ S'') (M : Model In B S'') :
    M.reduct (σ ≫ τ) = (M.reduct τ).reduct σ := rfl

/-- Observations of the reduct are observations of renamed code. -/
theorem obs_reduct (σ : S ⟶ S') (M : Model In B S') (c : S.Code) (i : In) :
    (M.reduct σ).obs (c, i) = M.obs (UInstr.mapCode σ.f c, i) := by
  show {b | M.ok ((M.alg.comap σ.f).evalCode c) ∧ b ∈ M.run ((M.alg.comap σ.f).evalCode c) i} = _
  rw [Alg.evalCode_comap]
  rfl

/-! ## Behaviours from a step relation -/

/-- A small-step machine for meanings `D` on inputs `In`: configurations, loading, steps, and
the observation of a final configuration. -/
structure Machine (D In B : Type) where
  /-- Configurations. -/
  Cfg : Type
  /-- The initial configuration. -/
  load : D → In → Cfg
  /-- The step relation. -/
  step : Cfg → Cfg → Prop
  /-- Final configurations and their observations. -/
  out : Cfg → Option B

/-- The behaviours of a machine: outcomes of finite runs, and `div` for an infinite run. -/
def Machine.run {D In B : Type} (m : Machine D In B) (div : B) (d : D) (i : In) : Set B :=
  {b | ∃ c, Relation.ReflTransGen m.step (m.load d i) c ∧ m.out c = some b} ∪
  {b | b = div ∧ ∃ f : Nat → m.Cfg, f 0 = m.load d i ∧ ∀ n, m.step (f n) (f (n + 1))}

/-- A model from an opcode algebra, validation and a small-step machine. -/
def stepRun (alg : Alg S.Op) (ok : alg.D → Prop) (m : Machine alg.D In B) (div : B) :
    Model In B S :=
  ⟨alg, ok, m.run div⟩

end Model

end Silmaril.Wasm.Unified
