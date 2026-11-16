module

public import Silmaril.Logic.Consequence.Defs

/-!
# Interpretations: values read as consequence systems

An *interpretation* reads a value `v : Value`, under a typed configuration `e : Env`, as a
consequence system, or fails to:

  `Interp Env Value Ax C := (e : Env) → Value → Option (System (Ax e) (C e))`.

* `Env` is **static configuration**, typed: which export or function index, the ABI, a
  profile, a set of admissible hosts. `Env = Unit` is the parameterless case (`Interp₀`). How a
  runtime host behaves is a separate semantic object; it enters an interpretation only through
  `Env` or `Value`.
* The output types `Ax e` and `C e` are explicit **families** over the configuration, in
  independent universes, so that different configurations may read different context and
  conclusion types.
* `none` means "not interpretable" (for example, the bytes do not parse). It is **not** the
  empty system: `some ⊥` is a system, verified to prove nothing. `sysOrBot` (and
  `Interp.orBot`) is the explicit compatibility projection to a raw system, sending `none` to
  `⊥`. It forgets this distinction (`Thms`: `sysOrBot_not_injective`), which is how the
  registry's `artifactSystem` reads parse failure.
* There is no lattice or monad structure claimed on `Option (System …)`. The complete lattice is
  on raw `System` only.

Operations: `ofDecode` (parse, then interpret), `map` (post-compose on systems), `pullback`
(reindex contexts and conclusions; it commutes with `orBot` because pullback preserves `⊥`),
`reindex` (change the configuration), `comap` (pre-process values, partially).

Evidence against a total specification `ref : (e : Env) → Value → System (Ax e) (C e)`:
`SoundFor`, `CompleteFor` and the slice-bounded `CompleteOnFor`. All of them quantify over
**defined** readings only. Definedness is a separate fact (`Defined`), never inferred from
`orBot`. At the level of systems: `System.SoundOn` and `System.CompleteOn` restrict to a slice
`P : Ax → C → Prop` (for example, contexts up to some size).

`WInterp` is the proof-relevant variant, reading values as witness systems, with `erase`.
-/

@[expose] public section

namespace Silmaril.Consequence

universe u v w z w' z' u' v' t

/-- `S` is sound against `T` on the slice `P`. -/
def System.SoundOn {Ax : Type w} {C : Type z} (S T : System Ax C) (P : Ax → C → Prop) : Prop :=
  ∀ a c, P a c → S a c → T a c

/-- `S` is complete against `T` on the slice `P` (bounded completeness when `P` bounds size). -/
def System.CompleteOn {Ax : Type w} {C : Type z} (S T : System Ax C) (P : Ax → C → Prop) :
    Prop :=
  ∀ a c, P a c → T a c → S a c

/-- Read a value, under a configuration, as a system; `none` when it cannot be read. -/
def Interp (Env : Type u) (Value : Type v) (Ax : Env → Type w) (C : Env → Type z) :
    Type (max u v w z) :=
  (e : Env) → Value → Option (System (Ax e) (C e))

/-- Parameterless interpretations with fixed output types. -/
abbrev Interp₀ (Value : Type v) (Ax : Type w) (C : Type z) : Type (max v w z) :=
  Interp PUnit.{1} Value (fun _ => Ax) (fun _ => C)

/-- The compatibility projection: an undefined reading becomes the empty system. -/
def sysOrBot {Ax : Type w} {C : Type z} : Option (System Ax C) → System Ax C
  | none => ⊥
  | some S => S

namespace Interp

variable {Env : Type u} {Value : Type v} {Ax : Env → Type w} {C : Env → Type z}

/-- The reading of `v` under `e` is defined. -/
def Defined (I : Interp Env Value Ax C) (e : Env) (v : Value) : Prop := (I e v).isSome = true

/-- The raw system, with undefined readings sent to `⊥`. -/
def orBot (I : Interp Env Value Ax C) (e : Env) (v : Value) : System (Ax e) (C e) :=
  sysOrBot (I e v)

/-- Decode, then interpret the decoded value. -/
def ofDecode {V : Type t} (parse : Value → Option V) (J : (e : Env) → V → System (Ax e) (C e)) :
    Interp Env Value Ax C :=
  fun e v => (parse v).map (J e)

/-- Post-compose every defined reading with a map of systems. -/
def map {Ax' : Env → Type w'} {C' : Env → Type z'}
    (f : ∀ e, System (Ax e) (C e) → System (Ax' e) (C' e)) (I : Interp Env Value Ax C) :
    Interp Env Value Ax' C' :=
  fun e v => (I e v).map (f e)

/-- Reindex contexts and conclusions of every defined reading. -/
def pullback {Ax' : Env → Type w'} {C' : Env → Type z'} (fa : ∀ e, Ax' e → Ax e)
    (fc : ∀ e, C' e → C e) (I : Interp Env Value Ax C) : Interp Env Value Ax' C' :=
  I.map fun e S => S.pullback (fa e) (fc e)

/-- Change the configuration type. -/
def reindex {Env' : Type u'} (g : Env' → Env) (I : Interp Env Value Ax C) :
    Interp Env' Value (fun e => Ax (g e)) (fun e => C (g e)) :=
  fun e v => I (g e) v

/-- Pre-process values, possibly failing. -/
def comap {Value' : Type v'} (h : Value' → Option Value) (I : Interp Env Value Ax C) :
    Interp Env Value' Ax C :=
  fun e v => (h v).bind (I e)

/-- Every defined reading is sound against `ref`. -/
def SoundFor (I : Interp Env Value Ax C) (ref : (e : Env) → Value → System (Ax e) (C e)) :
    Prop :=
  ∀ e v S, I e v = some S → S ≤ ref e v

/-- Every defined reading is complete against `ref`. -/
def CompleteFor (I : Interp Env Value Ax C) (ref : (e : Env) → Value → System (Ax e) (C e)) :
    Prop :=
  ∀ e v S, I e v = some S → ref e v ≤ S

/-- Every defined reading is complete against `ref` on the slice `P e`. -/
def CompleteOnFor (I : Interp Env Value Ax C) (ref : (e : Env) → Value → System (Ax e) (C e))
    (P : (e : Env) → Ax e → C e → Prop) : Prop :=
  ∀ e v S, I e v = some S → S.CompleteOn (ref e v) (P e)

end Interp

/-- Read a value, under a configuration, as a witness system; `none` when it cannot be read. -/
def WInterp (Env : Type u) (Value : Type v) (Ax : Env → Type w) (C : Env → Type z) :
    Type (max u v w z (t + 1)) :=
  (e : Env) → Value → Option (WSystem.{w, z, t} (Ax e) (C e))

/-- Forget witnesses. -/
def WInterp.erase {Env : Type u} {Value : Type v} {Ax : Env → Type w} {C : Env → Type z}
    (I : WInterp.{u, v, w, z, t} Env Value Ax C) : Interp Env Value Ax C :=
  fun e v => (I e v).map WSystem.erase

end Silmaril.Consequence
