module

public import Silmaril.Logic.Consequence.Interp.Defs
public import Silmaril.Logic.Consequence.Thms

/-!
# Interpretations: laws

**The projection.** `sysOrBot_none`, `sysOrBot_some`. `sysOrBot_map_iff`: projecting a mapped
option is "some decoded value is interpreted to prove it". This is the shape of the registry's
`artifactSystem`. `sysOrBot_not_injective`: `none` and `some ⊥` project to the same system,
although `none ≠ some ⊥`, so the projection forgets definedness.

**Operations.** `map_id`, `map_comp`. `orBot_map`: `map f` commutes with `orBot` **when
`f ⊥ = ⊥`**; `orBot_map_counterexample` shows that it can fail otherwise. `orBot_pullback`:
pullback always commutes (`System.pullback_bot`). `orBot_ofDecode`, `orBot_reindex`,
`comap_some`.

**Evidence.** `soundFor_iff_orBot`: soundness can be read off the projection, since `⊥` is
sound. Completeness cannot: `completeFor_of_orBot` holds in one direction, and the converse
`orBot_complete_of_completeFor` needs every reading to be defined. `soundFor_completeFor_iff`:
sound and complete means every defined reading is the specification. `eq_some_of_sound_complete`
then gives `I e v = some (ref e v)` from an explicit `Defined` premise.
`CompleteFor.completeOnFor`: completeness implies completeness on any slice.
`completeOnFor_top_iff`: completeness on the trivial slice is completeness.
-/

@[expose] public section

namespace Silmaril.Consequence

universe u v w z w' z' w'' z'' u' v' t

section Proj

variable {Ax : Type w} {C : Type z}

@[simp] theorem sysOrBot_none : sysOrBot (none : Option (System Ax C)) = ⊥ := rfl
@[simp] theorem sysOrBot_some (S : System Ax C) : sysOrBot (some S) = S := rfl

theorem sysOrBot_map_iff {V : Type t} (o : Option V) (f : V → System Ax C) (a : Ax) (c : C) :
    sysOrBot (o.map f) a c ↔ ∃ x, o = some x ∧ f x a c := by
  cases o <;> simp

theorem sysOrBot_not_injective :
    sysOrBot (none : Option (System Ax C)) = sysOrBot (some ⊥) ∧
      (none : Option (System Ax C)) ≠ some ⊥ := ⟨rfl, by simp⟩

end Proj

namespace Interp

variable {Env : Type u} {Value : Type v} {Ax : Env → Type w} {C : Env → Type z}
  {Ax' : Env → Type w'} {C' : Env → Type z'} {Ax'' : Env → Type w''} {C'' : Env → Type z''}
  (I : Interp Env Value Ax C)

theorem defined_iff (e : Env) (v : Value) : I.Defined e v ↔ ∃ S, I e v = some S :=
  Option.isSome_iff_exists

theorem orBot_of_eq_some {e : Env} {v : Value} {S : System (Ax e) (C e)} (h : I e v = some S) :
    I.orBot e v = S := by simp [orBot, h]

theorem orBot_of_eq_none {e : Env} {v : Value} (h : I e v = none) : I.orBot e v = ⊥ := by
  simp [orBot, h]

theorem map_id : I.map (fun _ S => S) = I := funext₂ fun _ _ => Option.map_id'

theorem map_comp (f : ∀ e, System (Ax e) (C e) → System (Ax' e) (C' e))
    (g : ∀ e, System (Ax' e) (C' e) → System (Ax'' e) (C'' e)) :
    (I.map f).map g = I.map fun e S => g e (f e S) :=
  funext₂ fun _ _ => Option.map_map _ _ _

theorem orBot_map (f : ∀ e, System (Ax e) (C e) → System (Ax' e) (C' e))
    (hf : ∀ e, f e ⊥ = ⊥) (e : Env) (v : Value) : (I.map f).orBot e v = f e (I.orBot e v) := by
  cases h : I e v <;> simp [orBot, map, h, hf]

/-- Without `f ⊥ = ⊥`, mapping does not commute with the projection. -/
theorem orBot_map_counterexample :
    let J : Interp₀ PUnit.{1} PUnit.{1} PUnit.{1} := fun _ _ => none
    let f : ∀ _ : PUnit.{1}, System PUnit.{1} PUnit.{1} → System PUnit.{1} PUnit.{1} :=
      fun _ _ => ⊤
    (J.map f).orBot () () ≠ f () (J.orBot () ()) := fun h => by
  simpa [orBot, map] using congrFun₂ h () ()

theorem orBot_pullback (fa : ∀ e, Ax' e → Ax e) (fc : ∀ e, C' e → C e) (e : Env) (v : Value) :
    (I.pullback fa fc).orBot e v = (I.orBot e v).pullback (fa e) (fc e) :=
  I.orBot_map _ (fun _ => System.pullback_bot _ _) e v

theorem orBot_ofDecode {V : Type t} (parse : Value → Option V)
    (J : (e : Env) → V → System (Ax e) (C e)) (e : Env) (v : Value) (a : Ax e) (c : C e) :
    (ofDecode parse J).orBot e v a c ↔ ∃ x, parse v = some x ∧ J e x a c :=
  sysOrBot_map_iff _ _ a c

theorem orBot_reindex {Env' : Type u'} (g : Env' → Env) (e : Env') (v : Value) :
    (I.reindex g).orBot e v = I.orBot (g e) v := rfl

theorem comap_some {Value' : Type v'} (h : Value' → Option Value) {e : Env} {v' : Value'}
    {v : Value} (hv : h v' = some v) : I.comap h e v' = I e v := by simp [comap, hv]

/-! ## Evidence -/

variable {I} {ref : (e : Env) → Value → System (Ax e) (C e)}

theorem soundFor_iff_orBot : I.SoundFor ref ↔ ∀ e v, I.orBot e v ≤ ref e v :=
  ⟨fun h e v => by
    cases hv : I e v with
    | none => simp [orBot, hv]
    | some S => simpa [orBot, hv] using h e v S hv,
   fun h e v S hv => by simpa [orBot, hv] using h e v⟩

theorem completeFor_of_orBot (h : ∀ e v, ref e v ≤ I.orBot e v) : I.CompleteFor ref :=
  fun e v S hv => by simpa [orBot, hv] using h e v

theorem orBot_complete_of_completeFor (h : I.CompleteFor ref) (hd : ∀ e v, I.Defined e v)
    (e : Env) (v : Value) : ref e v ≤ I.orBot e v := by
  obtain ⟨S, hS⟩ := (defined_iff I e v).1 (hd e v)
  simpa [orBot, hS] using h e v S hS

theorem soundFor_completeFor_iff :
    I.SoundFor ref ∧ I.CompleteFor ref ↔ ∀ e v S, I e v = some S → S = ref e v :=
  ⟨fun ⟨hs, hc⟩ e v S hv => le_antisymm (hs e v S hv) (hc e v S hv),
   fun h => ⟨fun e v S hv => (h e v S hv).le, fun e v S hv => (h e v S hv).ge⟩⟩

theorem eq_some_of_sound_complete (hs : I.SoundFor ref) (hc : I.CompleteFor ref) {e : Env}
    {v : Value} (hd : I.Defined e v) : I e v = some (ref e v) := by
  obtain ⟨S, hS⟩ := (defined_iff I e v).1 hd
  rw [hS, soundFor_completeFor_iff.1 ⟨hs, hc⟩ e v S hS]

theorem CompleteFor.completeOnFor (h : I.CompleteFor ref) (P : (e : Env) → Ax e → C e → Prop) :
    I.CompleteOnFor ref P := fun e v S hv a c _ hr => h e v S hv a c hr

theorem completeOnFor_top_iff : I.CompleteOnFor ref (fun _ _ _ => True) ↔ I.CompleteFor ref :=
  ⟨fun h e v S hv a c hr => h e v S hv a c trivial hr, fun h => h.completeOnFor _⟩

end Interp

theorem WInterp.erase_defined {Env : Type u} {Value : Type v} {Ax : Env → Type w}
    {C : Env → Type z} (I : WInterp.{u, v, w, z, t} Env Value Ax C) (e : Env) (v : Value) :
    I.erase.Defined e v ↔ (I e v).isSome = true := by
  simp [Interp.Defined, WInterp.erase]

end Silmaril.Consequence
