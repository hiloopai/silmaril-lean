module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Rel

/-!
# Selective asyncify: the simulation relation

The lowering `compO o` instruments a call of `f` iff `o.instr f`. Configurations are related
through **annotated stacks**: every waiting frame carries a flag, `true` when its call site has
its check (`trBO`, the frame sits at its check as in `FXAsync.trB`) and `false` when it does not
(the frame sits directly at its compiled code). The invariant (`OkR`, and the condition on the
top frame) says that an unchecked frame waits on a call, and that every frame above an unchecked
frame runs calm code (`Calm`: no `suspend`, no `resume`, no call into `o.instr`). Then no
unwinding can reach an unchecked frame.

* `trBO`, `trSO`, `trKO`, `trCO`: the translations with all checks (as `FXAsync.trB`, `trS`,
  `trK`, `trC`, for `compO o`);
* `trF`: an annotated waiting frame;
* `Main`, `Rel`: the relation of the simulation (`Rel` also relates the initial configurations
  and empty stacks);
* `compO_whole`: whole-program instrumentation is `FXAsync.comp`.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify

variable {V : Type}

/-! ## Whole-program instrumentation is the existing lowering -/

theorem compO_whole : ∀ c : List (Ins V), compO Opt.whole c = comp c
  | [] => rfl
  | .push _ :: c => congrArg _ (compO_whole c)
  | .prim _ _ :: c => congrArg _ (compO_whole c)
  | .drop :: c => congrArg _ (compO_whole c)
  | .call _ :: c => congrArg (List.cons _ ∘ List.cons _) (compO_whole c)
  | .cond _ _ :: c => congrArg (List.cons _ ∘ List.cons _) (compO_whole c)
  | .contNew _ :: c => congrArg _ (compO_whole c)
  | .resume _ _ :: c => congrArg (List.cons _ ∘ List.cons _) (compO_whole c)
  | .suspend _ _ :: c => congrArg _ (compO_whole c)

theorem compPO_whole (P : Prog (Ins V)) : compPO Opt.whole P = compP P := by
  funext f
  simp only [compPO, compP, compO_whole]

/-- Every program is in the fragment of whole-program instrumentation. -/
theorem sound_whole (P : Prog (Ins V)) : Sound Opt.whole.instr P :=
  fun _ _ _ _ h => absurd h (by simp [Opt.whole])

/-! ## Calm code -/

theorem calm_tail {S : Nat → Bool} {i : Ins V} {c : List (Ins V)} (h : Calm S (i :: c)) :
    Calm S c :=
  fun j hj => h j (List.mem_cons_of_mem _ hj)

theorem calm_call {S : Nat → Bool} {f : Nat} {c : List (Ins V)} (h : Calm S (.call f :: c)) :
    S f = false :=
  h _ (List.mem_cons_self ..)

theorem calm_cond {S : Nat → Bool} {f g : Nat} {c : List (Ins V)}
    (h : Calm S (.cond f g :: c)) : S f = false ∧ S g = false :=
  h _ (List.mem_cons_self ..)

theorem calm_resume {S : Nat → Bool} {n : Nat} {hs : List Clause} {c : List (Ins V)}
    (h : Calm S (.resume n hs :: c)) : False :=
  h _ (List.mem_cons_self ..)

theorem calm_suspend {S : Nat → Bool} {t n : Nat} {c : List (Ins V)}
    (h : Calm S (.suspend t n :: c)) : False :=
  h _ (List.mem_cons_self ..)

/-! ## Translations -/

/-- A waiting frame at its check. -/
def trBO (o : Opt) (b : SFrame V) : TFrame V := ⟨mark b.wait ++ compO o b.code, b.ops⟩

/-- A stack with every check present. -/
def trSO (o : Opt) : List (SFrame V) → List (TFrame V)
  | [] => []
  | fr :: rest => ⟨compO o fr.code, fr.ops⟩ :: rest.map (trBO o)

/-- A continuation store. -/
def trKO (o : Opt) (K : List (Option (List (SFrame V)))) : List (Option (List (TFrame V))) :=
  K.map (Option.map (trSO o))

/-- A configuration with every check present. -/
def trCO (o : Opt) (x : SCfg V) : TCfg V := ⟨trKO o x.conts, .normal, trSO o x.stack⟩

/-- An annotated waiting frame: at its check (`true`) or at its code (`false`). -/
def trF (o : Opt) (b : SFrame V × Bool) : TFrame V :=
  if b.2 then trBO o b.1 else ⟨compO o b.1.code, b.1.ops⟩

/-- Some waiting frame is unchecked. -/
def HasU (A : List (SFrame V × Bool)) : Prop := ∃ b ∈ A, b.2 = false

/-- The invariant of an annotated stack below the top. -/
def OkR (S : Nat → Bool) : List (SFrame V × Bool) → Prop
  | [] => True
  | b :: L => (b.2 = false → b.1.wait = none) ∧ (HasU L → Calm S b.1.code) ∧ OkR S L

/-- **The main relation**: an annotated stack satisfying the invariant. -/
def Main (o : Opt) (x : SCfg V) (y : TCfg V) : Prop :=
  ∃ top A, x.stack = top :: A.map Prod.fst ∧ (HasU A → Calm o.instr top.code) ∧
    OkR o.instr A ∧ y = ⟨trKO o x.conts, .normal, ⟨compO o top.code, top.ops⟩ :: A.map (trF o)⟩

/-- **The relation of the simulation**: empty stacks, the main relation, or the initial pair. -/
def Rel (o : Opt) (f : Nat) (args : List (SV V)) (x : SCfg V) (y : TCfg V) : Prop :=
  (x.stack = [] ∧ y = ⟨trKO o x.conts, .normal, []⟩) ∨ Main o x y ∨
    (x = sInit f args ∧ y = tInit f args)

/-! ## Facts about the translations -/

theorem trF_call (o : Opt) (c : List (Ins V)) (ops : List (SV V)) (b : Bool) :
    trF o (⟨c, ops, none⟩, b) = ⟨chkIf b ++ compO o c, ops⟩ := by
  cases b <;> rfl

/-- With no unchecked frame, the annotated stack is the fully checked one. -/
theorem map_trF_of_not {o : Opt} : ∀ {A : List (SFrame V × Bool)}, ¬ HasU A →
    A.map (trF o) = (A.map Prod.fst).map (trBO o)
  | [], _ => rfl
  | b :: A, h => by
    have hb : b.2 = true := by
      cases hb : b.2
      · exact absurd ⟨b, List.mem_cons_self .., hb⟩ h
      · rfl
    have hA : ¬ HasU A := fun ⟨c, hc, hc'⟩ => h ⟨c, List.mem_cons_of_mem _ hc, hc'⟩
    have hf : trF o b = trBO o b.1 := by simp only [trF, hb, ite_true]
    simp only [List.map_cons, hf, map_trF_of_not hA]

/-- All flags `true`: no unchecked frame. -/
theorem not_hasU_true (L : List (SFrame V)) : ¬ HasU (L.map fun b => (b, true)) := by
  rintro ⟨b, hb, hf⟩
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hb
  cases hf

theorem okR_true (S : Nat → Bool) : ∀ L : List (SFrame V), OkR S (L.map fun b => (b, true))
  | [] => trivial
  | b :: L => by
    show OkR S ((b, true) :: L.map fun b => (b, true))
    exact ⟨fun h => Bool.noConfusion h, fun h => absurd h (not_hasU_true L), okR_true S L⟩

theorem map_trF_true (o : Opt) (L : List (SFrame V)) :
    (L.map fun b => (b, true)).map (trF o) = L.map (trBO o) := by
  simp only [List.map_map]
  rfl

/-- A fully checked configuration is related. -/
theorem rel_trCO (o : Opt) (f : Nat) (args : List (SV V)) (x : SCfg V) :
    Rel o f args x (trCO o x) := by
  rcases x with ⟨K, _ | ⟨top, rest⟩⟩
  · exact .inl ⟨rfl, rfl⟩
  · refine .inr (.inl ⟨top, rest.map fun b => (b, true), ?_, ?_, okR_true _ rest, ?_⟩)
    · simp only [List.map_map]
      exact congrArg _ (List.map_id' rest).symm
    · exact fun h => absurd h (not_hasU_true rest)
    · simp only [trCO, trSO, map_trF_true]

/-- An annotated stack without unchecked frames is the fully checked one. -/
theorem main_eq_trCO {o : Opt} {x : SCfg V} {y : TCfg V} (h : Main o x y)
    (hc : ∀ top A, x.stack = top :: A → ¬ Calm o.instr top.code) : y = trCO o x := by
  obtain ⟨top, A, hx, htop, -, rfl⟩ := h
  have hA : ¬ HasU A := fun hu => hc top _ hx (htop hu)
  simp only [trCO, hx, trSO, map_trF_of_not hA]

end Silmaril.Proofs.Wasm.FX.Asyncify
