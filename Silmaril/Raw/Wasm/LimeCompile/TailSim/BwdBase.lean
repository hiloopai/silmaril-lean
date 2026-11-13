module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.BwdSplit
public import Silmaril.Raw.Wasm.LimeCompile.TailSim.FwdLabel

/-!
# The backward simulation of the tail-call rewrite: the matching statement and shared facts

* `BM`, `BIH`: the backward matching (a target step matched by a non-empty source run, or by a
  stutter of the source while the target's code shrinks) and its induction hypothesis, for
  pairs that are not pending (`PendR`);
* `BM.lift`: matching lifts through a value prefix and a related suffix;
* `R.vals_tinv`, `R.kernel_tinv`, `R.rcr_tinv`, `R.trap_tinv`, `R.throw_tinv`: the source of
  a target of values, or of values before `br`/`return`/`return_call_ref`, a trap or a throw;
* `TA.step`, `TT.step`: steps of trap- and throw-active code;
* `CallHead.match_back`: a target call is matched by the same call on the source.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **The pending shapes**: the target's `CALL_REF; RETURN` against the source's
`RETURN_CALL_REF`, under labels. -/
inductive PendR : List Admin → List Admin → Prop where
  | rcr {V : List Val} {c c' : Admin} {x y : List Admin} : RCRPair c c' →
      PendR (vals V ++ c :: x) (vals V ++ c' :: .plain .return_ :: y)
  | label {V : List Val} {n : Nat} {cont cont' : List Instr} {b b' x y : List Admin} :
      PendR b b' → PendR (vals V ++ .label n cont b :: x) (vals V ++ .label n cont' b' :: y)

/-- **Backward matching** of a target step to `⟨t', f', y'⟩` from the source `⟨s, f, x⟩`. -/
def BM (P : Numerics.Profile) (host : HostSemantics H) (tl : Bool) (t' : Store H) (f' : Frame)
    (y' : List Admin) (s : Store H) (f : Frame) (x : List Admin) (m : Nat) : Prop :=
  ∃ (s' : Store H) (x' : List Admin),
    (Relation.TransGen (Step P host) ⟨s, f, x⟩ ⟨s', f', x'⟩ ∨
      (s' = s ∧ f' = f ∧ x' = x ∧ codeSize y' < m)) ∧
    StoreRel FRel s' t' ∧ R false tl x' y'

/-- **The backward induction hypothesis**, for pairs that are not pending. -/
def BIH (P : Numerics.Profile) (host : HostSemantics H) (m : Nat) : Prop :=
  ∀ {tl : Bool} {s t t' : Store H} {f f' : Frame} {x y y' : List Admin},
    codeSize y < m → StoreRel FRel s t → R false tl x y → ¬ PendR x y →
    ContextTyped ⟨s, f, x⟩ → ContextTyped ⟨t, f, y⟩ → Step P host ⟨t, f, y⟩ ⟨t', f', y'⟩ →
    BM P host tl t' f' y' s f x (codeSize y)

theorem BIH.mono {m m' : Nat} (h : BIH P host m) (hm : m' ≤ m) : BIH P host m' :=
  fun hx => h (Nat.lt_of_lt_of_le hx hm)

theorem BM.lift {tl : Bool} {t' s : Store H} {f f' : Frame} {is' X Y : List Admin}
    (h : BM P host tl t' f' is' s f X (codeSize Y)) (W : List Val) {rest rest' : List Admin}
    (hr : R false tl rest rest') :
    BM P host tl t' f' (vals W ++ is' ++ rest') s f (vals W ++ X ++ rest)
      (codeSize (vals W ++ Y ++ rest')) := by
  obtain ⟨s', x', hm, hst, hR⟩ := h
  refine ⟨s', vals W ++ x' ++ rest, ?_, hst, ?_⟩
  · rcases hm with ht | ⟨rfl, rfl, rfl, hlt⟩
    · exact Or.inl (trans_mid ht W rest)
    · exact Or.inr ⟨rfl, rfl, rfl, LawfulCodeRank.context_lt (vals W) rest' hlt⟩
  · simpa using R.valPre (R.append hr hR) W

theorem BM.of_trans {tl : Bool} {t' s s' : Store H} {f f' : Frame} {y' x x' : List Admin}
    {m : Nat} (ht : Relation.TransGen (Step P host) ⟨s, f, x⟩ ⟨s', f', x'⟩)
    (hst : StoreRel FRel s' t') (hR : R false tl x' y') : BM P host tl t' f' y' s f x m :=
  ⟨s', x', Or.inl ht, hst, hR⟩

theorem BM.of_stutter {tl : Bool} {t' s : Store H} {f : Frame} {y' x : List Admin} {m : Nat}
    (hlt : codeSize y' < m) (hst : StoreRel FRel s t') (hR : R false tl x y') :
    BM P host tl t' f y' s f x m :=
  ⟨s, x, Or.inr ⟨rfl, rfl, rfl, hlt⟩, hst, hR⟩

/-! ## Trap- and throw-active code -/

theorem TA.not_vals : ∀ {y : List Admin}, TA y → ∀ vs, y ≠ vals vs := by
  intro y h vs hy
  have hm : ∃ b, b ∈ y ∧ b.val? = none := by
    cases h with
    | base ws y => exact ⟨.trap, by simp, rfl⟩
    | @label ws n cont bb y _ => exact ⟨.label n cont bb, by simp, rfl⟩
    | @frame ws n fi bb y _ => exact ⟨.frame n fi bb, by simp, rfl⟩
  obtain ⟨b, hb, hv⟩ := hm
  rw [hy] at hb
  obtain ⟨w, rfl⟩ := PC.mem_vals hb
  simp at hv

theorem TT.not_vals {a : Nat} : ∀ {y : List Admin}, TT a y → ∀ vs, y ≠ vals vs := by
  intro y h vs hy
  have hm : ∃ b, b ∈ y ∧ b.val? = none := by
    cases h with
    | base ws y => exact ⟨.plain .throwRef, by simp [throwing], rfl⟩
    | @label ws n cont bb y _ => exact ⟨.label n cont bb, by simp, rfl⟩
    | @frame ws n fi bb y _ => exact ⟨.frame n fi bb, by simp, rfl⟩
  obtain ⟨b, hb, hv⟩ := hm
  rw [hy] at hb
  obtain ⟨w, rfl⟩ := PC.mem_vals hb
  simp at hv

/-- The active head of trap-active code. -/
theorem TA.head {y : List Admin} (h : TA y) {ws : List Val} {b : Admin} {r : List Admin}
    (hb : b.val? = none) (hy : y = vals ws ++ b :: r) :
    b = .trap ∨ (∃ n cont bb, b = .label n cont bb ∧ TA bb) ∨
      ∃ n fi bb, b = .frame n fi bb ∧ TA bb := by
  cases h with
  | base ws' y' =>
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj rfl hb hy
    exact .inl rfl
  | label ws' n cont y' hb' =>
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj rfl hb hy
    exact .inr (.inl ⟨_, _, _, rfl, hb'⟩)
  | frame ws' n fi y' hb' =>
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj rfl hb hy
    exact .inr (.inr ⟨_, _, _, rfl, hb'⟩)

/-- The active head of throw-active code. -/
theorem TT.head {a : Nat} {y : List Admin} (h : TT a y) {ws : List Val} {b : Admin}
    {r : List Admin} (hb : b.val? = none) (hy : y = vals ws ++ b :: r) :
    (b = .plain .throwRef ∧ ∃ ws', ws = ws' ++ [.ref (.exn a)]) ∨
      (∃ n cont bb, b = .label n cont bb ∧ TT a bb) ∨ ∃ n fi bb, b = .frame n fi bb ∧ TT a bb := by
  cases h with
  | base ws' y' =>
    rw [throw_eq] at hy
    obtain ⟨h1, rfl, -⟩ := vals_append_cons_inj rfl hb hy
    exact .inl ⟨rfl, ws', h1.symm⟩
  | label ws' n cont y' hb' =>
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj rfl hb hy
    exact .inr (.inl ⟨_, _, _, rfl, hb'⟩)
  | frame ws' n fi y' hb' =>
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj rfl hb hy
    exact .inr (.inr ⟨_, _, _, rfl, hb'⟩)

end Silmaril.Raw.Wasm.LimeCompile.TailSim
