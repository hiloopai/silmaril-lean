module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.FwdSplit
public import Silmaril.Raw.Wasm.LimeCompile.TailSim.Call
public import Silmaril.Raw.Wasm.LimeCompile.TailSim.Typing
public import Silmaril.Wasm.Execution.Core.Sim.Rank
public import Silmaril.Wasm.Execution.Core.Sim.Segments

/-!
# The forward simulation of the tail-call rewrite: the matching statement and shared facts

* `FM`: a source step to `⟨s', f', x'⟩` is matched from the target `⟨t, f, y⟩` by a non-empty
  run, or by stuttering while the source code shrinks below `m`; the results have related stores
  and related code (forward relation, same level);
* `FIH m`: the one-step obligation for source code smaller than `m` (the induction hypothesis);
* `FM.lift`: matching lifts through a value prefix and a related suffix;
* `R.vals_inv`, `R.kernel_inv`, `R.trap_inv`, `R.throw_inv`: in the forward relation a source
  that is values, or values before `br`/`return`, a trap or a throw, has a target of the same
  shape (or trap- / throw-active);
* `CT_fill`: typing descends through a nest of labels.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **Forward matching** of a source step to `⟨s', f', x'⟩` from the target `⟨t, f, y⟩`. -/
def FM (P : Numerics.Profile) (host : HostSemantics H) (tl : Bool) (s' : Store H) (f' : Frame)
    (x' : List Admin) (t : Store H) (f : Frame) (y : List Admin) (m : Nat) : Prop :=
  ∃ (t' : Store H) (y' : List Admin),
    (Relation.TransGen (Step P host) ⟨t, f, y⟩ ⟨t', f', y'⟩ ∨
      (t' = t ∧ f' = f ∧ y' = y ∧ codeSize x' < m)) ∧
    StoreRel FRel s' t' ∧ R true tl x' y'

/-- **The forward induction hypothesis**: the one-step obligation below `m`. -/
def FIH (P : Numerics.Profile) (host : HostSemantics H) (m : Nat) : Prop :=
  ∀ {tl : Bool} {s t s' : Store H} {f f' : Frame} {x y x' : List Admin},
    codeSize x < m → StoreRel FRel s t → R true tl x y → ContextTyped ⟨s, f, x⟩ →
    ContextTyped ⟨t, f, y⟩ → Step P host ⟨s, f, x⟩ ⟨s', f', x'⟩ →
    FM P host tl s' f' x' t f y (codeSize x)

theorem FIH.mono {m m' : Nat} (h : FIH P host m) (hm : m' ≤ m) : FIH P host m' :=
  fun hx => h (Nat.lt_of_lt_of_le hx hm)

/-- **Matching lifts** through a value prefix and a related suffix. -/
theorem FM.lift {tl : Bool} {s' t : Store H} {f f' : Frame} {is' X Y : List Admin}
    (h : FM P host tl s' f' is' t f Y (codeSize X)) (W : List Val) {rest rest' : List Admin}
    (hr : R true tl rest rest') :
    FM P host tl s' f' (vals W ++ is' ++ rest) t f (vals W ++ Y ++ rest')
      (codeSize (vals W ++ X ++ rest)) := by
  obtain ⟨t', y', hm, hst, hR⟩ := h
  refine ⟨t', vals W ++ y' ++ rest', ?_, hst, ?_⟩
  · rcases hm with ht | ⟨rfl, rfl, rfl, hlt⟩
    · exact Or.inl (trans_mid ht W rest')
    · exact Or.inr ⟨rfl, rfl, rfl, LawfulCodeRank.context_lt (vals W) rest hlt⟩
  · simpa using R.valPre (R.append hr hR) W

/-- A non-empty target run with related results. -/
theorem FM.of_trans {tl : Bool} {s' t t' : Store H} {f f' : Frame} {x' y y' : List Admin}
    {m : Nat} (ht : Relation.TransGen (Step P host) ⟨t, f, y⟩ ⟨t', f', y'⟩)
    (hst : StoreRel FRel s' t') (hR : R true tl x' y') : FM P host tl s' f' x' t f y m :=
  ⟨t', y', Or.inl ht, hst, hR⟩

/-- A stutter with related results. -/
theorem FM.of_stutter {tl : Bool} {s' t : Store H} {f : Frame} {x' y : List Admin} {m : Nat}
    (hlt : codeSize x' < m) (hst : StoreRel FRel s' t) (hR : R true tl x' y) :
    FM P host tl s' f x' t f y m :=
  ⟨t, y, Or.inr ⟨rfl, rfl, rfl, hlt⟩, hst, hR⟩

/-! ## Shapes of the target -/

/-- A source of values has the same values as target. -/
theorem R.vals_inv {tl : Bool} : ∀ {vs : List Val} {y : List Admin}, R true tl (vals vs) y →
    y = vals vs
  | [], y, h => by
    generalize hx : vals [] = x at h
    simp only [Sim.vals_nil'] at hx
    cases h with
    | nil => rfl
    | same => cases hx
    | instr => cases hx
    | rcr => cases hx
    | label => cases hx
    | handler => cases hx
    | callee hce _ =>
      rcases CE.src_shape hce with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> simp at hx
    | bub => simp at hx
    | trapC => simp at hx
    | throwC => simp [throwing] at hx
  | v :: vs, y, h => by
    generalize hx : vals (v :: vs) = x at h
    cases h with
    | nil => simp at hx
    | same hc h' =>
      simp only [Sim.vals_cons', List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      rw [R.vals_inv h']
    | @instr _ i _ _ h' =>
      simp only [Sim.vals_cons', List.cons.injEq] at hx
      obtain ⟨hv, rfl⟩ := hx
      have hti : tailI i = [i] := tailI_of_val (v := v) (by rw [← hv]; simp)
      rw [hti, R.vals_inv h']
      simp
    | rcr hc _ =>
      simp only [Sim.vals_cons', List.cons.injEq] at hx
      have := RCRPair.val?_eq hc
      rw [← hx.1] at this; simp at this
    | label =>
      simp only [Sim.vals_cons', List.cons.injEq] at hx
      have hn := Val.toAdmin_not_ctx v
      rw [hx.1] at hn; exact absurd trivial hn
    | handler =>
      simp only [Sim.vals_cons', List.cons.injEq] at hx
      have hn := Val.toAdmin_not_ctx v
      rw [hx.1] at hn; exact absurd trivial hn
    | callee hce _ =>
      exfalso
      rcases CE.src_shape hce with ⟨_, _, rfl⟩ | ⟨vs', a, d, rfl⟩
      · simp only [Sim.vals_cons', List.singleton_append, List.cons.injEq] at hx
        have hn := Val.toAdmin_not_ctx v
        rw [hx.1] at hn; exact absurd trivial hn
      · have hm : Admin.callRefType d ∈ vals (v :: vs) := by rw [hx]; simp
        obtain ⟨w, hw⟩ := PC.mem_vals hm
        rcases w with ⟨⟨_ | _, _⟩⟩ | _ | _ <;> simp [Val.toAdmin] at hw
    | @bub ws c B U X hp =>
      exfalso
      obtain ⟨c', hc⟩ := PTL.rcr hp
      have hm : c ∈ vals (v :: vs) := by rw [hx]; simp
      obtain ⟨w, hw⟩ := PC.mem_vals hm
      have := RCRPair.val?_eq hc
      rw [hw] at this; simp at this
    | trapC us x _ =>
      exfalso
      have hm : Admin.trap ∈ vals (v :: vs) := by rw [hx]; simp
      obtain ⟨w, hw⟩ := PC.mem_vals hm
      rcases w with ⟨⟨_ | _, _⟩⟩ | _ | _ <;> simp [Val.toAdmin] at hw
    | throwC us x _ =>
      exfalso
      have hm : Admin.plain .throwRef ∈ vals (v :: vs) := by rw [hx]; simp [throwing]
      obtain ⟨w, hw⟩ := PC.mem_vals hm
      rcases w with ⟨⟨_ | _, _⟩⟩ | _ | _ <;> simp [Val.toAdmin] at hw

/-- A kernel that relates only to itself (`br`, `return`). -/
def Rigid : Admin → Prop
  | .plain (.br _) | .plain .return_ => True
  | _ => False

theorem Rigid.val?_eq {k : Admin} (h : Rigid k) : k.val? = none := by
  rcases k with i | _ | _ | _ | _ | _ | _ | _
  · cases i <;> first | rfl | exact (h : False).elim
  all_goals first | rfl | exact (h : False).elim

theorem Rigid.not_rcr {k : Admin} (h : Rigid k) : ¬ k.IsReturnCallRef := by
  rcases k with i | _ | _ | _ | _ | _ | _ | _
  · cases i <;> simp_all [Rigid, Admin.IsReturnCallRef]
  all_goals exact fun _ => (h : False).elim

theorem RCRPair.not_rigid {c c' : Admin} (h : RCRPair c c') : ¬ Rigid c :=
  fun hk => Rigid.not_rcr hk (RCRPair.isReturnCallRef h)

/-- **Rigid kernels**: values before `br` or `return` in the source have the same target. -/
theorem R.kernel_inv {tl : Bool} {V : List Val} {k : Admin} {rest y : List Admin}
    (hk : Rigid k) (h : R true tl (vals V ++ k :: rest) y) :
    ∃ y', y = vals V ++ k :: y' ∧ R true tl rest y' := by
  obtain ⟨V₀, V₁, y₀, rfl, rfl, hh⟩ := R.split hk.val?_eq h
  cases hh with
  | same _ hr => exact ⟨_, by simp, hr⟩
  | @instr i _ _ hr =>
    have hti : tailI i = [i] := by
      cases i <;> simp_all [Rigid, Silmaril.Wasm.LimeCompile.Tail.tailI]
    exact ⟨_, by rw [hti]; simp, hr⟩
  | rcr hc _ => exact absurd hk (RCRPair.not_rigid hc)
  | label => exact (hk : False).elim
  | handler => exact (hk : False).elim
  | frame => exact (hk : False).elim
  | call => exact (hk : False).elim
  | bub U X hp =>
    obtain ⟨c', hc⟩ := PTL.rcr hp
    exact absurd hk (RCRPair.not_rigid hc)
  | trap => exact (hk : False).elim
  | throw => exact (hk : False).elim

/-- **Traps**: values before a trap in the source give a trap-active target. -/
theorem R.trap_inv {tl : Bool} {V : List Val} {rest y : List Admin}
    (h : R true tl (vals V ++ .trap :: rest) y) : TA y := by
  obtain ⟨V₀, V₁, y₀, rfl, rfl, hh⟩ := R.split rfl h
  cases hh with
  | same _ _ => exact TA.base _ _
  | rcr hc _ => exact (hc : False).elim
  | bub U X hp =>
    obtain ⟨c', hc⟩ := PTL.rcr hp
    exact (hc : False).elim
  | trap us x ht => exact TA.prefix ht V₀

/-- **Throws**: a throw in the source gives a throw-active target. -/
theorem R.throw_inv {tl : Bool} {V : List Val} {a : Nat} {rest y : List Admin}
    (h : R true tl (vals V ++ throwing a ++ rest) y) : TT a y := by
  rw [throw_eq] at h
  obtain ⟨V₀, V₁, y₀, hV, rfl, hh⟩ := R.split rfl h
  cases hh with
  | @same _ _ _ y' _ _ =>
    simp only [List.append_nil] at hV
    subst hV
    have := TT.base (a := a) V y'
    simpa [throwing, Val.toAdmin] using this
  | @instr i _ y' _ =>
    simp only [List.append_nil] at hV
    subst hV
    have hti : tailI .throwRef = [.throwRef] := by simp [Silmaril.Wasm.LimeCompile.Tail.tailI]
    rw [hti]
    have := TT.base (a := a) V y'
    simpa [throwing, Val.toAdmin] using this
  | rcr hc _ => exact (hc : False).elim
  | bub U X hp =>
    obtain ⟨c', hc⟩ := PTL.rcr hp
    exact (hc : False).elim
  | @throw _ e us x y' ht =>
    have : e = a := by
      have h2 := congrArg List.getLast? hV
      simp at h2; exact h2.symm
    subst this
    exact TT.prefix ht V₀

/-! ## Typing under nests -/

theorem CT_fill {s : Store H} {g : Frame} {X : List Admin} :
    ∀ N : NCtx, ContextTyped ⟨s, g, N.fill X⟩ → ContextTyped ⟨s, g, X⟩
  | .hole, h => h
  | .label V n cont N L, h => by
    have h' : ContextTyped ⟨s, g, vals V ++ [.label n cont (N.fill X)] ++ L⟩ := by
      simpa [NCtx.fill] using h
    exact CT_fill N (ContextTyped.label h')

end Silmaril.Raw.Wasm.LimeCompile.TailSim
