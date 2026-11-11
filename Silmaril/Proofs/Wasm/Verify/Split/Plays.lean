module

public import Silmaril.Proofs.Wasm.Verify.Split.Step

/-!
# Per-export reachability: the plays of a scalar instance

`SplitIn I V Cs fs` collects what the per-export analysis establishes about an instance `I`:
a set `V` of escaping functions holding every reference of the store, and for every export `j`
a set `Cs j` of callable functions, closed for `PlVC V (Cs j) fs` (callees in `Cs j`, `ref.func`
targets in `V`), containing `V` and the export's function.

Along every path of the instance's transition system the hidden state satisfies `SplitInv`: between
activations the store holds references into `V`; during an activation of export `j` the thread
satisfies the reachability invariant at `Cs j` (`CfgIn`) and the escaping-reference invariant
`VIn V` (`trans_sInv`, `path_sInv`). The export whose call is pending is the export of the
hidden state (`stExp`, `stExp_trans`), so an import question asked while export `e` is active
comes from a thread invariant at `Cs e`, hence is not of an import that `Cs e` avoids
(`neverCallFrom_of_splitIn`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {V C : Nat → Prop} {fs : List Nat}

/-! ## Host-free runs and answers -/

theorem hostIn_noHost' : HostIn V (Det.noHost : HostSemantics Nat) :=
  fun _ _ _ _ _ h => h.elim

/-- The two invariants of a thread. -/
def TInv (V C : Nat → Prop) (fs : List Nat) (c : Config Nat) : Prop :=
  CfgIn C fs (PlVC V C fs) c ∧ VIn V false c

theorem internalP_tInv {P : Profile} {x y : Store Nat × Thread} (h : InternalP P x y)
    (hcl : FuncsClosed C fs (PlVC V C fs) x.1.funcs) (hc : TInv V C fs (x.2.config x.1)) :
    TInv V C fs (y.2.config y.1) ∧ y.1.funcs = x.1.funcs := by
  obtain ⟨f', code', hy, hst⟩ := h
  have hcl' : FuncsClosed C fs (PlVC V C fs) (x.2.config x.1).store.funcs := by
    rw [Thread.config_store]; exact hcl
  have hs : CfgIn C fs (PlVC V C fs) ⟨y.1, f', code'⟩ ∧
      y.1.funcs = (x.2.config x.1).store.funcs :=
    Step.cfgIn_of_empty plVC_plainOK hostIn_noHost hst hcl' hc.1
  have hv : VIn V false ⟨y.1, f', code'⟩ := Step.vIn hostIn_noHost' hst hc.1 hc.2
  rw [Thread.config_store] at hs
  rw [hy]
  exact ⟨⟨hs.1, hv⟩, hs.2⟩

/-- **Host-free runs preserve both invariants** (every profile). -/
theorem reach_tInv {P : Profile} {x y : Store Nat × Thread} (h : Reach P x y)
    (hcl : FuncsClosed C fs (PlVC V C fs) x.1.funcs) (hc : TInv V C fs (x.2.config x.1)) :
    TInv V C fs (y.2.config y.1) ∧ y.1.funcs = x.1.funcs := by
  induction h with
  | refl => exact ⟨hc, rfl⟩
  | tail _ hst ih =>
    obtain ⟨hc', hf'⟩ := ih
    obtain ⟨hc'', hf''⟩ := internalP_tInv hst (hf' ▸ hcl) hc'
    exact ⟨hc'', hf''.trans hf'⟩

/-- **Resuming a thread with a scalar answer keeps the escaping-reference invariant.** -/
theorem resume_vIn {s : Store Nat} {t : Thread} {r : Result} (hc : VIn V false (t.config s))
    (hr : ∀ x ∈ codeRefs r.toAdmin, RefIn V x) : VIn V false ((resumeResult s t r).config s) := by
  rcases hd : decompose? s (t.config s).code with _ | ⟨E, a, h, args⟩
  · have ht : resumeResult s t r = t := by unfold resumeResult; simp only [hd]
    rw [ht]; exact hc
  · rw [resumeResult_config hd]
    obtain ⟨_, _, _, _, _, _, _, _, _, hfill⟩ := decompose?_sound hd
    have hs : (t.config s).store = s := Thread.config_store s t
    have hcode : LooseIn V false (E.fill _) := hfill ▸ hc.2.2
    have hY : LooseIn V false r.toAdmin :=
      looseIn_of_codeIn (CodeIn.toAdmin (fs := []) (Pl := fun _ => True) hr) false
    exact ⟨hs ▸ hc.1, hc.2.1, LooseIn.fill (fun b => nextCall_vals_append rfl _) hY E hcode⟩

/-- The `$invoke` configuration of an export call. -/
theorem invoke_tInv {s : Store Nat} (hs : StoreIn V s) (hVC : ∀ a, V a → C a) {a : Nat}
    (ha : C a) {args : List Val} (hargs : ∀ r, Val.ref r ∈ args → RefIn V r) :
    TInv V C fs (invoke s a args) :=
  ⟨invoke_cfgIn (hs.mono hVC) ha fun r hr => (hargs r hr).mono hVC,
    hs, fun r hr => by simp [invoke] at hr,
    LooseIn.vals_append hargs (by simp [callAdm])⟩

/-! ## The instance -/

/-- What the per-export analysis establishes about an instance: the escaping set `V` holds every
reference of the store; each export `j` has a callable set `Cs j`, closed for
`PlVC V (Cs j) fs`, containing `V` and the export's function. -/
structure SplitIn (I : ScalarInstance) (V : Nat → Prop) (Cs : Fin I.exports.length → Nat → Prop)
    (fs : List Nat) : Prop where
  closed : ∀ j, FuncsClosed (Cs j) fs (PlVC V (Cs j) fs) I.store.funcs
  store : StoreIn V I.store
  sub : ∀ j a, V a → Cs j a
  exports : ∀ j, Cs j (I.addr j)

/-- The invariant of the hidden states. -/
def SplitInv (I : ScalarInstance) (V : Nat → Prop) (Cs : Fin I.exports.length → Nat → Prop)
    (fs : List Nat) : I.HState → Prop
  | .idle s => StoreIn V s ∧ s.funcs = I.store.funcs
  | .running f s t => TInv V (Cs f.1) fs (t.config s) ∧ s.funcs = I.store.funcs
  | .waiting f s t _ => TInv V (Cs f.1) fs (t.config s) ∧ s.funcs = I.store.funcs

/-- The export whose call is pending in a hidden state. -/
def stExp {I : ScalarInstance} : I.HState → Option (ifaceOf I).Exp
  | .idle _ => none
  | .running f _ _ => some f.1
  | .waiting f _ _ _ => some f.1

section
variable {I : ScalarInstance} {Cs : Fin I.exports.length → Nat → Prop}

/-- **The pending export follows the moves**: `activeStep` of the move's event. -/
theorem stExp_trans {P : Profile} {q q' : I.HState} {m : Move I.E I.F} (h : I.Trans P q m q') :
    activeStep (X := ifaceOf I) (stExp q) (moveEvent m) = stExp q' := by
  cases h <;> rfl

theorem stExp_path {P : Profile} {q q' : I.HState} {p : List (Move I.E I.F)}
    (h : I.Path P q p q') :
    (p.map (moveEvent (X := ifaceOf I))).foldl activeStep (stExp q) = stExp q' := by
  induction h with
  | nil => rfl
  | cons ht _ ih =>
    show List.foldl activeStep (activeStep (stExp _) (moveEvent _)) _ = _
    rw [stExp_trans ht]
    exact ih

theorem path_split {P : Profile} {q q' : I.HState} {p₁ p₂ : List (Move I.E I.F)}
    {m : Move I.E I.F} (h : I.Path P q (p₁ ++ m :: p₂) q') :
    ∃ q₁ q₂, I.Path P q p₁ q₁ ∧ I.Trans P q₁ m q₂ := by
  induction p₁ generalizing q with
  | nil =>
    cases h with
    | cons ht _ => exact ⟨q, _, .nil _, ht⟩
  | cons m₀ p₁ ih =>
    cases h with
    | cons ht hp =>
      obtain ⟨q₁, q₂, h₁, h₂⟩ := ih hp
      exact ⟨q₁, q₂, .cons ht h₁, h₂⟩

theorem trans_ucall_split {P : Profile} {f : I.F.Op} {s s' : Store Nat} {t t' : Thread} {h : Nat}
    {args : List Val} {e : I.E.Op} (hS : SplitIn I V Cs fs) (run : Reach P (s, t) (s', t'))
    (callout : CalloutAt s' t' h args) (op : I.importOp? h args = some e)
    (hq : SplitInv I V Cs fs (.running f s t)) :
    SplitInv I V Cs fs (.waiting f s' t' e) ∧
      ∀ i, Avoids (Cs f.1) I.store.funcs i → e.1.val ≠ i := by
  have hcl : FuncsClosed (Cs f.1) fs (PlVC V (Cs f.1) fs) s.funcs := hq.2 ▸ hS.closed f.1
  have hr : TInv V (Cs f.1) fs (t'.config s') ∧ s'.funcs = s.funcs := reach_tInv run hcl hq.1
  refine ⟨⟨hr.1, hr.2.trans hq.2⟩, fun i hav => ?_⟩
  have hav' : Avoids (Cs f.1) s'.funcs i := by rw [hr.2, hq.2]; exact hav
  exact (ifaceOp?_fst op).symm ▸ callout_ne callout hr.1.1 hav'

theorem trans_oret_split {P : Profile} {f : I.F.Op} {s s' : Store Nat} {t t' : Thread}
    (hS : SplitIn I V Cs fs) (run : Reach P (s, t) (s', t'))
    (hq : SplitInv I V Cs fs (.running f s t)) : SplitInv I V Cs fs (.idle s') := by
  have hcl : FuncsClosed (Cs f.1) fs (PlVC V (Cs f.1) fs) s.funcs := hq.2 ▸ hS.closed f.1
  have hr : TInv V (Cs f.1) fs (t'.config s') ∧ s'.funcs = s.funcs := reach_tInv run hcl hq.1
  exact ⟨Thread.config_store s' t' ▸ hr.1.2.1, hr.2.trans hq.2⟩

/-- **One transition keeps the invariant**; an import question asked during an activation of
export `j` is a callout of a thread invariant at `Cs j`. -/
theorem trans_sInv {P : Profile} {q q' : I.HState} {m : Move I.E I.F} (h : I.Trans P q m q')
    (hS : SplitIn I V Cs fs) (hq : SplitInv I V Cs fs q) :
    SplitInv I V Cs fs q' ∧ ∀ e (j : (ifaceOf I).Exp), m = .inl (.ask e) → stExp q = some j →
      ∀ i, Avoids (Cs j) I.store.funcs i → e.1.val ≠ i := by
  cases h with
  | call s f =>
    exact ⟨⟨invoke_tInv hq.1 (hS.sub f.1) (hS.exports f.1) (typed_refIn f.2.2), hq.2⟩,
      fun _ _ he => by cases he⟩
  | ucall run callout op =>
    exact ⟨(trans_ucall_split hS run callout op hq).1, fun e' j he hj => by
      cases he; cases hj; exact (trans_ucall_split hS run callout op hq).2⟩
  | uret v =>
    exact ⟨⟨⟨resume_cfgIn hq.1.1 (answer_refIn v), resume_vIn hq.1.2 (answer_refIn v)⟩, hq.2⟩,
      fun _ _ he => by cases he⟩
  | oret run final answer => exact ⟨trans_oret_split hS run hq, fun _ _ he => by cases he⟩

theorem path_sInv {P : Profile} {q q' : I.HState} {p : List (Move I.E I.F)}
    (h : I.Path P q p q') (hS : SplitIn I V Cs fs) (hq : SplitInv I V Cs fs q) :
    SplitInv I V Cs fs q' := by
  induction h with
  | nil => exact hq
  | cons ht _ ih => exact ih (trans_sInv ht hS hq).1

/-- **No play asks import `i` while export `e` is active** (every profile), when `Cs e` avoids
`i`. -/
theorem strategy_no_icall_from (hS : SplitIn I V Cs fs) {e : (ifaceOf I).Exp} {i : Nat}
    (hav : Avoids (Cs e) I.store.funcs i) (P : Profile) {p₁ p₂ : List (Move I.E I.F)}
    {m : Move I.E I.F} (hp : p₁ ++ m :: p₂ ∈ I.strategy P I.store) (e' : I.E.Op)
    (hm : m = .inl (.ask e')) (hact : activeExport (p₁.map (moveEvent (X := ifaceOf I))) = some e) :
    e'.1.val ≠ i := by
  obtain ⟨q', hpath⟩ := ScalarInstance.mem_strategy_iff.1 hp
  obtain ⟨q₁, q₂, h₁, h₂⟩ := path_split hpath
  have hq₁ : SplitInv I V Cs fs q₁ := path_sInv h₁ hS ⟨hS.store, rfl⟩
  have hst : stExp q₁ = some e := by
    rw [← stExp_path h₁]
    exact hact
  exact (trans_sInv h₂ hS hq₁).2 e' e hm hst i hav

end

/-- **Soundness of per-export reachability for "never calls import `i` from export `e`"**
(every profile): the Wasm program of an instance satisfying `SplitIn`, with the callable set of
export `e` avoiding import `i`, never calls `i` while `e` is active. -/
theorem neverCallFrom_of_splitIn {I : ScalarInstance} {Cs : Fin I.exports.length → Nat → Prop}
    (hS : SplitIn I V Cs fs) {i : (ifaceOf I).Imp} {e : (ifaceOf I).Exp}
    (hav : Avoids (Cs e) I.store.funcs i.val) (P : Profile) :
    Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) (WasmProg.ofInstance I)
      (i, e) := by
  rw [models_iff]
  rintro t ⟨q, hq, rfl⟩ h ev r hr a hev hact
  obtain ⟨l₁, l₂, rfl, rfl, hl₂⟩ := List.map_eq_append_iff.1 hr
  obtain ⟨m, l₂', rfl, hm, -⟩ := List.map_eq_cons_iff.1 hl₂
  obtain ⟨e', hei, rfl⟩ := moveEvent_icall (hm.trans hev)
  exact strategy_no_icall_from hS hav P hq e' rfl hact (by rw [hei])

end Silmaril.Wasm.Verify
