module

public import Silmaril.Proofs.Wasm.Game.Adequacy.RunTyping
public import Silmaril.Proofs.Wasm.Game.Strategy.Basic
public import Silmaril.Proofs.Wasm.Game.Machine.Basic

/-!
# Typing preservation along plays

The typing invariant `TypInv` on hidden states is preserved by every
transition whose environment answer throws only existing exceptions
(`TypInv.path`); hence well-formedness persists along complete activations
(`WellFormed.activation`). With no tags and no exception instances, an
instance never answers an export question with an exception
(`no_throw_of_no_tags`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Numerics

/-! ### Host-free steps never touch tags, and exceptions only through tags -/

theorem store_tag?_eq_none_of_nil {H : Type} {s : Store H} (h : s.tags = []) (f : Frame)
    (x : TagIdx) : s.tag? f x = none := by
  unfold Store.tag?
  rw [h]
  cases f.module.tags[x.toNat]? <;> simp

/-- A host-free Core step from a store without tags keeps the (empty) tags and the
exception instances. -/
theorem step_tags_nil {H : Type} {P : Profile} {c c' : Config H}
    (h : Step P (fun _ _ _ _ => False) c c') :
    c.store.tags = [] → c'.store.tags = [] ∧ c'.store.exns = c.store.exns := by
  induction h with
  | «variable» h => cases h <;> exact fun ht => ⟨ht, rfl⟩
  | table h => cases h <;> exact fun ht => ⟨ht, rfl⟩
  | memory h => cases h <;> exact fun ht => ⟨ht, rfl⟩
  | reference h => cases h <;> exact fun ht => ⟨ht, rfl⟩
  | aggregate h => cases h <;> exact fun ht => ⟨ht, rfl⟩
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | ctxtFrame _ ih => exact ih
  | callRefHost _ _ _ _ _ hhost => exact fun _ => hhost.elim
  | @throw s f x vs ta ti ts hta he hn =>
    intro ht
    rw [store_tag?_eq_none_of_nil (s := s) ht] at hta
    cases hta
  | _ => exact fun ht => ⟨ht, rfl⟩

theorem internal_tags_nil {P : Profile} {s s' : Store Nat} {t t' : Thread}
    (h : InternalP P (s, t) (s', t')) (ht : s.tags = []) : s'.tags = [] ∧ s'.exns = s.exns := by
  obtain ⟨f', code', -, hst⟩ := h
  have h2 := step_tags_nil hst
  rw [Thread.config_store] at h2
  exact h2 ht

theorem reach_tags_nil {P : Profile} {x y : Store Nat × Thread} (h : Reach P x y)
    (ht : x.1.tags = []) : y.1.tags = [] ∧ y.1.exns = x.1.exns := by
  induction h with
  | refl => exact ⟨ht, rfl⟩
  | @tail b c _ hst ih =>
    obtain ⟨hb, hbe⟩ := ih
    obtain ⟨sb, tb⟩ := b
    obtain ⟨sc, tc⟩ := c
    obtain ⟨hc, hce⟩ := internal_tags_nil hst hb
    exact ⟨hc, hce.trans hbe⟩

/-! ### Typing along host-free runs -/

/-- Host-free runs from a typed thread on a valid store stay typed, extend the store and
keep its function instances. -/
theorem reach_typed_extend {P : Profile} {ts : List CValType} {x y : Store Nat × Thread}
    (h : Reach P x y) (hs : StoreOk x.1) (ht : ThreadOk x.1 x.2 ts) :
    StoreOk y.1 ∧ ThreadOk y.1 y.2 ts ∧ Extend x.1 y.1 ∧ y.1.funcs = x.1.funcs := by
  induction h with
  | refl => exact ⟨hs, ht, Extend.refl hs, rfl⟩
  | @tail b c _ hst ih =>
    obtain ⟨hsb, htb, hext, hf⟩ := ih
    obtain ⟨sb, tb⟩ := b
    obtain ⟨sc, tc⟩ := c
    obtain ⟨hsc, htc, hext'⟩ := InternalP.preserves hsb htb hst
    exact ⟨hsc, htc, hext.trans hext', (InternalP.funcs_prefix hst).trans hf⟩

namespace ScalarInstance

variable {I : ScalarInstance}

theorem WellFormed.of_funcs_eq {s s' : Store Nat} (hw : I.WellFormed s) (hs : StoreOk s')
    (hf : s'.funcs = s.funcs) : I.WellFormed s' where
  storeOk := hs
  addrs_length := hw.addrs_length
  export_type j := by rw [hf]; exact hw.export_type j
  host_type a fi h ha hc := hw.host_type a fi h (by rw [← hf]; exact ha) hc

/-- The pending invocation of an export call is typed by the export's result types. -/
theorem WellFormed.initThread_ok {s : Store Nat} (hw : I.WellFormed s) (f : I.F.Op) :
    ThreadOk s (I.initThread f) ((I.exports.get f.1).results.map ScalarType.toC) := by
  obtain ⟨fi, hfi, hexp⟩ := hw.export_type f.1
  have hinv : InvokeOk s (I.addr f.1) f.2.1 := by
    refine ⟨fi, Ty.ofList ((I.exports.get f.1).params.map ScalarType.toC),
      Ty.ofList ((I.exports.get f.1).results.map ScalarType.toC), hfi, hexp, ?_⟩
    rw [Ty.toList_ofList]
    exact forall₂_valOk_of_hasVal s f.2.2
  obtain ⟨fi', ps, rs, hfi', hexp', hok⟩ := invoke_ok hw.storeOk hinv
  rw [hfi] at hfi'
  cases hfi'
  have heq := Expand.func_eq hexp' hexp
  simp only [FnType.toComp, Ty.func.injEq] at heq
  obtain ⟨-, rfl⟩ := heq
  rw [Ty.toList_ofList] at hok
  exact hok

theorem Answer.throwsBelow_mono {ft : FnType} {w : Answer ft}
    {n m : Nat} (h : Answer.ThrowsBelow n w) (hnm : n ≤ m) : Answer.ThrowsBelow m w := by
  cases w with
  | throw a => exact Nat.lt_of_lt_of_le h hnm
  | values vs => trivial
  | trap => trivial

/-- Resuming a typed callout with the typed Core result of an answer that throws only
existing exceptions gives a typed thread (store unchanged). -/
theorem resume_answer_typed (P : Profile) {s : Store Nat} {t : Thread} {ts : List CValType}
    {h : Nat} {args : List Val} {e : I.E.Op} (hw : I.WellFormed s) (ht : ThreadOk s t ts)
    (hc : CalloutAt s t h args) (hop : I.importOp? h args = some e) (v : I.E.Ar e)
    (hv : Answer.ThrowsBelow s.exns.length v) :
    ThreadOk s (resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)) ts := by
  have hop' : ifaceOp? I.imports h args = some e := hop
  have hstep : Step P (replayHost s h (Answer.toResult (ft := I.imports.get e.1) v))
      (t.config s) ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)).config s) :=
    calloutAt_step hc (Or.inr ⟨rfl, rfl, rfl⟩)
  have hok : HostOk (replayHost s h (Answer.toResult (ft := I.imports.get e.1) v)) := by
    refine replayHost_ok hw.storeOk fun fi hfi hcode ps rs hexp => ?_
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hfi
    obtain ⟨hlt, hexp'⟩ := hw.host_type n fi h hn hcode
    have hfin : (⟨h, hlt⟩ : Fin I.imports.length) = e.1 := Fin.ext (ifaceOp?_fst hop').symm
    rw [hfin] at hexp'
    have heq := Expand.func_eq hexp hexp'
    simp only [FnType.toComp, Ty.func.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    rw [Ty.toList_ofList]
    exact resultTyped_toResult hv (Nat.le_refl _)
  exact (Step.preservation hok ht hstep).1

variable (I) in
/-- The typing invariant on hidden states (see the module docstring). -/
def TypInv (n : Nat) : I.HState → Prop
  | .idle s => I.WellFormed s ∧ n ≤ s.exns.length
  | .running f s t => I.WellFormed s ∧ n ≤ s.exns.length ∧
      ThreadOk s t ((I.exports.get f.1).results.map ScalarType.toC)
  | .waiting f s t e => I.WellFormed s ∧ n ≤ s.exns.length ∧
      ThreadOk s t ((I.exports.get f.1).results.map ScalarType.toC) ∧
      ∃ h args, CalloutAt s t h args ∧ I.importOp? h args = some e

theorem TypInv.trans {P : Profile} {n : Nat} {q q' : I.HState} {m : Move I.E I.F}
    (ht : I.Trans P q m q') (hq : TypInv I n q)
    (hthrow : ∀ (e : I.E.Op) (v : I.E.Ar e), m = .inl (.ans e v) → Answer.ThrowsBelow n v) :
    TypInv I n q' := by
  cases ht with
  | call s f =>
    obtain ⟨hw, hn⟩ := hq
    exact ⟨hw, hn, WellFormed.initThread_ok hw f⟩
  | ucall run callout op =>
    obtain ⟨hw, hn, htt⟩ := hq
    obtain ⟨hs', ht', hext, hf⟩ := reach_typed_extend run hw.storeOk htt
    exact ⟨WellFormed.of_funcs_eq hw hs' hf, Nat.le_trans hn hext.exns.1, ht', _, _, callout, op⟩
  | @uret f s t e v =>
    obtain ⟨hw, hn, htt, h, args, hc, hop⟩ := hq
    exact ⟨hw, hn, resume_answer_typed P hw htt hc hop v
      (Answer.throwsBelow_mono (hthrow e v rfl) hn)⟩
  | oret run final answer =>
    obtain ⟨hw, hn, htt⟩ := hq
    obtain ⟨hs', -, hext, hf⟩ := reach_typed_extend run hw.storeOk htt
    exact ⟨WellFormed.of_funcs_eq hw hs' hf, Nat.le_trans hn hext.exns.1⟩

/-- The typing invariant along a path whose environment throws only exceptions below `n`. -/
theorem TypInv.path {P : Profile} {n : Nat} {q q' : I.HState}
    {p : List (Move I.E I.F)} (hp : I.Path P q p q') :
    TypInv I n q → (∀ (e : I.E.Op) (v : I.E.Ar e), (.inl (.ans e v) : Move I.E I.F) ∈ p →
      Answer.ThrowsBelow n v) → TypInv I n q' := by
  induction hp with
  | nil => exact fun hq _ => hq
  | cons ht _ ih =>
    intro hq hthrow
    refine ih (TypInv.trans ht hq fun e v hm => hthrow e v (by rw [hm]; exact List.mem_cons_self ..))
      fun e v hm => hthrow e v (List.mem_cons_of_mem _ hm)

/-! ### No exceptions without tags -/

/-- The store of a hidden state. -/
def HState.store : I.HState → Store Nat
  | .idle s => s
  | .running _ s _ => s
  | .waiting _ s _ _ => s

variable (I) in
/-- The typing invariant with no tags and no exception instances. -/
def NoTagInv (q : I.HState) : Prop :=
  TypInv I 0 q ∧ (HState.store q).tags = [] ∧ (HState.store q).exns = []

theorem NoTagInv.trans {P : Profile} {q q' : I.HState} {m : Move I.E I.F}
    (ht : I.Trans P q m q') (hq : NoTagInv I q)
    (hthrow : ∀ (e : I.E.Op) (v : I.E.Ar e), m = .inl (.ans e v) → Answer.ThrowsBelow 0 v) :
    NoTagInv I q' := by
  refine ⟨TypInv.trans ht hq.1 hthrow, ?_⟩
  obtain ⟨-, htg, hex⟩ := hq
  cases ht with
  | call s f => exact ⟨htg, hex⟩
  | ucall run callout op =>
    obtain ⟨h1, h2⟩ := reach_tags_nil run htg
    exact ⟨h1, h2.trans hex⟩
  | uret v => exact ⟨htg, hex⟩
  | oret run final answer =>
    obtain ⟨h1, h2⟩ := reach_tags_nil run htg
    exact ⟨h1, h2.trans hex⟩

/-- Under the invariant, a transition never answers an export call with an exception. -/
theorem NoTagInv.trans_ne_throw {P : Profile} {q q' : I.HState} {m : Move I.E I.F}
    (ht : I.Trans P q m q') (hq : NoTagInv I q) (f : I.F.Op) (a : Nat) :
    m ≠ .inr (.ans f (.throw a)) := by
  cases ht with
  | @oret f₀ s₀ s₁ t₀ t₁ r v run final answer =>
    show (Sum.inr (Ev.ans f₀ v) : Move I.E I.F) ≠ .inr (.ans f (.throw a))
    intro hm
    obtain ⟨⟨hw, -, htt⟩, htg, hex⟩ := hq
    obtain ⟨-, ht', -, -⟩ := reach_typed_extend run hw.storeOk htt
    have hex0 : s₀.exns = [] := hex
    have hex1 : s₁.exns = s₀.exns := (reach_tags_nil run htg).2
    cases hm
    have hr : r = Result.throw a := (Answer.toResult_of_ofResult? answer).symm
    have hcode : (t₁.config s₁).code = Result.toAdmin (.throw a) := hr ▸ final
    obtain ⟨C, -, hadm⟩ := ht'
    have hmem : Admin.ref (.exn a) ∈ (t₁.config s₁).code := by simp [hcode, Result.toAdmin]
    obtain ⟨e, he⟩ := AdminsOk.exn_existsExn (a := a) hadm hmem
    have hnil : (t₁.config s₁).store.exns = [] := by rw [Thread.config_store, hex1, hex0]
    exact absurd he (by simp [hnil])
  | call s f' => intro hm; cases hm
  | ucall run callout op => intro hm; cases hm
  | uret v => intro hm; cases hm

theorem NoTagInv.path_no_throw {P : Profile} {q q' : I.HState}
    {p : List (Move I.E I.F)} (hp : I.Path P q p q') :
    NoTagInv I q → (∀ (e : I.E.Op) (v : I.E.Ar e), (.inl (.ans e v) : Move I.E I.F) ∈ p →
      Answer.ThrowsBelow 0 v) → ∀ (f : I.F.Op) (a : Nat),
      (.inr (.ans f (.throw a)) : Move I.E I.F) ∉ p := by
  induction hp with
  | nil => intro _ _ f a h; simp at h
  | @cons q₁ q₂ q₃ m p ht _ ih =>
    intro hq hthrow f a h
    have hthrow' : ∀ (e : I.E.Op) (v : I.E.Ar e), m = .inl (.ans e v) → Answer.ThrowsBelow 0 v :=
      fun e v hm => hthrow e v (by rw [hm]; exact List.mem_cons_self ..)
    rcases List.mem_cons.mp h with h | h
    · exact NoTagInv.trans_ne_throw ht hq f a h.symm
    · exact ih (NoTagInv.trans ht hq hthrow') (fun e v hm => hthrow e v (List.mem_cons_of_mem _ hm))
        f a h

end ScalarInstance

namespace ScalarInstance

variable {I : ScalarInstance}

/-- **Typing preservation.** Well-formedness is preserved by a complete activation whose
environment throws only existing exceptions; the exception heap only grows. -/
theorem WellFormed.activation {P : Profile} {s s' : Store Nat}
    {c : List (Move I.E I.F)} (hw : I.WellFormed s)
    (hthrow : I.PlayThrowsBelow s.exns.length c) (hc : I.Activation P s c s') :
    I.WellFormed s' ∧ s.exns.length ≤ s'.exns.length :=
  TypInv.path (n := s.exns.length) hc ⟨hw, Nat.le_refl _⟩ hthrow

/-- Typing preservation along any number of activations. -/
theorem WellFormed.path {P : Profile} {s s' : Store Nat}
    {p : List (Move I.E I.F)} (hw : I.WellFormed s)
    (hthrow : I.PlayThrowsBelow s.exns.length p) (hp : I.Path P (.idle s) p (.idle s')) :
    I.WellFormed s' ∧ s.exns.length ≤ s'.exns.length :=
  TypInv.path (n := s.exns.length) hp ⟨hw, Nat.le_refl _⟩ hthrow

/-- **No exceptions without tags.** From a well-formed store with no tags and no exception
instances, against an environment that never throws, the instance never answers an export
call with `throw a`. -/
theorem no_throw_of_no_tags {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (htags : s.tags = []) (hexns : s.exns = []) {p : List (Move I.E I.F)}
    (hp : p ∈ I.plays P s) (henv : I.PlayThrowsBelow 0 p) (f : I.F.Op) (a : Nat) :
    (.inr (.ans f (.throw a)) : Move I.E I.F) ∉ p := by
  obtain ⟨q, hq⟩ := hp
  exact NoTagInv.path_no_throw hq ⟨⟨hw, Nat.zero_le _⟩, htags, hexns⟩ henv f a

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
