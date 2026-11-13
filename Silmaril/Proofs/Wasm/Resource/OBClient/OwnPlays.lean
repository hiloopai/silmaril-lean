module

public import Silmaril.Proofs.Wasm.Resource.OBClient.Own
public import Silmaril.Proofs.Wasm.Resource.OBClient.Plays

/-!
# Frees of owned handles: the protocol invariant

`OFIn`: what the ownership check with frees (`checkOF`) establishes. `JF`: the protocol invariant
of `I.dlts P I.store` for `(obSpec ρ).comap moveEvent`, with the held handles of the protocol
state as the live list of the held instance and the owned handles as the live list of the owned
instance. The held handles of a protocol state are distinct (`WF`), so a free removes the freed
handle from both lists (`heldL_release`, `ownedL_release`). `ofIn_sound`: the ownership sentence
over `wasmSem P`, every profile; `checkOF_sound`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.OBClient

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Client
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (CfgIn StoreIn RefIn Avoids isHost PlOK CallPl typed_refIn answer_refIn
  callout_mem decompose_toAdmin_none ifaceOp?_fst ifaceOp?_snd)

/-- **What the ownership check with frees establishes.** -/
structure OFIn (I : ScalarInstance) (G R : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat)
    (ρ : OBRoles (ifaceOf I)) : Prop where
  core : ClientCore I G fs ia iu if_ []
  bodiesO : BodiesC G (cfgO I.store fs ia iu if_) I.store.funcs
  role : ∀ j, (ρ.lend j || ρ.take j) = true → R (I.addr j) ∧
    (I.exports.get j).params.length = 1 ∧
    ∃ (fi : FuncInst Nat) (code : Func), I.store.funcs[I.addr j]? = some fi ∧
      fi.code = .wasm code ∧ fi.module.funcs = fs ∧
      (∀ i ∈ code.body, PlOK (CallPl G (isBadC I.store ia iu if_) fs) i) ∧
      okL (cfgOf I.store fs ia iu if_ []) fi.module.globals [.loc 0] .other code.body = true ∧
      okL (cfgO I.store fs ia iu if_) fi.module.globals
        (if (!ρ.lend j && ρ.take j) = true then [.loc 0] else []) .other code.body = true
  plain : ∀ j, (ρ.lend j || ρ.take j) = false → G (I.addr j)
  alloc : ∀ i : (ifaceOf I).Imp, ρ.alloc i = (i.val == ia)
  use : ∀ i : (ifaceOf I).Imp, ρ.use i = (i.val == iu)
  free : ∀ i : (ifaceOf I).Imp, ρ.free i = (i.val == if_)
  give : ∀ i : (ifaceOf I).Imp, ρ.give i = true → Avoids G I.store.funcs i.val

/-- The held handles of an ownership state are distinct. -/
def WF (L : List (Val × Mode)) : Prop := (heldL L).Nodup

section
variable {I : ScalarInstance} {G R : Nat → Prop} {fs : List Nat} {ia iu if_ : Nat}
  {ρ : OBRoles (ifaceOf I)}

/-- The invariant of a resumed thread. -/
def JRF (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat) :
    Option (List (Val × Mode)) → Config Nat → Prop
  | none, _ => True
  | some L, c => WF L ∧ InvAB I G fs ia iu if_ (heldL L) (ownedL L) c

/-- **The protocol invariant**: everything holds after an environment fault (`none`); otherwise
both instances hold of a running, guarded or entering thread. -/
def JF (I : ScalarInstance) (G R : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat)
    (ρ : OBRoles (ifaceOf I)) : Option (List (Val × Mode)) → I.HState → Prop
  | none, _ => True
  | some L, .idle s => WF L ∧ StoreIn G s ∧ s.funcs = I.store.funcs
  | some L, .running _ s t => WF L ∧
    (InvAB I G fs ia iu if_ (heldL L) (ownedL L) (t.config s) ∨
      GuardedAB I G fs ia iu if_ (heldL L) (ownedL L) (t.config s) ∨
      EntryF I G R fs ia iu if_ (heldL L) (ownedL L) s t) ∧ s.funcs = I.store.funcs
  | some L, .waiting _ s t e => s.funcs = I.store.funcs ∧
    ∀ (v : I.E.Ar e) (q' : Option (List (Val × Mode))),
      (πO I ρ).step (some L) (.inl (.ans e v)) = some q' →
      JRF I G fs ia iu if_ q'
        ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)).config s)

/-! ## Protocol lists -/

theorem wf_release {L : List (Val × Mode)} (hL : WF L) (h : Val) : WF (release L h) := by
  unfold WF
  rw [heldL_release hL]
  exact hL.erase h

theorem wf_cons {L : List (Val × Mode)} (hL : WF L) {h : Val} (hh : h ∉ heldL L) (m : Mode) :
    WF ((h, m) :: L) :=
  List.nodup_cons.2 ⟨hh, hL⟩

theorem wf_endCall {L : List (Val × Mode)} (hL : WF L) : WF (L.filter fun p => p.2 == .owned) :=
  (ownedL_sublist L).nodup hL

theorem ownedL_owned (L : List (Val × Mode)) (h : Val) :
    ownedL ((h, .owned) :: L) = h :: ownedL L := by
  simp [ownedL]

theorem ownedL_borrowed (L : List (Val × Mode)) (h : Val) :
    ownedL ((h, .borrowed) :: L) = ownedL L := by
  simp [ownedL]

theorem not_owned {L : List (Val × Mode)} {h : Val} (hh : h ∉ heldL L) : h ∉ ownedL L :=
  fun ho => hh ((ownedL_sublist L).subset ho)

/-! ## Vis steps -/

section Vis
variable {f : I.F.Op} {s : Store Nat} {t : Thread} {e : I.E.Op} {L : List (Val × Mode)}

/-- A callout of an invariant thread: another import, no handle event. -/
theorem visF_inv (hR : OFIn I G R fs ia iu if_ ρ) {h : Nat} {args : List Val}
    (callout : CalloutAt s t h args) (op : I.importOp? h args = some e) (hL : WF L)
    (hy : InvAB I G fs ia iu if_ (heldL L) (ownedL L) (t.config s))
    (hfy : s.funcs = I.store.funcs) :
    ∃ q', (πO I ρ).step (some L) (.inl (.ask e)) = some q' ∧
      JF I G R fs ia iu if_ ρ q' (.waiting f s t e) := by
  obtain ⟨a, fi, ha, hf, hcode⟩ := callout_mem callout hy.1.1
  have he : e.1.val = h := ifaceOp?_fst op
  have hne : ∀ i : Nat, Avoids G I.store.funcs i → e.1.val ≠ i :=
    fun i hav ei => hav a fi ha (hfy ▸ hf) (by rw [hcode, ← he, ei])
  have hu : ρ.use e.1 = false := (hR.use e.1).trans (by simpa using hne _ hR.core.avU)
  have hal : ρ.alloc e.1 = false := (hR.alloc e.1).trans (by simpa using hne _ hR.core.avA)
  have hfr : ρ.free e.1 = false := (hR.free e.1).trans (by simpa using hne _ hR.core.avF)
  have hfg : ∀ k, (ρ.free e.1 = true ∨ ρ.give e.1 = true) → OEv.ofArgs k e.2.1 = .skip := by
    intro k hk
    rcases hk with hk | hk
    · exact absurd hk (by rw [hfr]; exact Bool.false_ne_true)
    · exact absurd rfl (hne _ (hR.give e.1 hk))
  refine ⟨some L, stepO_ask_skip hu hfg, hfy, fun w q' hq' => ?_⟩
  rw [stepO_ans_skip w hal] at hq'
  cases hq'
  exact ⟨hL, resume_invAB hy _ (answer_refIn w)⟩

/-- A guarded use: the handle is held. -/
theorem visF_use (hR : OFIn I G R fs ia iu if_ ρ) {h : Nat} {E₀ E : Ctx} {a₀ b : Nat}
    {args : List Val} {v : Val} (op : I.importOp? h args = some e) (hfy : s.funcs = I.store.funcs)
    (hL : WF L) (hd₀ : decompose? s (t.config s).code = some (E₀, a₀, h, args))
    (hd : decompose? s (t.config s).code = some (E, b, iu, [v])) (hv : v ∈ heldL L)
    (hres : ∀ r, Client.RefsOK G r →
      InvAB I G fs ia iu if_ (heldL L) (ownedL L) ⟨s, (t.config s).frame, E.fill r.toAdmin⟩) :
    ∃ q', (πO I ρ).step (some L) (.inl (.ask e)) = some q' ∧
      JF I G R fs ia iu if_ ρ q' (.waiting f s t e) := by
  obtain ⟨hh, rfl⟩ := callout_eq' hd₀ hd
  have he : e.1.val = iu := (ifaceOp?_fst op).trans hh
  have hargs : e.2.1 = [v] := ifaceOp?_snd op
  have hu : ρ.use e.1 = true := (hR.use e.1).trans (by simp [he])
  have hal : ρ.alloc e.1 = false :=
    (hR.alloc e.1).trans (by simpa [he] using fun e' => hR.core.dAU e'.symm)
  have hstep : (πO I ρ).step (some L) (.inl (.ask e)) = some (some L) := by
    rw [stepO_ask, hu, ite_t rfl, hargs]
    simp [OEv.ofArgs, obStep, (held_iff L v).2 hv]
  refine ⟨some L, hstep, hfy, fun w q' hq' => ?_⟩
  rw [stepO_ans_skip w hal] at hq'
  cases hq'
  show JRF I G fs ia iu if_ (some L) _
  rw [resumeResult_config hd]
  exact ⟨hL, hres _ (answer_refIn w)⟩

/-- A guarded free: the handle is owned; it is released from both lists. -/
theorem visF_free (hR : OFIn I G R fs ia iu if_ ρ) {h : Nat} {E₀ E : Ctx} {a₀ b : Nat}
    {args : List Val} {v : Val} (op : I.importOp? h args = some e) (hfy : s.funcs = I.store.funcs)
    (hL : WF L) (hd₀ : decompose? s (t.config s).code = some (E₀, a₀, h, args))
    (hd : decompose? s (t.config s).code = some (E, b, if_, [v])) (hv : v ∈ ownedL L)
    (hres : ∀ r, Client.RefsOK G r → InvAB I G fs ia iu if_ ((heldL L).erase v)
      ((ownedL L).erase v) ⟨s, (t.config s).frame, E.fill r.toAdmin⟩) :
    ∃ q', (πO I ρ).step (some L) (.inl (.ask e)) = some q' ∧
      JF I G R fs ia iu if_ ρ q' (.waiting f s t e) := by
  obtain ⟨hh, rfl⟩ := callout_eq' hd₀ hd
  have he : e.1.val = if_ := (ifaceOp?_fst op).trans hh
  have hargs : e.2.1 = [v] := ifaceOp?_snd op
  have hu : ρ.use e.1 = false := (hR.use e.1).trans (by simpa [he] using hR.core.dUF.symm)
  have hfr : ρ.free e.1 = true := (hR.free e.1).trans (by simp [he])
  have hal : ρ.alloc e.1 = false :=
    (hR.alloc e.1).trans (by simpa [he] using fun e' => hR.core.dAF e'.symm)
  have hstep : (πO I ρ).step (some L) (.inl (.ask e)) = some (some (release L v)) := by
    rw [stepO_ask, hu, ite_f Bool.false_ne_true, hfr, ite_t rfl, hargs]
    simp [OEv.ofArgs, obStep, (owns_iff L v).2 hv]
  refine ⟨_, hstep, hfy, fun w q' hq' => ?_⟩
  rw [stepO_ans_skip w hal] at hq'
  cases hq'
  refine ⟨wf_release hL v, ?_⟩
  show InvAB I G fs ia iu if_ (heldL (release L v)) (ownedL (release L v)) _
  rw [resumeResult_config hd, heldL_release hL, ownedL_release hL]
  exact hres _ (answer_refIn w)

/-- The answer of an allocation adds an owned handle, unless the environment faults. -/
theorem visF_alloc_ans (hR : OFIn I G R fs ia iu if_ ρ) {E : Ctx} {b : Nat} (hL : WF L)
    (he : e.1.val = ia) (hd : decompose? s (t.config s).code = some (E, b, ia, []))
    (hres₁ : ∀ h, h ∉ heldL L → h ∉ ownedL L → Client.RefsOK G (.values [h]) →
      InvAB I G fs ia iu if_ (h :: heldL L) (h :: ownedL L)
        ⟨s, (t.config s).frame, E.fill (Result.values [h]).toAdmin⟩)
    (hres₂ : ∀ r, Client.RefsOK G r → (∀ ws, r ≠ .values ws) →
      InvAB I G fs ia iu if_ (heldL L) (ownedL L) ⟨s, (t.config s).frame, E.fill r.toAdmin⟩)
    (w : I.E.Ar e) (q' : Option (List (Val × Mode)))
    (hq' : (πO I ρ).step (some L) (.inl (.ans e w)) = some q') :
    JRF I G fs ia iu if_ q'
      ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) w)).config s) := by
  have hal : ρ.alloc e.1 = true := (hR.alloc e.1).trans (by simp [he])
  rw [stepO_ans, hal, ite_t rfl] at hq'
  rw [resumeResult_config hd]
  cases w with
  | values vs =>
    obtain ⟨ws, hws⟩ := vs
    have hres : (I.imports.get e.1).results.length = 1 := by
      have he' : e.1 = ⟨ia, he ▸ e.1.isLt⟩ := Fin.ext he
      rw [he']; exact (hR.core.arA _).2
    obtain ⟨h₁, rfl⟩ := List.length_eq_one_iff.1 ((List.Forall₂.length_eq hws).symm.trans hres)
    by_cases hh : h₁ ∈ heldL L
    · simp [Answer.toBehaviour, Answer.toResult, OEv.ofRes, obStep, (held_iff L h₁).2 hh] at hq'
      subst hq'; trivial
    · have hh' : held L h₁ = false := Bool.eq_false_iff.2 fun h' => hh ((held_iff L h₁).1 h')
      simp [Answer.toBehaviour, Answer.toResult, OEv.ofRes, obStep, hh'] at hq'
      subst hq'
      refine ⟨wf_cons hL hh _, ?_⟩
      rw [ownedL_owned]
      exact hres₁ h₁ hh (not_owned hh)
        (answer_refIn (Answer.values (ft := I.imports.get e.1) ⟨[h₁], hws⟩))
  | trap =>
    simp [Answer.toBehaviour, Answer.toResult, OEv.ofRes, obStep] at hq'
    subst hq'
    exact ⟨hL, hres₂ .trap (answer_refIn (Answer.trap (ft := I.imports.get e.1))) (fun _ => nofun)⟩
  | throw a =>
    simp [Answer.toBehaviour, Answer.toResult, OEv.ofRes, obStep] at hq'
    subst hq'
    exact ⟨hL, hres₂ (.throw a) (answer_refIn (Answer.throw (ft := I.imports.get e.1) a))
      (fun _ => nofun)⟩

/-- A guarded allocation: no event at the question. -/
theorem visF_alloc (hR : OFIn I G R fs ia iu if_ ρ) {h : Nat} {E₀ E : Ctx} {a₀ b : Nat}
    {args : List Val} (op : I.importOp? h args = some e) (hfy : s.funcs = I.store.funcs)
    (hL : WF L) (hd₀ : decompose? s (t.config s).code = some (E₀, a₀, h, args))
    (hd : decompose? s (t.config s).code = some (E, b, ia, []))
    (hres₁ : ∀ h, h ∉ heldL L → h ∉ ownedL L → Client.RefsOK G (.values [h]) →
      InvAB I G fs ia iu if_ (h :: heldL L) (h :: ownedL L)
        ⟨s, (t.config s).frame, E.fill (Result.values [h]).toAdmin⟩)
    (hres₂ : ∀ r, Client.RefsOK G r → (∀ ws, r ≠ .values ws) →
      InvAB I G fs ia iu if_ (heldL L) (ownedL L) ⟨s, (t.config s).frame, E.fill r.toAdmin⟩) :
    ∃ q', (πO I ρ).step (some L) (.inl (.ask e)) = some q' ∧
      JF I G R fs ia iu if_ ρ q' (.waiting f s t e) := by
  obtain ⟨hh, rfl⟩ := callout_eq' hd₀ hd
  have he : e.1.val = ia := (ifaceOp?_fst op).trans hh
  have hargs : e.2.1 = [] := ifaceOp?_snd op
  have hu : ρ.use e.1 = false := (hR.use e.1).trans (by simpa [he] using hR.core.dAU)
  have hfg : ∀ k, (ρ.free e.1 = true ∨ ρ.give e.1 = true) → OEv.ofArgs k e.2.1 = .skip :=
    fun k _ => by rw [hargs]; rfl
  exact ⟨some L, stepO_ask_skip hu hfg, hfy, visF_alloc_ans hR hL he hd hres₁ hres₂⟩

/-- A callout of a guarded thread: a use, a free or an allocation. -/
theorem visF_guard (hR : OFIn I G R fs ia iu if_ ρ) {h : Nat} {args : List Val}
    (callout : CalloutAt s t h args) (op : I.importOp? h args = some e) (hL : WF L)
    (hy : GuardedAB I G fs ia iu if_ (heldL L) (ownedL L) (t.config s))
    (hfy : s.funcs = I.store.funcs) :
    ∃ q', (πO I ρ).step (some L) (.inl (.ask e)) = some q' ∧
      JF I G R fs ia iu if_ ρ q' (.waiting f s t e) := by
  have hf₀ : (t.config s).store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hfy
  obtain ⟨E₀, a₀, hd₀⟩ := callout
  obtain ⟨E, b, ⟨v, hd, hv, hres⟩ | ⟨v, hd, hv, hres⟩ | ⟨hd, hres₁, hres₂⟩⟩ :=
    guardedAB_cases hR.core hf₀ hy
  · exact visF_use hR op hfy hL hd₀ (by simpa [Thread.config_store] using hd) hv
      (by simpa [Thread.config_store] using hres)
  · exact visF_free hR op hfy hL hd₀ (by simpa [Thread.config_store] using hd) hv
      (by simpa [Thread.config_store] using hres)
  · exact visF_alloc hR op hfy hL hd₀ (by simpa [Thread.config_store] using hd)
      (by simpa [Thread.config_store] using hres₁) (by simpa [Thread.config_store] using hres₂)

/-- A role export lends or hands over its argument and starts entering. -/
theorem visF_role (hR : OFIn I G R fs ia iu if_ ρ) (hs : StoreIn G s)
    (hfs : s.funcs = I.store.funcs) (hL : WF L) (hr : (ρ.lend f.1 || ρ.take f.1) = true) :
    ∃ q', (πO I ρ).step (some L) (.inr (.ask f)) = some q' ∧
      JF I G R fs ia iu if_ ρ q' (.running f s (I.initThread f)) := by
  obtain ⟨hR₁, hlen, fi', code, hfi', hcode, hm, hpl, hok, hokO⟩ := hR.role f.1 hr
  have hl : f.2.1.length = 1 := (List.Forall₂.length_eq f.2.2).symm.trans hlen
  obtain ⟨h, hh⟩ := List.length_eq_one_iff.1 hl
  obtain ⟨fi, hfi, hexp⟩ := hR.core.ok.export_type f.1
  obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
  have hentry : ∀ L' : List (Val × Mode), h ∈ heldL L' →
      ((!ρ.lend f.1 && ρ.take f.1) = true → h ∈ ownedL L') →
      EntryF I G R fs ia iu if_ (heldL L') (ownedL L') s (I.initThread f) := fun L' hL' hO =>
    ⟨I.addr f.1, h, _, fi, code, _, _, by simp [ScalarInstance.initThread, hh], hR₁, hL', hO, hs,
      fun r hr' => typed_refIn (G := G) f.2.2 r (by rw [hh]; exact hr'), hfs ▸ hfi, hcode, hexp,
      by simpa [Ty.length_ofList] using hlen.symm, hm, hpl, hok, hokO⟩
  have hcases : ∀ (k : Val → OEv Val) (m : Mode),
      (∀ L' : List (Val × Mode), obStep (some L') (k h) =
        if held L' h = true then some none else some (some ((h, m) :: L'))) →
      ((!ρ.lend f.1 && ρ.take f.1) = true → m = .owned) →
      ∃ q', obStep (some L) (OEv.ofArgs k f.2.1) = some q' ∧
        JF I G R fs ia iu if_ ρ q' (.running f s (I.initThread f)) := by
    intro k m hk hm
    rw [hh]
    show ∃ q', obStep (some L) (k h) = some q' ∧ _
    rw [hk]
    by_cases hb : held L h = true
    · exact ⟨none, by rw [ite_t hb], trivial⟩
    · have hn : h ∉ heldL L := fun h' => hb ((held_iff L h).2 h')
      refine ⟨some ((h, m) :: L), by rw [ite_f hb], wf_cons hL hn m,
        .inr (.inr (hentry _ (by simp [heldL]) fun ho => ?_)), hfs⟩
      rw [hm ho, ownedL_owned]
      exact List.mem_cons_self
  rw [stepO_call]
  by_cases hlend : ρ.lend f.1 = true
  · rw [ite_t hlend]
    exact hcases .lend .borrowed (fun _ => rfl) (fun ho => by simp [hlend] at ho)
  · have htake : ρ.take f.1 = true := by simpa [hlend] using hr
    rw [ite_f hlend, ite_t htake]
    exact hcases .take .owned (fun _ => rfl) (fun _ => rfl)

/-- An export call: a role export starts entering, another export is invoked. -/
theorem visF_call (hR : OFIn I G R fs ia iu if_ ρ) (hs : StoreIn G s)
    (hfs : s.funcs = I.store.funcs) (hL : WF L) :
    ∃ q', (πO I ρ).step (some L) (.inr (.ask f)) = some q' ∧
      JF I G R fs ia iu if_ ρ q' (.running f s (I.initThread f)) := by
  by_cases hr : (ρ.lend f.1 || ρ.take f.1) = true
  · exact visF_role hR hs hfs hL hr
  · have hr' : ρ.lend f.1 = false ∧ ρ.take f.1 = false := by simpa using hr
    refine ⟨some L, by rw [stepO_call, hr'.1, hr'.2]; rfl, hL, .inl ?_, hfs⟩
    exact invAB_invoke hs (hR.plain f.1 (by simpa using hr)) (typed_refIn f.2.2)

/-- A finished thread: the borrows end, the store invariant holds. -/
theorem visF_ret (hR : OFIn I G R fs ia iu if_ ρ) {r : Result} (final : ResultAt s t r)
    (hx : WF L ∧ (InvAB I G fs ia iu if_ (heldL L) (ownedL L) (t.config s) ∨
      GuardedAB I G fs ia iu if_ (heldL L) (ownedL L) (t.config s) ∨
      EntryF I G R fs ia iu if_ (heldL L) (ownedL L) s t) ∧ s.funcs = I.store.funcs) :
    WF (L.filter fun p => p.2 == .owned) ∧ StoreIn G s ∧ s.funcs = I.store.funcs := by
  obtain ⟨hL, hy | hy | hy, hfy⟩ := hx
  · exact ⟨wf_endCall hL, Thread.config_store s t ▸ hy.1.1.1, hfy⟩
  · have hf₀ : (t.config s).store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hfy
    obtain ⟨E, b, ⟨v, hd, -⟩ | ⟨v, hd, -⟩ | ⟨hd, -⟩⟩ := guardedAB_cases hR.core hf₀ hy <;>
      · rw [final, decompose_toAdmin_none] at hd
        cases hd
  · obtain ⟨a, h, -, -, -, -, -, rfl, -⟩ := hy
    exact absurd final (invoke_ne_result r)

end Vis

/-- The vis steps. -/
theorem jf_vis (hR : OFIn I G R fs ia iu if_ ρ) {P : Profile} {q : Option (List (Val × Mode))}
    {x y : I.HState} {o : Move I.E I.F} (hs : I.DTrans P x (some o) y)
    (hx : JF I G R fs ia iu if_ ρ q x) :
    ∃ q', (πO I ρ).step q o = some q' ∧ JF I G R fs ia iu if_ ρ q' y := by
  rcases q with _ | L
  · exact ⟨none, rfl, trivial⟩
  cases hs with
  | call s f => exact visF_call hR hx.2.1 hx.2.2 hx.1
  | ucall callout op =>
    obtain ⟨hL, hy | hy | hy, hfy⟩ := hx
    · exact visF_inv hR callout op hL hy hfy
    · exact visF_guard hR callout op hL hy hfy
    · exact absurd callout (entryF_no_callout hy)
  | uret v =>
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1
      (obSpec_oTotal ρ (some L) (.inl (.ans _ v)) trivial)
    exact ⟨q', hq', match q', hx.2 v _ hq' with
      | none, _ => trivial
      | some _, ⟨hL', hz⟩ => ⟨hL', .inl hz, hx.1⟩⟩
  | oret final answer => exact ⟨_, stepO_ret L _ _, visF_ret hR final hx⟩

/-- The silent steps. -/
theorem jf_tau (hR : OFIn I G R fs ia iu if_ ρ) {P : Profile} {q : Option (List (Val × Mode))}
    {x y : I.HState} (hst : I.DTrans P x none y) (hx : JF I G R fs ia iu if_ ρ q x) :
    JF I G R fs ia iu if_ ρ q y := by
  rcases q with _ | L
  · trivial
  cases hst with
  | @tau f s s' t t' h =>
    obtain ⟨hL, hy | hy | hy, hfy⟩ := hx
    · obtain ⟨f', code', ht', hstep⟩ := h
      have hf₀ : (t.config s).store.funcs = I.store.funcs := by
        rw [Thread.config_store]; exact hfy
      obtain ⟨hz, hfz⟩ := step_invAB hR.core hR.bodiesO hstep hf₀ hy
      subst ht'
      exact ⟨hL, hz.elim .inl (fun hg => .inr (.inl hg)), hfz.trans hf₀⟩
    · obtain ⟨hh, _, hc⟩ := guardedAB_callout hR.core hfy hy
      exact absurd h (calloutAt_no_internal hc _)
    · obtain ⟨hz, rfl⟩ := entryF_step hy h
      exact ⟨hL, .inl hz, hfy⟩

/-- **The protocol invariant of the instance's transition system** (every profile). -/
def ofLTSInv (hR : OFIn I G R fs ia iu if_ ρ) (P : Profile) :
    LTSInv (I.dlts P I.store) (πO I ρ) where
  J := JF I G R fs ia iu if_ ρ
  init := ⟨List.nodup_nil, hR.core.store, rfl⟩
  tau := fun hst hx => jf_tau hR hst hx
  vis := fun hst hx => jf_vis hR hst hx

/-- **Soundness of the ownership analysis with frees** (every profile): every play of the
instance is accepted by the ownership sentence. -/
theorem ofIn_accepts (hR : OFIn I G R fs ia iu if_ ρ) (P : Profile) :
    ∀ p ∈ I.strategy P I.store, (πO I ρ).Accepts p :=
  dlts_accepts (ofLTSInv hR P) (obSpec_oTotal ρ)

/-- **The ownership sentence over `wasmSem P`** (every profile). -/
theorem ofIn_sound (hR : OFIn I G R fs ia iu if_ ρ) (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode)))) (wasmSem P)
      (WasmProg.ofInstance I) (obSpec ρ) :=
  models_of_plays _ _ (ofIn_accepts hR P)

end

end Silmaril.Wasm.Resource.OBClient

/-! ## The checker -/

namespace Silmaril.Wasm.Resource.OBClient

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Client
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (instOf progOf instance? isInstance_instOf mem_storeFuncs_of rootsB_mem
  avoidsB_sound avoidsB Avoids PlOK CallPl isHost)

theorem funcOkO_sound {s : Store Nat} {fs : List Nat} {ia iu if_ : Nat} {F : List Fact} {a : Nat}
    (h : funcOkO s fs ia iu if_ F a = true) {fi : FuncInst Nat} {code : Func}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code) :
    okL (cfgO s fs ia iu if_) fi.module.globals F .other code.body = true := by
  simpa [funcOkO, hf, hcode] using h

theorem exportsOKF_at {I : ScalarInstance} {G : List Nat} {ia iu if_ : Nat} {ρ : NRoles}
    (h : exportsOKF I G ia iu if_ ρ = true) {j : Nat} (hj : j < I.exports.length) :
    (roleB ρ j = true → (I.exports[j]?.map (·.params.length)) = some 1 ∧
      funcOkE I.store (fsOf I) G ia iu if_ (I.addrs.getD j 0) = true ∧
      funcOkO I.store (fsOf I) ia iu if_ (entryO ρ j) (I.addrs.getD j 0) = true) ∧
    (roleB ρ j = false → I.addrs.getD j 0 ∈ G) := by
  have hj' := List.all_eq_true.1 h j (List.mem_range.2 hj)
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · simp only [hr, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hj'
    exact ⟨hj'.1.1, hj'.1.2, hj'.2⟩
  · simpa [hr] using hj'

theorem roleOKF_at {I : ScalarInstance} {G : List Nat} {ia iu if_ : Nat} {ρ : NRoles}
    (h : roleOKF I G ia iu if_ ρ = true) {i : Nat} (hi : i < I.imports.length) :
    ρ.alloc i = (i == ia) ∧ ρ.use i = (i == iu) ∧ ρ.free i = (i == if_) ∧
      (ρ.give i = true → avoidsB I.store G i = true) := by
  have hi' := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at hi'
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := hi'
  refine ⟨h₁, h₂, h₃, fun hg => ?_⟩
  rcases h₄ with h₄ | h₄
  · rw [h₄] at hg; cases hg
  · exact h₄

/-- The role exports of a checked instance. -/
theorem ofIn_role {I : ScalarInstance} {ia iu if_ : Nat} {ρ : NRoles}
    {G : List Nat} (hexp : exportsOKF I G ia iu if_ ρ = true) (j : (ifaceOf I).Exp)
    (hj : ((ρ.toOB : OBRoles (ifaceOf I)).lend j || (ρ.toOB : OBRoles (ifaceOf I)).take j) = true) :
    (I.addr j ∈ roleAddrs I ρ) ∧ (I.exports.get j).params.length = 1 ∧
    ∃ (fi : FuncInst Nat) (code : Func), I.store.funcs[I.addr j]? = some fi ∧
      fi.code = .wasm code ∧ fi.module.funcs = fsOf I ∧
      (∀ i ∈ code.body, PlOK (CallPl (· ∈ G) (isBadC I.store ia iu if_) (fsOf I)) i) ∧
      okL (cfgOf I.store (fsOf I) ia iu if_ []) fi.module.globals [.loc 0] .other
        code.body = true ∧
      okL (cfgO I.store (fsOf I) ia iu if_) fi.module.globals
        (if (!(ρ.toOB : OBRoles (ifaceOf I)).lend j && (ρ.toOB : OBRoles (ifaceOf I)).take j) = true
          then [.loc 0] else []) .other code.body = true := by
  have hjl : j.val < I.exports.length := j.isLt
  have hr : roleB ρ j.val = true := by simpa [roleB, NRoles.toOB] using hj
  obtain ⟨h₁, h₂, h₃⟩ := (exportsOKF_at hexp hjl).1 hr
  rw [List.getElem?_eq_getElem hjl, Option.map_some, Option.some.injEq] at h₁
  obtain ⟨fi, code, hfi, hcode, hm, hpl, hok⟩ := funcOkE_sound h₂
  have hokO := funcOkO_sound h₃ hfi hcode
  refine ⟨List.mem_map.2 ⟨j.val, List.mem_filter.2 ⟨List.mem_range.2 hjl, hr⟩, rfl⟩, h₁, fi, code,
    hfi, hcode, hm, hpl, hok, ?_⟩
  simpa [entryO, NRoles.toOB] using hokO

/-- **The checker establishes `OFIn`.** -/
theorem ofIn_of_checkOFInst {I : ScalarInstance} (hok : I.Ok) {ia iu if_ : Nat} {ρ : NRoles}
    (h : checkOFInst I ia iu if_ ρ = true) :
    OFIn I (· ∈ reachOF I ia iu if_ ρ) (· ∈ roleAddrs I ρ) (fsOf I) ia iu if_ ρ.toOB := by
  simp only [checkOFInst, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hAU, hAF⟩, hUF⟩, hia⟩, hiu⟩, hif⟩, haA⟩, hrA⟩, haU⟩, haF⟩, hfun⟩,
    hfunO⟩, hroots⟩, hvA⟩, hvU⟩, hvF⟩, hexp⟩, hrole⟩ := h
  have core : ClientCore I (· ∈ reachOF I ia iu if_ ρ) (fsOf I) ia iu if_ [] :=
    { ok := hok
      closed := fun a fi code ha hf hcode =>
        ⟨(funcOkC_sound (hfun a ha) hf hcode).1, (funcOkC_sound (hfun a ha) hf hcode).2.1⟩
      bodies := fun a fi code ha hf hcode => (funcOkC_sound (hfun a ha) hf hcode).2.2
      store := mem_storeFuncs_of (rootsB_mem hroots)
      avA := avoidsB_sound hvA
      avU := avoidsB_sound hvU
      avF := avoidsB_sound hvF
      pairs := by decide
      init := fun p hp => absurd hp (List.not_mem_nil)
      dAU := hAU
      dAF := hAF
      dUF := hUF
      arA := fun hi => ⟨arity_of haA hi, arity_res hrA hi⟩
      arU := fun hi => arity_of haU hi
      arF := fun hi => arity_of haF hi }
  refine ⟨core, fun a fi code ha hf hcode => funcOkO_sound (hfunO a ha) hf hcode,
    fun j hj => ofIn_role hexp j hj, fun j hj => ?_, fun i => (roleOKF_at hrole i.isLt).1,
    fun i => (roleOKF_at hrole i.isLt).2.1, fun i => (roleOKF_at hrole i.isLt).2.2.1,
    fun i hi => avoidsB_sound ((roleOKF_at hrole i.isLt).2.2.2 (by simpa [NRoles.toOB] using hi))⟩
  exact (exportsOKF_at hexp j.isLt).2 (by simpa [roleB, NRoles.toOB] using hj)

/-- **Soundness of the ownership checker with frees on a module** (every profile, no
determinism assumed). -/
theorem checkOF_sound {m : Module} {ia iu if_ : Nat} {ρ : NRoles}
    (h : checkOF m ia iu if_ ρ = true) (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode)))) (wasmSem P)
      (progOf m) (obSpec ρ.toOB) := by
  simp only [checkOF, Bool.and_eq_true] at h
  obtain ⟨mt, hI⟩ := isInstance_instOf h.1
  exact ofIn_sound (ofIn_of_checkOFInst hI.ok h.2) P

end Silmaril.Wasm.Resource.OBClient
