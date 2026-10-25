module

public import Silmaril.Wasm.Execution.Core.Soundness.PresBasic
public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux
public import Silmaril.Wasm.Execution.Core.Soundness.PresBranch
public import Silmaril.Wasm.Execution.Core.Soundness.PresBrCast
public import Silmaril.Wasm.Execution.Core.Soundness.Aggregate
public import Silmaril.Wasm.Execution.Core.Soundness.PresWireCall
public import Silmaril.Wasm.Execution.Core.Soundness.PresWireCtl
public import Silmaril.Wasm.Execution.Core.Soundness.PresWireFrame
public import Silmaril.Wasm.Execution.Core.Soundness.PresWireCatch
public import Silmaril.Wasm.Execution.Core.Soundness.PresWireExn
public import Silmaril.Wasm.Execution.Core.Soundness.PresWireCallRef
public import Silmaril.Wasm.Execution.Core.Soundness.PresDivergent

@[expose] public section

/-! # Preservation (subject reduction) for Core 3.0

Induction on `Step`: the delegated families use `<Family>Step.preservation`
(`Soundness/<Family>.lean`); the control, context, call, exception and
trap rules, and the variable family (`local.set` changes the frame and the
initialisation status of a local), are proved here.

## The generalised invariant (`Soundness/PresBasic.lean`)

`Step.preservation` is a corollary of `Step.preservation_gen`, which types the
code of a configuration in a *typing context* `Ct` related to the *frame context*
`Cf` (the context `Frame_ok` assigns to the current frame) by `CtxUnder Ct Cf`:

* `Ct` agrees with `Cf` except on `LOCALS`, `LABELS` and `RETURN`;
* the locals of `Ct` are pointwise `≤` those of `Cf` (`LocalsLe`): same types, and
  a local set in `Ct` is set in `Cf` (the frame may have initialised more).

A step may change the frame (`local.set`), so the conclusion produces a new frame
context `Cf'` (differing from `Cf` only in its locals) and a new typing context
`Ct'` with `CtxLe Ct Ct'` (more locals set).

The delegated families are typed in the frame context itself: their redexes and
reducts contain no control instruction (`AllFlat`), so their typing moves
between `Ct` and `Cf` by `AdminsOk.relabel` and `AdminsOk.weaken`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Helpers -/

@[simp] theorem constAddr_flat (a : AddrType) (n : Nat) : (constAddr a n).flat = true := by
  cases a <;> rfl

@[simp] theorem Admin.flat_plain (i : Instr) : (Admin.plain i).flat = i.flat := rfl
@[simp] theorem Admin.flat_ref (r : Ref) : (Admin.ref r).flat = true := rfl
@[simp] theorem Admin.flat_trap : (Admin.trap).flat = true := rfl

@[simp] theorem allFlat_map_ref (rs : List Ref) : (rs.map Admin.ref).all Admin.flat = true := by
  simp

theorem ParametricStep.allFlat {is is' : List Admin} (h : ParametricStep is is') :
    AllFlat is ∧ AllFlat is' := by
  cases h <;> simp [AllFlat, Instr.flat]

theorem NumericStep.allFlat {P : Profile} {is is' : List Admin} (h : NumericStep P is is') :
    AllFlat is ∧ AllFlat is' := by
  cases h <;> simp [AllFlat, Instr.flat]

theorem VectorStep.allFlat {P : Profile} {is is' : List Admin} (h : VectorStep P is is') :
    AllFlat is ∧ AllFlat is' := by
  cases h <;> simp [AllFlat, Instr.flat]

theorem TableStep.allFlat {P : Profile} {c c' : Config H} (h : TableStep P c c') :
    AllFlat c.code ∧ AllFlat c'.code := by
  cases h <;> simp [AllFlat, Instr.flat]

theorem MemoryStep.allFlat {P : Profile} {c c' : Config H} (h : MemoryStep P c c') :
    AllFlat c.code ∧ AllFlat c'.code := by
  cases h <;> simp [AllFlat, Instr.flat, store8, load8u]

theorem RefStep.allFlat {c c' : Config H} (h : RefStep c c') :
    AllFlat c.code ∧ AllFlat c'.code := by
  cases h <;> simp [AllFlat, Instr.flat]

theorem AggregateStep.allFlat {c c' : Config H} (h : AggregateStep c c') :
    AllFlat c.code ∧ AllFlat c'.code := by
  cases h <;> simp [AllFlat, Instr.flat]
  intro x hx
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  rfl

/-- The code of a configuration that steps is not empty. -/
theorem Step.code_ne_nil {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') : c.code ≠ [] := by
  induction h with
  | parametric h => cases h <;> simp
  | numeric h => cases h <;> simp
  | vector h => cases h <;> simp
  | «variable» h => cases h <;> simp
  | table h => cases h <;> simp
  | memory h => cases h <;> simp
  | reference h => cases h <;> simp
  | aggregate h => cases h <;> simp
  | ctxtInstrs _ _ ih =>
    exact fun h => ih (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).2
  | _ => simp

theorem CtxLe.initLocals_of {C C' : Context} (h : CtxLe C C') {xs ys : List Nat}
    (hL : LocalsLe (C.initLocals xs).locals (C.initLocals ys).locals) :
    CtxLe (C.initLocals xs) (C'.initLocals ys) := by
  refine ⟨?_, hL.trans (LocalsLe.initLocals h.le ys)⟩
  have e1 := C'.initLocals_eq_with ys
  have e2 := C.initLocals_eq_with xs
  generalize C'.initLocals ys = D' at e1 ⊢
  generalize C.initLocals xs = D at e2 ⊢
  rw [e1, e2]
  have e3 := h.eq
  generalize C'.locals = L' at e3
  subst e3
  rfl

theorem CtxLe.withLabel_inv {C D : Context} {t : List CValType} (h : CtxLe (C.withLabel t) D) :
    D = ({ C with locals := D.locals } : Context).withLabel t ∧
      CtxLe C { C with locals := D.locals } := by
  obtain ⟨e, hl⟩ := h
  refine ⟨?_, ⟨rfl, hl⟩⟩
  generalize D.locals = L at e ⊢
  subst e
  rfl

theorem CtxUnder.shift {Ct Cf Cf' : Context} (hu : CtxUnder Ct Cf)
    (hCf' : Cf' = Cf.reshape Cf'.locals Cf.labels Cf.return_) {L : List LocalType}
    (hL : LocalsLe L Cf'.locals) : CtxUnder { Ct with locals := L } Cf' := by
  refine ⟨?_, hL⟩
  generalize Cf'.locals = L' at hCf' hL
  subst hCf'
  have e := hu.reshape_eq L Ct.labels Ct.return_
  show Ct.reshape L Ct.labels Ct.return_ = _
  rw [e]

theorem CtxUnder.toCtxLe {Ct Cf : Context} (hu : CtxUnder Ct Cf) (hl : Ct.labels = Cf.labels)
    (hr : Ct.return_ = Cf.return_) : CtxLe Ct Cf := by
  refine ⟨?_, hu.le⟩
  have e := hu.reshape_eq Cf.locals Ct.labels Ct.return_
  show Cf = Ct.reshape Cf.locals Ct.labels Ct.return_
  rw [e, hl, hr]

theorem CtxLe.catchOk {C C' : Context} (h : CtxLe C C') {c : Catch} (hc : CatchOk C c) :
    CatchOk C' c := by
  have := CatchOk.mono (L := C'.locals) (r := C.return_) hc
  rw [h.eq]; exact this

/-! ## Context rules -/

section ctxt

variable {P : Profile} {host : HostSemantics H}

/-- The inductive hypothesis of `Step.preservation_gen` for a step `c ~> c'`. -/
abbrev PresIH (c c' : Config H) : Prop :=
  ∀ {Cf Ct : Context} {it : InstrType}, StoreOk c.store → FrameOk c.store c.frame Cf →
    CtxUnder Ct Cf → CtxWf Ct → StoreTypesOk c.store → AdminsOk c.store Ct c.code it →
    PresConcl c c' Cf Ct it

theorem pres_ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hne' : is ≠ []) (ih : PresIH (H := H) ⟨s, f, is⟩ ⟨s', f', is'⟩)
    {Cf Ct : Context} {it : InstrType} (hs : StoreOk s) (hf : FrameOk s f Cf)
    (hu : CtxUnder Ct Cf) (hwf : CtxWf Ct) (hts : StoreTypesOk s)
    (hty : AdminsOk s Ct (vals vs ++ is ++ rest) it) :
    PresConcl ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ Cf Ct it := by
  have hreg := AdminsOk.regular hs hts hwf hty
  obtain ⟨t₂, xs₁, xs₂, hA, hR, hL1⟩ : ∃ t₂ xs₁ xs₂,
      AdminsOk s Ct (vals vs ++ is) ⟨it.params, xs₁, t₂⟩ ∧
      AdminsOk s (Ct.initLocals xs₁) rest ⟨t₂, xs₂, it.results⟩ ∧
      LocalsLe (Ct.initLocals it.inits).locals (Ct.initLocals (xs₁ ++ xs₂)).locals := by
    by_cases hr : rest = []
    · subst hr
      refine ⟨it.results, it.inits, [], by simpa using hty, AdminsOk.id (by simpa using hreg.2.1),
        by simpa using LocalsLe.refl _⟩
    · exact AdminsOk.split hty hwf _ _ rfl hr
  obtain ⟨m, ya, yb, hV, hI, hL2⟩ := AdminsOk.split hA hwf (vals vs) is rfl hne'
  have hyaS := AdminsOk.vals_inits hV
  have hya : Ct.initLocals ya = Ct := Context.initLocals_of_set hyaS
  rw [hya] at hI
  have hybE := (AdminsOk.params_ok hwf hI).2
  obtain ⟨Cf', Ct', hs', hext, hf', hCf', hu', hle, hI'⟩ := ih hs hf hu hwf hts hI
  refine ⟨Cf', Ct', hs', hext, hf', hCf', hu', hle, ?_⟩
  have hV' := (hV.extend hs hext).weaken hle
  have hya' : Ct'.initLocals ya = Ct' :=
    Context.initLocals_of_set fun x hx => by
      obtain ⟨t, ht⟩ := hyaS x hx; exact ⟨t, hle.le.set ht⟩
  have hVI : AdminsOk s' Ct' (vals vs ++ is') ⟨it.params, ya ++ yb, t₂⟩ := by
    refine .seq hV' (fun x hx => ?_) (by rw [hya']; exact hI')
    obtain ⟨t, ht⟩ := hyaS x hx; exact ⟨_, hle.le.set ht⟩
  have hR' : AdminsOk s' (Ct'.initLocals (ya ++ yb)) rest ⟨t₂, xs₂, it.results⟩ :=
    (hR.extend hs hext).weaken (hle.initLocals_of hL2)
  have hW : AdminsOk s' Ct' (vals vs ++ is' ++ rest) ⟨it.params, (ya ++ yb) ++ xs₂, it.results⟩ := by
    refine .seq hVI (fun x hx => ?_) hR'
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨t, ht⟩ := hyaS x hx; exact ⟨_, hle.le.set ht⟩
    · exact hle.le.exists (hybE x hx)
  refine AdminsOk.sub hW ⟨ResultSub.refl _ _, ResultSub.refl _ _, ?_⟩ (hle.instrTypeOk hreg)
  intro x hx hnx
  obtain ⟨lt, hlt⟩ := hreg.2.2 x hx
  have h1 := Context.initLocals_set_of_mem (C := Ct) hx hlt
  obtain ⟨i₁, h2, hi₁⟩ := hL1 x _ h1
  have hi₁' := hi₁ rfl
  subst hi₁'
  rw [Context.initLocals_append] at h2
  have h3 := LocalsLe.initLocals (C := Ct.initLocals xs₁) (C' := Ct.initLocals (ya ++ yb)) hL2 xs₂
  obtain ⟨i₂, h4, hi₂⟩ := h3 x _ h2
  have hi₂' := hi₂ rfl
  subst hi₂'
  rw [← Context.initLocals_append] at h4
  obtain ⟨i₃, h5, hi₃⟩ := LocalsLe.initLocals hle.le ((ya ++ yb) ++ xs₂) x _ h4
  have hi₃' := hi₃ rfl
  subst hi₃'
  rcases Context.initLocals_set h5 with h6 | h6
  · exact absurd h6 hnx
  · exact ⟨_, h6⟩

theorem pres_ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (ih : PresIH (H := H) ⟨s, f, is⟩ ⟨s', f', is'⟩)
    {Cf Ct : Context} {it : InstrType} (hs : StoreOk s) (hf : FrameOk s f Cf)
    (hu : CtxUnder Ct Cf) (hwf : CtxWf Ct) (hts : StoreTypesOk s)
    (hty : AdminsOk s Ct [.label n cont is] it) :
    PresConcl ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ Cf Ct it := by
  obtain ⟨it₀, ha, k⟩ := AdminsOk.single_decomp hs hty _ rfl hwf.types
  cases ha with
  | label hn hc hb =>
    rename_i t' ts xs' xs
    have ht' : ResultOk Ct.toTypeCtx t' := (AdminsOk.params_ok hwf hc).1
    obtain ⟨Cf', Ct'', hs', hext, hf', hCf', hu'', hle'', hb'⟩ :=
      ih hs hf (hu.withLabel t') (hwf.withLabel ht') hts hb
    obtain ⟨e'', hle⟩ := CtxLe.withLabel_inv hle''
    have hu' : CtxUnder { Ct with locals := Ct''.locals } Cf' := hu.shift hCf' hu''.le
    refine ⟨Cf', _, hs', hext, hf', hCf', hu', hle, k s' _ _ hext hle ?_⟩
    rw [e''] at hb'
    exact .label hn ((hc.extend hs hext).weaken hle) hb'

theorem pres_ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (ih : PresIH (H := H) ⟨s, f, is⟩ ⟨s', f', is'⟩)
    {Cf Ct : Context} {it : InstrType} (hs : StoreOk s) (hf : FrameOk s f Cf)
    (hu : CtxUnder Ct Cf) (hwf : CtxWf Ct) (hts : StoreTypesOk s)
    (hty : AdminsOk s Ct [.handler n cs is] it) :
    PresConcl ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ Cf Ct it := by
  obtain ⟨it₀, ha, k⟩ := AdminsOk.single_decomp hs hty _ rfl hwf.types
  cases ha with
  | handler hc hb =>
    obtain ⟨Cf', Ct', hs', hext, hf', hCf', hu', hle, hb'⟩ := ih hs hf hu hwf hts hb
    exact ⟨Cf', Ct', hs', hext, hf', hCf', hu', hle,
      k s' Ct' _ hext hle (.handler (fun c hc' => hle.catchOk (hc c hc')) hb')⟩

theorem pres_ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat}
    {is is' : List Admin} (ih : PresIH (H := H) ⟨s, fi, is⟩ ⟨s', fi', is'⟩)
    {Cf Ct : Context} {it : InstrType} (hs : StoreOk s) (hf : FrameOk s f Cf)
    (hu : CtxUnder Ct Cf) (hwf : CtxWf Ct) (hts : StoreTypesOk s)
    (hty : AdminsOk s Ct [.frame n fi is] it) :
    PresConcl ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ Cf Ct it := by
  obtain ⟨it₀, ha, k⟩ := AdminsOk.single_decomp hs hty _ rfl hwf.types
  cases ha with
  | frame hfi hn hb hok =>
    rename_i C' ts
    have hwfi : CtxWf { C' with return_ := some ts } :=
      (FrameOk.ctxWf hs hts hfi).withReturn fun t h => TyOk.of_empty _ (hok t h)
    have huI : CtxUnder { C' with return_ := some ts } C' := ⟨rfl, LocalsLe.refl _⟩
    obtain ⟨Cf'', Ct'', hs', hext, hf'', hCf'', hu'', hle'', hb'⟩ := ih hs hfi huI hwfi hts hb
    have hlab : Cf''.labels = C'.labels := by rw [hCf'']
    have hbody : AdminsOk s' { Cf'' with return_ := some ts } is' (.plain [] ts) := by
      refine AdminsOk.weaken (C' := { Cf'' with return_ := some ts }) ⟨?_, hu''.le⟩ hb'
      have e := hu''.reshape_eq Cf''.locals Ct''.labels Ct''.return_
      show _ = Ct''.reshape Cf''.locals Ct''.labels Ct''.return_
      rw [e, hle''.labels, hle''.return_, ← hlab]
    exact ⟨Cf, Ct, hs', hext, hf.extend_of_storeOk hs hext, rfl, hu, CtxLe.refl _,
      k s' Ct _ hext (CtxLe.refl _) (.frame hf'' hn hbody hok)⟩

end ctxt

/-! ## Delegated families -/

theorem pres_pure {s : Store H} {f : Frame} {is is' : List Admin} {Cf Ct : Context}
    {it : InstrType} (hs : StoreOk s) (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf)
    (hty : AdminsOk s Ct is it) (hfl : AllFlat is ∧ AllFlat is')
    (hp : StateOk s f Cf → AdminsOk s Cf is it → AdminsOk s Cf is' it) :
    PresConcl ⟨s, f, is⟩ ⟨s, f, is'⟩ Cf Ct it :=
  PresConcl.of_frame hu rfl hs (Extend.refl hs) hf (hp ⟨hs, hf⟩ (hty.toFrame hu hfl.1)) hfl.2

theorem pres_state {c c' : Config H} {Cf Ct : Context} {it : InstrType} (hs : StoreOk c.store)
    (hf : FrameOk c.store c.frame Cf) (hu : CtxUnder Ct Cf) (hty : AdminsOk c.store Ct c.code it)
    (hfl : AllFlat c.code ∧ AllFlat c'.code)
    (hp : StateOk c.store c.frame Cf → AdminsOk c.store Cf c.code it →
      c'.frame = c.frame ∧ StoreOk c'.store ∧ Extend c.store c'.store ∧
        AdminsOk c'.store Cf c'.code it) :
    PresConcl c c' Cf Ct it := by
  obtain ⟨hfr, hs', he, h'⟩ := hp ⟨hs, hf⟩ (hty.toFrame hu hfl.1)
  refine PresConcl.of_frame hu hfr hs' he ?_ h' hfl.2
  rw [hfr]; exact hf.extend_of_storeOk hs he

/-! ## Variable family -/

section variableFamily

theorem forall₂_append_inv {α β : Type} {R : α → β → Prop} :
    ∀ {a b : List α} {c d : List β}, List.Forall₂ R (a ++ b) (c ++ d) →
      a.length = c.length → List.Forall₂ R a c ∧ List.Forall₂ R b d
  | [], _, [], _, h, _ => ⟨.nil, h⟩
  | [], _, _ :: _, _, _, hl => by simp at hl
  | _ :: _, _, [], _, _, hl => by simp at hl
  | _ :: _, _, _ :: _, _, .cons hab h, hl => by
    have := forall₂_append_inv h (by simpa using hl)
    exact ⟨.cons hab this.1, this.2⟩

theorem forall₂_set {α β : Type} {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    ∀ {l : List α} {m : List β} (i : Nat), List.Forall₂ R l m →
      List.Forall₂ R (l.set i a) (m.set i b)
  | _, _, _, .nil => .nil
  | _, _, 0, .cons _ h => .cons hab h
  | _, _, i + 1, .cons h' h => .cons h' (forall₂_set hab i h)

theorem Sub.num_fwd {Δ : TypeCtx} {b : CValType} {nt : NumType} (h : Sub Δ (.num nt) b) :
    b = .num nt := by
  generalize e : (Ty.num nt : CValType) = T at h
  cases h <;> first | (cases e; rfl) | cases e

theorem Sub.vec_fwd {Δ : TypeCtx} {b : CValType} {vt : VecType} (h : Sub Δ (.vec vt) b) :
    b = .vec vt := by
  generalize e : (Ty.vec vt : CValType) = T at h
  cases h <;> first | (cases e; rfl) | cases e

theorem Sub.refv_fwd {Δ : TypeCtx} {b : CValType} {rt : CRefType} (h : Sub Δ (.refv rt) b) :
    ∃ rt', b = .refv rt' ∧ Sub Δ rt rt' := by
  generalize e : (Ty.refv rt : CValType) = T at h
  cases h <;> first | (cases e; exact ⟨_, rfl, by assumption⟩) | cases e

/-- Value subsumption along subtyping in `{}`. -/
theorem ValOk.sub_empty {s : Store H} {v : Val} {a b : CValType} (hv : ValOk s v a)
    (hsub : Sub {} a b) (hb : TyOk {} b) : ValOk s v b := by
  cases hv with
  | num v => rw [Sub.num_fwd hsub]; exact .num v
  | vec x => rw [Sub.vec_fwd hsub]; exact .vec x
  | ref h =>
    obtain ⟨rt', rfl, hs⟩ := Sub.refv_fwd hsub
    have : TyOk {} rt' := by cases hb; assumption
    exact .ref (.sub h this hs)

/-- Value subsumption along subtyping in the typing context of a typed frame, to a type
valid in `{}` (via the runtime strengthening `ValOk.ctxSubAgg`). -/
theorem ValOk.sub_ctx {s : Store H} {f : Frame} {Ct Cf : Context} (hs : StoreOk s)
    (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf) {v : Val} {a b : CValType} (hv : ValOk s v a)
    (hsub : Sub Ct.toTypeCtx a b) (hb : TyOk {} b) : ValOk s v b := by
  rw [hu.toTypeCtx] at hsub
  exact ValOk.ctxSubAgg ⟨hs, hf⟩ ⟨hs.structsClosed, hs.arraysClosed⟩ hv hsub hb

theorem CtxUnder.types_eqW {Ct Cf : Context} (hu : CtxUnder Ct Cf) : Ct.types = Cf.types :=
  congrArg TypeCtx.types hu.toTypeCtx

theorem CtxUnder.types_moduleW {s : Store H} {f : Frame} {Ct Cf : Context} (hu : CtxUnder Ct Cf)
    (hf : FrameOk s f Cf) : Ct.types = f.module.types :=
  hu.types_eqW.trans hf.types_eq

theorem CtxUnder.types_emptyW {s : Store H} {f : Frame} {Ct Cf : Context} (hu : CtxUnder Ct Cf)
    (hf : FrameOk s f Cf) : ∀ d ∈ Ct.types, TyOk {} d := by
  rw [hu.types_eqW]; exact hf.typesOkEmptyCast

/-- Singleton inversion (`AdminsOk.single_aux`) that also records the validity of the
framed prefix. -/
theorem AdminsOk.single_aux' {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → ∀ a, as = [a] →
      C.toTypeCtx.Ok →
      ∃ ts it₀, AdminOk s C a it₀ ∧ ResultOk C.toTypeCtx ts ∧
        List.Forall₂ (SubEqL C.toTypeCtx) it.params (ts ++ it₀.params) ∧
        List.Forall₂ (SubEqR C.toTypeCtx) (ts ++ it₀.results) it.results ∧
        ∀ x ∈ it.inits, x ∉ it₀.inits → ∃ t, C.locals[x]? = some ⟨.set, t⟩
  | _, _, _, .nil, _, e, _ => by cases e
  | _, _, it, .single h, a, e, _ => by
    cases e
    exact ⟨[], it, h, by simp [ResultOk], forall₂_self (fun _ => .inl rfl) _,
      forall₂_self (fun _ => .inl rfl) _, fun _ hx hn => absurd hx hn⟩
  | C, _, _, .cons (t₁ := t₁) (t₂ := t₂) (xs₁ := xs₁) ha _ hs, a, e, hΔ => by
    obtain ⟨rfl, e₂⟩ := List.cons_eq_cons.mp e
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    obtain ⟨_, r₂, s₂, i₂⟩ := AdminsOk.nil_aux hs e₂ hΔ'
    rw [Context.initLocals_toTypeCtx] at r₂ s₂
    refine ⟨[], ⟨t₁, xs₁, t₂⟩, ha, by simp [ResultOk], forall₂_self (fun _ => .inl rfl) _,
      forall₂_subEqR_of_sub s₂ r₂, ?_⟩
    intro x hx hn
    rcases List.mem_append.mp hx with hx | hx
    · exact absurd hx hn
    · obtain ⟨t, ht⟩ := i₂ x hx
      rcases Context.initLocals_set ht with hx' | h'
      · exact absurd hx' hn
      · exact ⟨t, h'⟩
  | C, _, _, .seq (xs₁ := xs₁) h₁ _ h₂, a, e, hΔ => by
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    rcases List.append_eq_singleton_iff.mp e with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · obtain ⟨p₁, _, s₁, i₁⟩ := AdminsOk.nil_aux h₁ e₁ hΔ
      have hC : C.initLocals xs₁ = C := Context.initLocals_of_set i₁
      obtain ⟨ts, it₀, ha, hts, hp, hr, hi⟩ := AdminsOk.single_aux' h₂ a e₂ hΔ'
      rw [hC] at ha hts hp hr hi
      refine ⟨ts, it₀, ha, hts, forall₂_comp s₁ hp fun a _ _ ha' _ _ hab hbc =>
        SubEqL.sub_left hΔ hab (p₁ a ha') hbc, hr, ?_⟩
      intro x hx hn
      rcases List.mem_append.mp hx with hx | hx
      · exact i₁ x hx
      · exact hi x hx hn
    · obtain ⟨ts, it₀, ha, hts, hp, hr, hi⟩ := AdminsOk.single_aux' h₁ a e₁ hΔ
      obtain ⟨_, r₂, s₂, i₂⟩ := AdminsOk.nil_aux h₂ e₂ hΔ'
      rw [Context.initLocals_toTypeCtx] at r₂ s₂
      refine ⟨ts, it₀, ha, hts, hp, forall₂_comp hr s₂ fun _ _ c _ _ hc hab hbc =>
        SubEqR.sub_right hΔ hab hbc (r₂ c hc), ?_⟩
      intro x hx hn
      rcases List.mem_append.mp hx with hx | hx
      · exact hi x hx hn
      · obtain ⟨t, ht⟩ := i₂ x hx
        rcases Context.initLocals_set ht with hx' | h'
        · exact hi x hx' hn
        · exact ⟨t, h'⟩
  | _, _, _, .sub (it := it) h hs hok, a, e, hΔ => by
    obtain ⟨ts, it₀, ha, hts, hp, hr, hi⟩ := AdminsOk.single_aux' h a e hΔ
    refine ⟨ts, it₀, ha, hts, forall₂_comp hs.1 hp fun a _ _ ha' _ _ hab hbc =>
        SubEqL.sub_left hΔ hab (hok.1 a ha') hbc,
      forall₂_comp hr hs.2.1 fun _ _ c _ _ hc hab hbc =>
        SubEqR.sub_right hΔ hab hbc (hok.2.1 c hc), ?_⟩
    intro x hx hn
    by_cases hx' : x ∈ it.inits
    · exact hi x hx' hn
    · exact hs.2.2 x hx hx'
  | _, _, _, .frame (ts := F) h hok, a, e, hΔ => by
    obtain ⟨ts, it₀, ha, hts, hp, hr, hi⟩ := AdminsOk.single_aux' h a e hΔ
    refine ⟨F ++ ts, it₀, ha, ResultOk.append hok hts, ?_, ?_, hi⟩
    · rw [List.append_assoc]
      exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) hp
    · rw [List.append_assoc]
      exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) hr

/-- Inversion of a typed one-operand redex `v instr`. -/
theorem AdminsOk.redex1_inv {s : Store H} (hs : StoreOk s) (hts : StoreTypesOk s) {C : Context}
    (hC : C.Wf) {v : Val} {i : Instr} {it : InstrType}
    (h : AdminsOk s C [v.toAdmin, .plain i] it) (hne : i ≠ .throwRef := by intro h; cases h) :
    ∃ tv F it₁, ValOk s v tv ∧ InstrOk C i it₁ ∧ ResultOk C.toTypeCtx F ∧
      ResultSub C.toTypeCtx (it.params ++ [tv]) (F ++ it₁.params) ∧
      ResultSub C.toTypeCtx (F ++ it₁.results) it.results ∧
      ∀ x ∈ it.inits, x ∈ it₁.inits ∨ ∃ t, C.locals[x]? = some ⟨.set, t⟩ := by
  have hΔ := hC.types
  obtain ⟨m, ya, yb, hV, hI, hL⟩ := AdminsOk.split h hC [v.toAdmin] [.plain i] rfl (by simp)
  have hyaS := AdminsOk.vals_inits (vs := [v]) hV
  have hya : C.initLocals ya = C := Context.initLocals_of_set hyaS
  rw [hya] at hI
  obtain ⟨ts, hvs, hsub⟩ := AdminsOk.vals_inv (vs := [v]) hΔ hV
  obtain ⟨tv, rfl, hv⟩ : ∃ tv, ts = [tv] ∧ ValOk s v tv := by
    cases hvs with | cons h hn => cases hn; exact ⟨_, rfl, h⟩
  obtain ⟨F, it₁, ha, hF, hp, hr, hi⟩ := AdminsOk.single_aux' hI _ rfl hΔ
  have hi₁ : InstrOk C i it₁ := AdminOk.plain_inv ha hne
  have hm : ResultOk C.toTypeCtx m := (AdminsOk.params_ok hC hI).1
  refine ⟨tv, F, it₁, hv, hi₁, hF, ?_, hr.imp fun _ _ h => h.sub, ?_⟩
  · exact forall₂_sub_trans hΔ hsub (hp.imp fun _ _ h => h.sub) hm
  · intro x hx
    obtain ⟨lt, hlt⟩ := (AdminsOk.regular hs hts hC h).2.2 x hx
    have h1 := Context.initLocals_set_of_mem (C := C) hx hlt
    obtain ⟨j, h2, hj⟩ := hL x _ h1
    have hj' := hj rfl
    subst hj'
    rcases Context.initLocals_set h2 with h3 | h3
    · rcases List.mem_append.mp h3 with h4 | h4
      · exact .inr (hyaS x h4)
      · by_cases h5 : x ∈ it₁.inits
        · exact .inl h5
        · exact .inr (hi x h4 h5)
    · exact .inr ⟨_, h3⟩

theorem InstrOk.localGet_inv {C : Context} {x : LocalIdx} {it : InstrType}
    (h : InstrOk C (.localGet x) it) :
    ∃ t, C.locals[x.toNat]? = some ⟨.set, t⟩ ∧ it = .plain [] [t] := by
  cases h <;> (try (rename_i h'; cases h'))
  exact ⟨_, ‹_›, rfl⟩

theorem InstrOk.localSet_inv {C : Context} {x : LocalIdx} {it : InstrType}
    (h : InstrOk C (.localSet x) it) :
    ∃ i t, C.locals[x.toNat]? = some ⟨i, t⟩ ∧ it = ⟨[t], [x.toNat], []⟩ := by
  cases h <;> (try (rename_i h'; cases h'))
  exact ⟨_, _, ‹_›, rfl⟩

theorem InstrOk.localTee_inv {C : Context} {x : LocalIdx} {it : InstrType}
    (h : InstrOk C (.localTee x) it) :
    ∃ i t, C.locals[x.toNat]? = some ⟨i, t⟩ ∧ it = ⟨[t], [x.toNat], [t]⟩ := by
  cases h <;> (try (rename_i h'; cases h'))
  exact ⟨_, _, ‹_›, rfl⟩

theorem InstrOk.globalGet_inv {C : Context} {x : GlobalIdx} {it : InstrType}
    (h : InstrOk C (.globalGet x) it) :
    ∃ m t, C.globals[x.toNat]? = some ⟨m, t⟩ ∧ it = .plain [] [t] := by
  cases h <;> (try (rename_i h'; cases h'))
  exact ⟨_, _, ‹_›, rfl⟩

theorem InstrOk.globalSet_inv {C : Context} {x : GlobalIdx} {it : InstrType}
    (h : InstrOk C (.globalSet x) it) :
    ∃ t, C.globals[x.toNat]? = some ⟨.var, t⟩ ∧ it = .plain [t] [] := by
  cases h <;> (try (rename_i h'; cases h'))
  exact ⟨_, ‹_›, rfl⟩

theorem FrameOk.local_valOk {s : Store H} {f : Frame} {C : Context} (hf : FrameOk s f C)
    {x : LocalIdx} {v : Val} (hx : f.local? x = some (some v)) {t : CValType}
    (hl : C.locals[x.toNat]? = some ⟨.set, t⟩) : ValOk s v t := by
  obtain ⟨C₀, lts, hm, hl', rfl⟩ := hf
  obtain ⟨h0, -⟩ := hm.ctx_fields
  simp only [h0, List.nil_append] at hl
  obtain ⟨a, ha, hv⟩ := forall₂_getElem?_right hl' hl
  simp only [Frame.local?] at hx
  rw [hx] at ha
  cases ha
  cases hv with
  | set h => exact h

theorem FrameOk.local_tyOk {s : Store H} {f : Frame} {C : Context} (hs : StoreOk s)
    (_hts : StoreTypesOk s) (hf : FrameOk s f C) {x : Nat} {i : Init} {t : CValType}
    (hl : C.locals[x]? = some ⟨i, t⟩) : TyOk {} t := by
  obtain ⟨C₀, lts, hm, hl', rfl⟩ := hf
  obtain ⟨h0, -⟩ := hm.ctx_fields
  simp only [h0, List.nil_append] at hl
  obtain ⟨a, -, hv⟩ := forall₂_getElem?_right hl' hl
  cases hv with
  | set h => exact h.tyOk_empty hs
  | unset h => exact h

theorem FrameOk.setLocal {s : Store H} {f : Frame} {C : Context} (hf : FrameOk s f C)
    {x : LocalIdx} {v : Val} {t : CValType} (hv : ValOk s v t) :
    FrameOk s (f.setLocal x v) { C with locals := C.locals.set x.toNat ⟨.set, t⟩ } := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := hf
  obtain ⟨h0, -⟩ := hm.ctx_fields
  refine ⟨C₀, lts.set x.toNat ⟨.set, t⟩, hm, forall₂_set (.set hv) _ hl, ?_⟩
  simp only [h0, List.nil_append]

theorem FrameOk.global {s : Store H} {f : Frame} {C : Context} (hf : FrameOk s f C)
    {x : GlobalIdx} {gt : CGlobalType} (hx : C.globals[x.toNat]? = some gt) :
    ∃ a, f.module.globals[x.toNat]? = some a ∧ ExternAddrOk s (.global a) (.global gt) := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := hf
  cases hm with
  | mk _ _ hglobals => exact forall₂_getElem?_right hglobals hx

theorem Store.global?_spec {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat}
    {g : GlobalInst} (h : s.global? f x = some (a, g)) :
    f.module.globals[x.toNat]? = some a ∧ s.globals[a]? = some g := by
  simp only [Store.global?] at h
  cases h₁ : f.module.globals[x.toNat]? with
  | none => simp [h₁] at h
  | some b =>
    cases h₂ : s.globals[b]? with
    | none => simp [h₁, h₂] at h
    | some t =>
      simp [h₁, h₂] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, h₂⟩

theorem ExternAddrOk.global_val {s : Store H} (hs : StoreOk s) {xa : ExternAddr}
    {xt : CExternType} (h : ExternAddrOk s xa xt) :
    ∀ (a : Nat) (g : GlobalInst) (gt : CGlobalType), xa = .global a → s.globals[a]? = some g →
      xt = .global gt → ValOk s g.value gt.type := by
  induction h with
  | global h =>
    intro a g gt e1 hg e2
    cases e1
    injection e2 with e2
    rw [h] at hg
    cases hg
    rw [← e2]
    exact (hs.globals _ (List.mem_of_getElem? h)).2
  | sub h hok hsub ih =>
    intro a g gt e1 hg e2
    subst e1 e2
    cases hsub with
    | global hgs =>
      cases hgs with
      | const h' =>
        have := ih a g _ rfl hg rfl
        cases hok with
        | global hok => exact ValOk.sub_empty this h' hok
      | var h₁ h₂ =>
        have := ih a g _ rfl hg rfl
        cases hok with
        | global hok => exact ValOk.sub_empty this h₁ hok
  | _ => intro a g gt e1; cases e1

theorem ExternAddrOk.global_var {s : Store H} (hs : StoreOk s) {xa : ExternAddr}
    {xt : CExternType} (h : ExternAddrOk s xa xt) :
    ∀ (a : Nat) (g : GlobalInst) (t : CValType), xa = .global a → s.globals[a]? = some g →
      xt = .global ⟨.var, t⟩ →
      g.type.mutability = .var ∧ ∀ v, ValOk s v t → ValOk s v g.type.type := by
  induction h with
  | global h =>
    intro a g t e1 hg e2
    cases e1
    injection e2 with e2
    rw [h] at hg
    cases hg
    rw [e2]
    exact ⟨rfl, fun _ hv => hv⟩
  | sub h hok hsub ih =>
    intro a g t e1 hg e2
    subst e1 e2
    cases hsub with
    | global hgs =>
      cases hgs with
      | var h₁ h₂ =>
        obtain ⟨hm, hc⟩ := ih a g _ rfl hg rfl
        have ht₁ : TyOk {} _ := (h.tyOk0 hs : ExternTyOk0 (.global ⟨.var, _⟩))
        exact ⟨hm, fun v hv => hc v (ValOk.sub_empty hv h₂ ht₁)⟩
  | _ => intro a g t e1; cases e1

theorem storeOk_setGlobal {s : Store H} (hs : StoreOk s) {a : Nat} {g : GlobalInst}
    (hg : s.globals[a]? = some g) (hmut : g.type.mutability = .var) {v : Val}
    (hv : ValOk s v g.type.type) : StoreOk (s.setGlobal a v) ∧ Extend s (s.setGlobal a v) := by
  have he : Extend s (s.setGlobal a v) :=
    { Extend.refl hs with
      globals := TM.extendsList_modify (fun _ _ => ⟨rfl, .inr rfl⟩) fun x hx => by
        rw [hg] at hx; cases hx; exact ⟨rfl, .inl hmut⟩ }
  refine ⟨?_, he⟩
  exact {
    tags := fun ti h => hs.tags ti h
    globals := fun gi h => by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
      simp only [Store.setGlobal, List.getElem?_modify] at hi
      by_cases hia : a = i
      · subst hia
        simp [hg] at hi
        subst hi
        exact ⟨(hs.globals g (List.mem_of_getElem? hg)).1, TM.valOk_extend he hv⟩
      · simp [hia] at hi
        obtain ⟨h₁, h₂⟩ := hs.globals gi (List.mem_of_getElem? hi)
        exact ⟨h₁, TM.valOk_extend he h₂⟩
    mems := hs.mems
    tables := fun ti h => TM.tableInstOk_extend he (hs.tables ti h)
    funcs := fun fi h => by
      cases hs.funcs fi h with
      | wasm hdt hm hcode hf hsub => exact .wasm hdt (TM.moduleInstOk_extend hs he hm) hcode hf hsub
      | host hdt he' hcode => exact .host hdt he' hcode
    elems := fun ei h => ⟨(hs.elems ei h).1, fun r hr => ((hs.elems ei h).2 r hr).extend he⟩
    structs := fun si h => by
      obtain ⟨fs, hx, hf⟩ := hs.structs si h
      exact ⟨fs, hx, hf.imp fun _ _ h => TM.fieldValOk_extend he h⟩
    arrays := fun ai h => by
      obtain ⟨ft, hx, hf⟩ := hs.arrays ai h
      exact ⟨ft, hx, fun fv hfv => TM.fieldValOk_extend he (hf fv hfv)⟩
    exns := fun e h => by
      obtain ⟨ti, ts, ht, hx, hf⟩ := hs.exns e h
      exact ⟨ti, ts, ht, hx, hf.imp fun _ _ h => TM.valOk_extend he h⟩
    acyclicStructs := fun a' ha hr => hs.acyclicStructs a' ha
      (TM.immutReachable_transfer (s := s) (s' := s.setGlobal a v) rfl rfl rfl hr)
    acyclicArrays := fun a' ha hr => hs.acyclicArrays a' ha
      (TM.immutReachable_transfer (s := s) (s' := s.setGlobal a v) rfl rfl rfl hr)
    acyclicExns := fun a' ha hr => hs.acyclicExns a' ha
      (TM.immutReachable_transfer (s := s) (s' := s.setGlobal a v) rfl rfl rfl hr)
    structsClosed := hs.structsClosed
    arraysClosed := hs.arraysClosed }

theorem CtxUnder.globals {Ct Cf : Context} (hu : CtxUnder Ct Cf) : Ct.globals = Cf.globals := by
  have := congrArg Context.globals (hu.reshape_eq Ct.locals Ct.labels Ct.return_)
  exact this

theorem pres_variable {c c' : Config H} (h : VariableStep c c') {Cf Ct : Context} {it : InstrType}
    (hs : StoreOk c.store) (hf : FrameOk c.store c.frame Cf) (hu : CtxUnder Ct Cf)
    (hwf : CtxWf Ct) (hts : StoreTypesOk c.store) (hty : AdminsOk c.store Ct c.code it) :
    PresConcl c c' Cf Ct it := by
  have hreg := AdminsOk.regular hs hts hwf hty
  cases h with
  | localGet hx =>
    obtain ⟨it₀, ha, k⟩ := AdminsOk.single_decomp hs hty _ rfl hwf.types
    obtain ⟨t, hl, rfl⟩ := InstrOk.localGet_inv (AdminOk.plain_inv ha)
    have hval := FrameOk.local_valOk hf hx (hu.le.set hl)
    exact PresConcl.same hs hf hu
      (k _ Ct _ (Extend.refl hs) (CtxLe.refl _) (AdminOk.toAdmin_ok hval))
  | globalGet hgx =>
    obtain ⟨it₀, ha, k⟩ := AdminsOk.single_decomp hs hty _ rfl hwf.types
    obtain ⟨m, t, hg, rfl⟩ := InstrOk.globalGet_inv (AdminOk.plain_inv ha)
    rw [hu.globals] at hg
    obtain ⟨a', ha', hext⟩ := FrameOk.global hf hg
    obtain ⟨h1, h2⟩ := Store.global?_spec hgx
    rw [h1] at ha'
    cases ha'
    have hval := ExternAddrOk.global_val hs hext _ _ ⟨m, t⟩ rfl h2 rfl
    exact PresConcl.same hs hf hu
      (k _ Ct _ (Extend.refl hs) (CtxLe.refl _) (AdminOk.toAdmin_ok hval))
  | @localSet s f x v hx =>
    obtain ⟨tv, F, it₁, hv, hi₁, hF, hsp, hsr, hinit⟩ := AdminsOk.redex1_inv hs hts hwf hty
    obtain ⟨i₀, t, hl, rfl⟩ := InstrOk.localSet_inv hi₁
    have hlen : it.params.length = F.length := by
      have := hsp.length_eq; simp at this; omega
    obtain ⟨hPF, htv⟩ := forall₂_append_inv hsp hlen
    have htvt : Sub Ct.toTypeCtx tv t := by cases htv with | cons h _ => exact h
    have hPR : ResultSub Ct.toTypeCtx it.params it.results :=
      forall₂_sub_trans hwf.types hPF (by rw [List.append_nil] at hsr; exact hsr) hF
    obtain ⟨i', hl', -⟩ := hu.le x.toNat _ hl
    have htyt : TyOk {} t := FrameOk.local_tyOk hs hts hf hl'
    have hvt : ValOk s v t := ValOk.sub_ctx hs hf hu hv htvt htyt
    have hle := CtxLe.self_initLocals Ct [x.toNat]
    refine ⟨{ Cf with locals := Cf.locals.set x.toNat ⟨.set, t⟩ }, Ct.initLocals [x.toNat], hs,
      Extend.refl hs, FrameOk.setLocal hf hvt, rfl, ?_, hle, ?_⟩
    · rw [Ct.initLocals_eq_with]
      refine hu.shift rfl ?_
      intro y a hy
      rw [Context.initLocals_locals] at hy
      by_cases hyx : y = x.toNat
      · subst hyx
        simp only [List.mem_singleton, ite_true, hl, Option.map_some, Option.some.injEq] at hy
        subst hy
        refine ⟨.set, ?_, fun _ => rfl⟩
        have hlt : x.toNat < Cf.locals.length := by
          rcases List.getElem?_eq_some_iff.mp hl' with ⟨h, -⟩; exact h
        simp [hlt]
      · simp only [List.mem_singleton, hyx, ite_false] at hy
        obtain ⟨j, hj, hjj⟩ := hu.le y a hy
        refine ⟨j, ?_, hjj⟩
        rw [List.getElem?_set_ne (Ne.symm hyx)]
        exact hj
    · refine AdminsOk.sub (AdminsOk.id (by simpa using hreg.1))
        ⟨ResultSub.refl _ _, by simpa using hPR, ?_⟩ (hle.instrTypeOk hreg)
      intro y hy _
      rcases hinit y hy with h | ⟨t', ht'⟩
      · simp only [List.mem_singleton] at h
        subst h
        exact ⟨t, Context.initLocals_set_of_mem (by simp) hl⟩
      · exact ⟨t', Context.initLocals_set_of_set ht'⟩
  | @localTee s f x v =>
    obtain ⟨tv, F, it₁, hv, hi₁, hF, hsp, hsr, hinit⟩ := AdminsOk.redex1_inv hs hts hwf hty
    obtain ⟨i₀, t, hl, rfl⟩ := InstrOk.localTee_inv hi₁
    have hlen : it.params.length = F.length := by
      have := hsp.length_eq; simp at this; omega
    obtain ⟨hPF, htv⟩ := forall₂_append_inv hsp hlen
    have htvt : Sub Ct.toTypeCtx tv t := by cases htv with | cons h _ => exact h
    have htv_ok : TyOk Ct.toTypeCtx tv := TyOk.of_empty _ (hv.tyOk_empty hs)
    have ht_ok : TyOk Ct.toTypeCtx t := hwf.locals _ (List.mem_of_getElem? hl)
    have hvv : AdminsOk s Ct (vals [v, v]) ⟨[], [], [tv, tv]⟩ :=
      AdminsOk.of_vals (.cons hv (.cons hv .nil)) (by simp [htv_ok])
    have hvv' : AdminsOk s Ct (vals [v, v]) ⟨it.params, [], it.params ++ [tv, tv]⟩ := by
      simpa using AdminsOk.frame (ts := it.params) hvv hreg.1
    have hset : AdminsOk s Ct [.plain (.localSet x)] ⟨[tv], [x.toNat], []⟩ :=
      AdminsOk.sub (.single (.plain (.variable (.localSet hl))))
        ⟨.cons htvt .nil, .nil, by simp⟩ ⟨by simp [htv_ok], by simp, by simp [hl]⟩
    have hset' : AdminsOk s Ct [.plain (.localSet x)]
        ⟨it.params ++ [tv, tv], [x.toNat], it.params ++ [tv]⟩ := by
      simpa using AdminsOk.frame (ts := it.params ++ [tv]) hset
        (ResultOk.append hreg.1 (by simp [htv_ok]))
    have hW : AdminsOk s Ct (vals [v, v] ++ [.plain (.localSet x)])
        ⟨it.params, [] ++ [x.toNat], it.params ++ [tv]⟩ := .seq hvv' (by simp) hset'
    have hR : ResultSub Ct.toTypeCtx (it.params ++ [tv]) it.results :=
      forall₂_sub_trans hwf.types hsp hsr (ResultOk.append hF (by simp [ht_ok]))
    refine PresConcl.same hs hf hu (AdminsOk.sub hW ⟨ResultSub.refl _ _, hR, ?_⟩ hreg)
    intro y hy hn
    rcases hinit y hy with h | h
    · exact absurd (by simpa using h) hn
    · exact h
  | @globalSet s f x a g v hgx =>
    obtain ⟨tv, F, it₁, hv, hi₁, hF, hsp, hsr, hinit⟩ := AdminsOk.redex1_inv hs hts hwf hty
    obtain ⟨t, hg, rfl⟩ := InstrOk.globalSet_inv hi₁
    have hlen : it.params.length = F.length := by
      have := hsp.length_eq; simp at this; omega
    obtain ⟨hPF, htv⟩ := forall₂_append_inv hsp hlen
    have htvt : Sub Ct.toTypeCtx tv t := by cases htv with | cons h _ => exact h
    have hPR : ResultSub Ct.toTypeCtx it.params it.results :=
      forall₂_sub_trans hwf.types hPF (by rw [List.append_nil] at hsr; exact hsr) hF
    rw [hu.globals] at hg
    obtain ⟨a', ha', hext⟩ := FrameOk.global hf hg
    obtain ⟨h1, h2⟩ := Store.global?_spec hgx
    rw [h1] at ha'
    cases ha'
    have htyt : TyOk {} t := (hext.tyOk0 hs : ExternTyOk0 (.global ⟨.var, t⟩))
    have hvt : ValOk s v t := ValOk.sub_ctx hs hf hu hv htvt htyt
    obtain ⟨hmut, hconv⟩ := ExternAddrOk.global_var hs hext _ _ t rfl h2 rfl
    obtain ⟨hs', he⟩ := storeOk_setGlobal hs h2 hmut (hconv v hvt)
    refine ⟨Cf, Ct, hs', he, hf.extend_of_storeOk hs he, rfl, hu, CtxLe.refl _, ?_⟩
    refine AdminsOk.sub (AdminsOk.id hreg.1) ⟨ResultSub.refl _ _, hPR, ?_⟩ hreg
    intro y hy _
    rcases hinit y hy with h | h
    · simp at h
    · exact h

end variableFamily

/-- **Preservation, generalised** to code typed under a context related to the frame's.
(`StoreTypesOk` is an added hypothesis, see `Soundness/PresBasic.lean`.) -/
theorem Step.preservation_gen {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {c c' : Config H} (h : Step P host c c') :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk c.store → FrameOk c.store c.frame Cf →
      CtxUnder Ct Cf → CtxWf Ct → StoreTypesOk c.store → AdminsOk c.store Ct c.code it →
      PresConcl c c' Cf Ct it := by
  induction h with
  | parametric h =>
    intro Cf Ct it hs hf hu _ _ hty
    exact pres_pure hs hf hu hty h.allFlat fun hst hty' => ParametricStep.preservation hst hty' h
  | numeric h =>
    intro Cf Ct it hs hf hu _ _ hty
    exact pres_pure hs hf hu hty h.allFlat fun hst hty' => NumericStep.preservation hst hty' h
  | vector h =>
    intro Cf Ct it hs hf hu _ _ hty
    exact pres_pure hs hf hu hty h.allFlat fun hst hty' => VectorStep.preservation hst hty' h
  | «variable» h =>
    intro Cf Ct it hs hf hu hwf hts hty
    exact pres_variable h hs hf hu hwf hts hty
  | table h =>
    intro Cf Ct it hs hf hu _ _ hty
    exact pres_state hs hf hu hty h.allFlat fun hst hty' => TableStep.preservation hst hty' h
  | memory h =>
    intro Cf Ct it hs hf hu _ _ hty
    exact pres_state hs hf hu hty h.allFlat fun hst hty' => MemoryStep.preservation hst hty' h
  | reference h =>
    intro Cf Ct it hs hf hu _ _ hty
    exact pres_state hs hf hu hty h.allFlat fun hst hty' => RefStep.preservation hst hty' h
  | aggregate h =>
    intro Cf Ct it hs hf hu _ _ hty
    exact pres_state hs hf hu hty h.allFlat fun hst hty' => AggregateStep.preservation hst hty' h
  | ctxtInstrs h _ ih =>
    intro Cf Ct it hs hf hu hwf hts hty
    exact pres_ctxtInstrs h.code_ne_nil ih hs hf hu hwf hts hty
  | ctxtLabel _ ih =>
    intro Cf Ct it hs hf hu hwf hts hty
    exact pres_ctxtLabel ih hs hf hu hwf hts hty
  | ctxtHandler _ ih =>
    intro Cf Ct it hs hf hu hwf hts hty
    exact pres_ctxtHandler ih hs hf hu hwf hts hty
  | ctxtFrame _ ih =>
    intro Cf Ct it hs hf hu hwf hts hty
    exact pres_ctxtFrame ih hs hf hu hwf hts hty
  -- Control (unit q12, `PresControl.lean`).
  | block hbt hm => exact pres_block hbt hm
  | loop hbt hm => exact pres_loop hbt hm
  | ifTrue hc => exact pres_ifTrue hc
  | ifFalse => exact pres_ifFalse
  | labelVals => exact pres_labelVals
  | brLabelZero hl hn => exact pres_brLabelZero hl hn
  | brLabelSucc hl => exact pres_brLabelSucc hl
  | brHandler => exact pres_brHandler
  | brIfTrue hc =>
    intro Cf Ct it hs hf hu hwf hts hty; exact PresConcl.same hs hf hu (Step.brIfTrue_presBr hty hc hwf)
  | brIfFalse =>
    intro Cf Ct it hs hf hu hwf hts hty; exact PresConcl.same hs hf hu (Step.brIfFalse_presBr hty hwf)
  | brTableLt hi =>
    intro Cf Ct it hs hf hu hwf hts hty; exact PresConcl.same hs hf hu (Step.brTableLt_presBr hty hi)
  | brTableGe hi =>
    intro Cf Ct it hs hf hu hwf hts hty; exact PresConcl.same hs hf hu (Step.brTableGe_presBr hty hi)
  | brOnNullNull =>
    intro Cf Ct it hs hf hu hwf hts hty; exact PresConcl.same hs hf hu (Step.brOnNullNull_presBr hty hwf)
  | brOnNullAddr hv =>
    intro Cf Ct it hs hf hu hwf hts hty; exact PresConcl.same hs hf hu (Step.brOnNullAddr_presBr hty hv hwf)
  | brOnNonNullNull =>
    intro Cf Ct it hs hf hu hwf hts hty; exact PresConcl.same hs hf hu (Step.brOnNonNullNull_presBr hty hwf)
  | brOnNonNullAddr hv =>
    intro Cf Ct it hs hf hu hwf hts hty; exact PresConcl.same hs hf hu (Step.brOnNonNullAddr_presBr hty hv hwf)
  | brOnCastSucceed h =>
    intro Cf Ct it hs hf hu hwf hts hty; exact PresConcl.same hs hf hu (Step.brOnCastSucceed_presCast hty h hwf (hu.types_moduleW hf))
  | brOnCastFail h =>
    intro Cf Ct it hs hf hu hwf hts hty; exact PresConcl.same hs hf hu (Step.brOnCastFail_presCast hty h hwf (hu.types_moduleW hf) (hu.types_emptyW hf))
  | brOnCastFailSucceed h =>
    intro Cf Ct it hs hf hu hwf hts hty; exact PresConcl.same hs hf hu (Step.brOnCastFailSucceed_presCast hty h hwf (hu.types_moduleW hf))
  | brOnCastFailFail h =>
    intro Cf Ct it hs hf hu hwf hts hty; exact PresConcl.same hs hf hu (Step.brOnCastFailFail_presCast hty h hwf (hu.types_moduleW hf) (hu.types_emptyW hf))
  -- Calls (unit core-pres-call, `PresCall.lean`).
  | call hx hf => exact wireCall_call hx hf
  | callRefNull hc => exact wireCall_callRefNull hc
  | callRefFunc hc hf he hn hcode => exact pres_wireCallRef_callRefFunc hc hf he hn hcode
  | callRefHost hc hf he hn hcode hh => exact pres_wireCallRef_callRefHost hhost hc hf he hn hcode hh
  | callRefHostDiv hc hf he hn hcode hh => exact wireCall_callRefHostDiv
  | returnCall hx hf => exact wireCall_returnCall hx hf
  | returnCallRefLabel hc => exact pres_wireCallRef_returnCallRefLabel hc
  | returnCallRefHandler hc => exact pres_wireCallRef_returnCallRefHandler hc
  | returnCallRefFrameNull hc => exact pres_wireCallRef_returnCallRefFrameNull hc
  | returnCallRefFrameAddr hc hf he hn => exact pres_wireCallRef_returnCallRefFrameAddr hc hf he hn
  | callIndirect => exact wireCall_callIndirect
  | returnCallIndirect => exact wireCall_returnCallIndirect
  | frameVals hn => exact pres_frameVals hn
  | returnFrame hn => exact pres_returnFrame hn
  | returnLabel => exact pres_returnLabel
  | returnHandler => exact pres_returnHandler
  -- Exceptions and traps (unit q13, `PresExn.lean`).
  | throw ht he hn => exact pres_throw ht he hn
  | throwRefNull => exact pres_throwRefNull
  | throwRefInstrs hne => exact pres_throwRefInstrs hne
  | throwRefLabel => exact pres_throwRefLabel
  | throwRefFrame => exact pres_throwRefFrame
  | throwRefHandlerEmpty => exact pres_throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact pres_throwRefHandlerCatch he ht
  | throwRefHandlerCatchRef he ht => exact pres_throwRefHandlerCatchRef he ht
  | throwRefHandlerCatchAll => exact pres_throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact pres_throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact pres_throwRefHandlerNext h
  | tryTable hbt hm => exact pres_tryTable hbt hm
  | handlerVals => exact pres_handlerVals
  | trapInstrs hne => exact pres_trapInstrs hne
  | trapLabel => exact pres_trapLabel
  | trapHandler => exact pres_trapHandler
  | trapFrame => exact pres_trapFrame

/-- Preservation for a store satisfying `StoreTypesOk` (the invariant that makes frame
contexts well formed, see `Soundness/PresBasic.lean`). -/
theorem Step.preservation_of_storeTypesOk {P : Profile} {host : HostSemantics H}
    (hhost : HostOk host) {c c' : Config H} {ts : List CValType} (hts : StoreTypesOk c.store)
    (hc : ConfigOk c ts) (h : Step P host c c') :
    ConfigOk c' ts ∧ Extend c.store c'.store := by
  obtain ⟨C, ⟨hs, hf⟩, hty⟩ := hc
  obtain ⟨Cf', Ct', hs', hext, hf', hCf', hu', hle, hty'⟩ :=
    Step.preservation_gen hhost h hs hf (CtxUnder.refl C) (hf.ctxWf hs hts) hts hty
  refine ⟨⟨Cf', ⟨hs', hf'⟩, ?_⟩, hext⟩
  have hl : Cf'.labels = C.labels := by rw [hCf']
  have hr : Cf'.return_ = C.return_ := by rw [hCf']
  exact hty'.weaken (hu'.toCtxLe (by rw [hle.labels, hl]) (by rw [hle.return_, hr]))

/-- Preservation (subject reduction). `StoreTypesOk` follows from the upstream
`StoreOk.structsClosed`/`StoreOk.arraysClosed` deviation. -/
theorem Step.preservation {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {c c' : Config H} {ts : List CValType} (hc : ConfigOk c ts) (h : Step P host c c') :
    ConfigOk c' ts ∧ Extend c.store c'.store :=
  Step.preservation_of_storeTypesOk hhost
    ⟨hc.choose_spec.1.1.structsClosed, hc.choose_spec.1.1.arraysClosed⟩ hc h

end Silmaril.Wasm.Execution.Core
