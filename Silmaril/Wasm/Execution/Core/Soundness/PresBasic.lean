module

public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping
public import Silmaril.Wasm.Execution.Core.Soundness.RefOkClosed
public import Silmaril.Wasm.Execution.Core.Soundness.FrameRegularity
public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux

@[expose] public section

/-! # Preservation: the generalised invariant and its basic lemmas

Used by `Soundness/Preservation.lean` and the control/call/exception units.

* `Context.reshape`: a context with its locals, labels and return type replaced.
* `CtxLe C C'`: `C'` is `C` with (weakly) more locals set; typing is monotone along it
  (`AdminsOk.weaken`).
* `Admin.flat`/`AllFlat`: code without control instructions, whose typing ignores
  `LABELS` and `RETURN` (`AdminsOk.relabel`).
* `CtxUnder Ct Cf`: the typing context `Ct` of the code agrees with the frame context
  `Cf` except on `LOCALS` (pointwise less initialised), `LABELS` and `RETURN`.
* `CtxWf`: well-formedness of a typing context (`Context.Wf`).
* `PresConcl`: the conclusion of the generalised preservation lemma.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Contexts differing only in locals, labels and return -/

/-- `C` with its locals, labels and return type replaced. -/
abbrev _root_.Silmaril.Wasm.Validation.Context.reshape (C : Context) (lo : List LocalType)
    (lb : List (List CValType)) (r : Option (List CValType)) : Context :=
  { C with locals := lo, labels := lb, return_ := r }

section transfer

variable {C : Context} {lo : List LocalType} {lb : List (List CValType)}
  {r : Option (List CValType)} {i : Instr} {it : InstrType}

theorem _root_.Silmaril.Wasm.Validation.ParametricInstrOk.relabel (h : ParametricInstrOk C i it) :
    ParametricInstrOk (C.reshape C.locals lb r) i it := by
  cases h with
  | unreachable h => exact .unreachable ⟨h.1, h.2.1, h.2.2⟩
  | _ => constructor <;> assumption

theorem _root_.Silmaril.Wasm.Validation.NumericInstrOk.reshape (h : NumericInstrOk C i it) :
    NumericInstrOk (C.reshape lo lb r) i it := by
  cases h <;> constructor
  all_goals assumption

theorem _root_.Silmaril.Wasm.Validation.VectorInstrOk.reshape (h : VectorInstrOk C i it) :
    VectorInstrOk (C.reshape lo lb r) i it := by
  cases h <;> constructor <;> assumption

theorem _root_.Silmaril.Wasm.Validation.MemoryInstrOk.reshape (h : MemoryInstrOk C i it) :
    MemoryInstrOk (C.reshape lo lb r) i it := by
  cases h <;> constructor <;> assumption

theorem _root_.Silmaril.Wasm.Validation.TableInstrOk.reshape (h : TableInstrOk C i it) :
    TableInstrOk (C.reshape lo lb r) i it := by
  cases h <;> constructor <;> assumption

theorem _root_.Silmaril.Wasm.Validation.RefInstrOk.reshape (h : RefInstrOk C i it) :
    RefInstrOk (C.reshape lo lb r) i it := by
  cases h <;> constructor <;> assumption

theorem _root_.Silmaril.Wasm.Validation.VariableInstrOk.relabel (h : VariableInstrOk C i it) :
    VariableInstrOk (C.reshape C.locals lb r) i it := by
  cases h <;> constructor <;> assumption

end transfer

/-! ## `CtxLe`: more locals set, everything else equal -/

/-- `C ≤ C'`: `C'` is `C` with (weakly) more locals set. -/
structure CtxLe (C C' : Context) : Prop where
  eq : C' = { C with locals := C'.locals }
  le : LocalsLe C.locals C'.locals

theorem CtxLe.refl (C : Context) : CtxLe C C := ⟨rfl, LocalsLe.refl _⟩

theorem CtxLe.trans {C₁ C₂ C₃ : Context} (h₁ : CtxLe C₁ C₂) (h₂ : CtxLe C₂ C₃) : CtxLe C₁ C₃ := by
  refine ⟨?_, h₁.le.trans h₂.le⟩
  rw [h₂.eq, h₁.eq]

theorem CtxLe.toTypeCtx {C C' : Context} (h : CtxLe C C') : C'.toTypeCtx = C.toTypeCtx := by
  rw [h.eq]

theorem CtxLe.labels {C C' : Context} (h : CtxLe C C') : C'.labels = C.labels := by
  rw [h.eq]

theorem CtxLe.return_ {C C' : Context} (h : CtxLe C C') : C'.return_ = C.return_ := by
  rw [h.eq]

theorem CtxLe.withLabel {C C' : Context} (h : CtxLe C C') (ts : List CValType) :
    CtxLe (C.withLabel ts) (C'.withLabel ts) := by
  obtain ⟨heq, hle⟩ := h
  refine ⟨?_, hle⟩
  rw [heq]; rfl

theorem CtxLe.initLocals {C C' : Context} (h : CtxLe C C') (xs : List Nat) :
    CtxLe (C.initLocals xs) (C'.initLocals xs) := by
  refine ⟨?_, LocalsLe.initLocals h.le xs⟩
  have e1 := C'.initLocals_eq_with xs
  have e2 := C.initLocals_eq_with xs
  generalize C'.initLocals xs = D' at e1 ⊢
  generalize C.initLocals xs = D at e2 ⊢
  rw [e1, e2]
  have e3 := h.eq
  generalize C'.locals = L' at e3
  subst e3
  rfl

theorem CtxLe.self_initLocals (C : Context) (xs : List Nat) : CtxLe C (C.initLocals xs) := by
  refine ⟨C.initLocals_eq_with xs, ?_⟩
  intro y a hy
  rw [Context.initLocals_locals]
  split
  · exact ⟨.set, by simp [hy], fun _ => rfl⟩
  · exact ⟨a.init, by rw [hy], id⟩

theorem CtxLe.instrTypeOk {C C' : Context} (h : CtxLe C C') {it : InstrType}
    (hok : InstrTypeOk C it) : InstrTypeOk C' it :=
  ⟨h.toTypeCtx ▸ hok.1, h.toTypeCtx ▸ hok.2.1, fun x hx => h.le.exists (hok.2.2 x hx)⟩

theorem CtxLe.instrTypeSub {C C' : Context} (h : CtxLe C C') {it it' : InstrType}
    (hs : InstrTypeSub C it it') : InstrTypeSub C' it it' := by
  refine ⟨h.toTypeCtx ▸ hs.1, h.toTypeCtx ▸ hs.2.1, fun x hx hnx => ?_⟩
  obtain ⟨t, ht⟩ := hs.2.2 x hx hnx
  exact ⟨t, h.le.set ht⟩

theorem CtxLe.wf {C C' : Context} (h : CtxLe C C') (hC : C.Wf)
    (hl : ∀ lt ∈ C'.locals, TyOk C'.toTypeCtx lt.type) : C'.Wf := by
  have e := h.eq
  have ht := h.toTypeCtx
  refine ⟨ht ▸ hC.types, ?_, ?_, ?_, ?_, hl, ?_, ?_, ?_⟩
  · rw [e]; exact hC.tags
  · rw [e]; exact hC.globals
  · rw [e]; exact hC.tables
  · rw [e]; exact hC.funcs
  · rw [e]; exact hC.labels
  · rw [e]; exact hC.return_
  · rw [e]; exact hC.elems

/-- Typing is monotone along `CtxLe`. -/
theorem AdminsOk.weaken {s : Store H} {C C' : Context} (hle : CtxLe C C') {as : List Admin}
    {it : InstrType} (h : AdminsOk s C as it) : AdminsOk s C' as it :=
  h.relocal hle.le hle.eq

theorem AdminOk.weaken {s : Store H} {C C' : Context} (hle : CtxLe C C') {a : Admin}
    {it : InstrType} (h : AdminOk s C a it) : AdminOk s C' a it := by
  have := AdminOk.mono h hle.le (r := C.return_) (.inr rfl)
  rw [hle.eq]; exact this

/-! ## Code without control instructions (`Admin.flat`)

The typing of a flat instruction does not look at `LABELS` or `RETURN`, so a typed
flat sequence can be moved between contexts differing only there. Every redex and
reduct of the delegated families is flat. -/

/-- Instructions whose typing ignores `LABELS` and `RETURN`. -/
def _root_.Silmaril.Wasm.Instr.flat : Instr → Bool
  | .block .. | .loop .. | .if_ .. | .br _ | .brIf _ | .brTable .. | .brOnNull _
  | .brOnNonNull _ | .brOnCast .. | .brOnCastFail .. | .return_ | .returnCall _
  | .returnCallRef _ | .returnCallIndirect .. | .tryTable .. => false
  | _ => true

/-- Administrative instructions whose typing ignores `LABELS` and `RETURN`. -/
def Admin.flat : Admin → Bool
  | .plain i => i.flat
  | .ref _ | .callRefType _ | .trap => true
  | _ => false

/-- Every instruction of the sequence is flat. -/
abbrev AllFlat (as : List Admin) : Prop := as.all Admin.flat = true

@[simp] theorem Val.toAdmin_flat (v : Val) : v.toAdmin.flat = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

@[simp] theorem constI32_flat (c : BitVec 32) : (constI32 c).flat = true := Val.toAdmin_flat _

@[simp] theorem allFlat_vals (vs : List Val) : (vals vs).all Admin.flat = true := by
  simp [vals]

theorem Context.initLocals_reshape (C : Context) (lb : List (List CValType))
    (r : Option (List CValType)) (xs : List Nat) :
    (C.reshape C.locals lb r).initLocals xs =
      (C.initLocals xs).reshape (C.initLocals xs).locals lb r := by
  obtain ⟨L₁, h₁, hy₁⟩ := (C.reshape C.locals lb r).initLocals_spec xs
  obtain ⟨L₂, h₂, hy₂⟩ := C.initLocals_spec xs
  have : L₁ = L₂ := List.ext_getElem? fun y => by rw [hy₁ y, hy₂ y]
  rw [h₁, h₂, this]

theorem _root_.Silmaril.Wasm.Validation.InstrOk.relabel {C : Context} {i : Instr}
    {it : InstrType} (h : InstrOk C i it) (hfl : i.flat = true) (lb : List (List CValType))
    (r : Option (List CValType)) :
    InstrOk (C.reshape C.locals lb r) i it := by
  cases h with
  | parametric h => exact .parametric h.relabel
  | numeric h => exact .numeric h.reshape
  | vector h => exact .vector h.reshape
  | «variable» h => exact .variable h.relabel
  | memory h => exact .memory h.reshape
  | table h => exact .table h.reshape
  | reference h => exact .reference h.reshape
  | call hf he => exact .call hf he
  | callRef hd he => exact .callRef hd he
  | callIndirect ht hs hd he => exact .callIndirect ht hs hd he
  | throw hx he hok => exact .throw hx he hok
  | throwRef hok => exact .throwRef hok
  | _ => simp [Instr.flat] at hfl

theorem AdminOk.relabel {s : Store H} {C : Context} {a : Admin} {it : InstrType}
    (h : AdminOk s C a it) (hf : a.flat = true) (lb : List (List CValType))
    (r : Option (List CValType)) : AdminOk s (C.reshape C.locals lb r) a it := by
  cases h with
  | plain h => exact .plain (h.relabel hf lb r)
  | callRefType hok he => exact .callRefType hok he
  | ref h => exact .ref h
  | trap hok => exact .trap hok
  | throwRefInits hok => exact .throwRefInits hok
  | _ => simp [Admin.flat] at hf

theorem AdminsOk.relabel {s : Store H} (lb : List (List CValType)) (r : Option (List CValType)) :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → AllFlat as →
      AdminsOk s (C.reshape C.locals lb r) as it
  | _, _, _, .nil, _ => .nil
  | _, _, _, .single ha, hf => by
      simp only [AllFlat, List.all_cons, List.all_nil, Bool.and_true] at hf
      exact .single (ha.relabel hf lb r)
  | _, _, _, .seq h₁ hx h₂, hf => by
      simp only [AllFlat, List.all_append, Bool.and_eq_true] at hf
      refine .seq (AdminsOk.relabel lb r h₁ hf.1) hx ?_
      rw [Context.initLocals_reshape]
      exact AdminsOk.relabel lb r h₂ hf.2
  | _, _, _, .cons ha hx hs, hf => by
      simp only [AllFlat, List.all_cons, Bool.and_eq_true] at hf
      refine .cons (ha.relabel hf.1 lb r) hx ?_
      rw [Context.initLocals_reshape]
      exact AdminsOk.relabel lb r hs hf.2
  | _, _, _, .sub h hs hok, hf => .sub (AdminsOk.relabel lb r h hf) hs hok
  | _, _, _, .frame h hok, hf => .frame (AdminsOk.relabel lb r h hf) hok

/-! ## The invariant -/

/-- The typing context `Ct` of the code agrees with the frame context `Cf` except on
`LOCALS` (pointwise less initialised), `LABELS` and `RETURN`. -/
structure CtxUnder (Ct Cf : Context) : Prop where
  eq : Ct = Cf.reshape Ct.locals Ct.labels Ct.return_
  le : LocalsLe Ct.locals Cf.locals

theorem CtxUnder.refl (C : Context) : CtxUnder C C := ⟨rfl, LocalsLe.refl _⟩

theorem CtxUnder.reshape_eq {Ct Cf : Context} (h : CtxUnder Ct Cf) (lo : List LocalType)
    (lb : List (List CValType)) (r : Option (List CValType)) :
    Ct.reshape lo lb r = Cf.reshape lo lb r := by
  have e := h.eq
  conv_lhs => rw [e]

theorem CtxUnder.toTypeCtx {Ct Cf : Context} (h : CtxUnder Ct Cf) :
    Ct.toTypeCtx = Cf.toTypeCtx := by
  rw [h.eq]

theorem CtxUnder.withLabel {Ct Cf : Context} (h : CtxUnder Ct Cf) (ts : List CValType) :
    CtxUnder (Ct.withLabel ts) Cf := by
  refine ⟨?_, h.le⟩
  conv_lhs => rw [h.eq]
  rfl

/-- Well-formedness of a typing context: what the regularity of typing needs. -/
abbrev CtxWf (C : Context) : Prop := C.Wf

/-- The conclusion of the generalised preservation lemma: a new frame context `Cf'`
(differing from `Cf` only in its locals) and a new typing context `Ct'` under it,
with more locals set than `Ct`, typing the reduct at the same type. -/
def PresConcl (c c' : Config H) (Cf Ct : Context) (it : InstrType) : Prop :=
  ∃ Cf' Ct', StoreOk c'.store ∧ Extend c.store c'.store ∧ FrameOk c'.store c'.frame Cf' ∧
    Cf' = Cf.reshape Cf'.locals Cf.labels Cf.return_ ∧ CtxUnder Ct' Cf' ∧ CtxLe Ct Ct' ∧
    AdminsOk c'.store Ct' c'.code it

/-- A step that only rewrites the code. -/
theorem PresConcl.same {s : Store H} {f : Frame} {is is' : List Admin} {Cf Ct : Context}
    {it : InstrType} (hs : StoreOk s) (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf)
    (h : AdminsOk s Ct is' it) : PresConcl ⟨s, f, is⟩ ⟨s, f, is'⟩ Cf Ct it :=
  ⟨Cf, Ct, hs, Extend.refl hs, hf, rfl, hu, CtxLe.refl _, h⟩

/-- A step that keeps the frame and whose reduct is typed in the frame context. -/
theorem PresConcl.of_frame {c c' : Config H} {Cf Ct : Context} {it : InstrType}
    (hu : CtxUnder Ct Cf) (_hfr : c'.frame = c.frame) (hs' : StoreOk c'.store)
    (he : Extend c.store c'.store) (hf' : FrameOk c'.store c'.frame Cf)
    (h : AdminsOk c'.store Cf c'.code it) (hfl : AllFlat c'.code) : PresConcl c c' Cf Ct it := by
  refine ⟨Cf, Cf.reshape Cf.locals Ct.labels Ct.return_, hs', he, hf', rfl, ⟨rfl, LocalsLe.refl _⟩,
    ⟨?_, hu.le⟩, AdminsOk.relabel Ct.labels Ct.return_ h hfl⟩
  have e := hu.reshape_eq Cf.locals Ct.labels Ct.return_
  rw [← e]

/-- Moving flat code typed in `Ct` to the frame context. -/
theorem AdminsOk.toFrame {s : Store H} {Ct Cf : Context} {as : List Admin} {it : InstrType}
    (hu : CtxUnder Ct Cf) (h : AdminsOk s Ct as it) (hfl : AllFlat as) : AdminsOk s Cf as it := by
  have h1 := AdminsOk.relabel Cf.labels Cf.return_ h hfl
  rw [hu.reshape_eq] at h1
  exact AdminsOk.weaken (C := Cf.reshape Ct.locals Cf.labels Cf.return_) ⟨rfl, hu.le⟩ h1

/-! ## Well-formed runtime types

`Structinst_ok`/`Arrayinst_ok` (faithful to SpecTec) do not validate the instance's
`TYPE`, so a value `REF.STRUCT_ADDR a` may have an ill-formed type, and a frame
context (`Frame_ok`) need not be well formed (`Context.Wf`): a set local may hold
such a value. `StoreTypesOk` is the missing invariant: with it every runtime value
type is valid in `{}`, and frame contexts are well formed (`FrameOk.ctxWf`). -/

/-- The `TYPE` of every structure and array instance is valid. -/
def StoreTypesOk (s : Store H) : Prop :=
  (∀ si ∈ s.structs, TyOk {} si.type) ∧ (∀ ai ∈ s.arrays, TyOk {} ai.type)

mutual

theorem TyOk.closed_aux : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k}, TyOk Δ t → Δ.types = [] →
    t.freeIdx = []
  | _, _, _, .idx h, ht => by simp [ht] at h
  | _, _, _, .recv _, _ => by simp [Ty.freeIdx]
  | _, _, _, .dt h, ht => by simp only [Ty.freeIdx]; exact TyOk.closed_aux h ht
  | _, _, _, .defn h _, ht => by simp only [Ty.freeIdx]; exact GroupOk2.closed_aux h ht
  | _, _, _, .abs _, _ => by simp [Ty.freeIdx]
  | _, _, _, .bot, _ => by simp [Ty.freeIdx]
  | _, _, _, .use h, ht => by simp only [Ty.freeIdx]; exact TyOk.closed_aux h ht
  | _, _, _, .ref h, ht => by simp only [Ty.freeIdx]; exact TyOk.closed_aux h ht
  | _, _, _, .num _, _ => by simp [Ty.freeIdx]
  | _, _, _, .vec _, _ => by simp [Ty.freeIdx]
  | _, _, _, .refv h, ht => by simp only [Ty.freeIdx]; exact TyOk.closed_aux h ht
  | _, _, _, .botv, _ => by simp [Ty.freeIdx]
  | _, _, _, .val h, ht => by simp only [Ty.freeIdx]; exact TyOk.closed_aux h ht
  | _, _, _, .pack _, _ => by simp [Ty.freeIdx]
  | _, _, _, .field h, ht => by simp only [Ty.freeIdx]; exact TyOk.closed_aux h ht
  | _, _, _, .struct h, ht => by simp only [Ty.freeIdx]; exact TyOk.closed_aux h ht
  | _, _, _, .array h, ht => by simp only [Ty.freeIdx]; exact TyOk.closed_aux h ht
  | _, _, _, .func hp hr, ht => by
    simp only [Ty.freeIdx, TyOk.closed_aux hp ht, TyOk.closed_aux hr ht, List.append_nil]
  | _, _, _, .nil, _ => by simp [Ty.freeIdx]
  | _, _, _, .cons ha hl, ht => by
    simp only [Ty.freeIdx, TyOk.closed_aux ha ht, TyOk.closed_aux hl ht, List.append_nil]

theorem SubOk2.closed_aux : ∀ {Δ : TypeCtx} {st : CSubType} {i : Nat}, SubOk2 Δ st i →
    Δ.types = [] → st.freeIdx = []
  | _, _, _, .noSuper hct, ht => by simp [Ty.freeIdx, TyOk.closed_aux hct ht]
  | _, _, _, .oneSuper hu _ _ hct _, ht => by
    simp [Ty.freeIdx, TyOk.closed_aux hu ht, TyOk.closed_aux hct ht]

theorem GroupOk2.closed_aux : ∀ {Δ : TypeCtx} {g : CRecType} {i : Nat}, GroupOk2 Δ g i →
    Δ.types = [] → g.freeIdx = []
  | _, _, _, .nil, _ => by simp [Ty.freeIdx]
  | _, _, _, .cons h hs, ht => by
    have h1 := SubOk2.closed_aux h ht
    have h2 := GroupOk2.closed_aux hs ht
    simp only [Ty.freeIdx] at h2 ⊢
    simp [h1, h2]

end

/-- What `Externaddr_ok` tells about the validity of the components of an extern type. -/
def ExternTyOk0 : CExternType → Prop
  | .tag d => TyOk {} d
  | .global g => TyOk {} g.type
  | .mem _ => True
  | .table t => TyOk {} t.element
  | .func d => TyOk {} d

theorem ExternAddrOk.tyOk0 {s : Store H} (hs : StoreOk s) {xa : ExternAddr} {xt : CExternType}
    (h : ExternAddrOk s xa xt) : ExternTyOk0 xt := by
  induction h with
  | tag h => exact (hs.tags _ (List.mem_of_getElem? h)).1
  | global h => exact (hs.globals _ (List.mem_of_getElem? h)).1
  | mem _ => trivial
  | table h => exact (hs.tables _ (List.mem_of_getElem? h)).1.2
  | func h => cases hs.funcs _ (List.mem_of_getElem? h) <;> assumption
  | sub _ hok _ _ =>
    cases hok with
    | tag h => exact h.1
    | global h => exact h
    | mem _ => trivial
    | table h => exact h.2
    | func h _ => exact h

/-- Frame contexts are well formed (given `StoreTypesOk`). -/
theorem FrameOk.ctxWf {s : Store H} {f : Frame} {C : Context} (hs : StoreOk s)
    (_ht : StoreTypesOk s) (hf : FrameOk s f C) : CtxWf C := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := hf
  cases hm with
  | mk htypes htags hglobals hfuncs hmems htables _ helems =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd
      have := htypes d hd
      exact ⟨TyOk.closed_of_empty this, TyOk.of_empty _ this⟩
    · intro d hd
      obtain ⟨a, -, h⟩ := forall₂_mem_right htags d hd
      exact TyOk.of_empty _ (h.tyOk0 hs)
    · intro g hg
      obtain ⟨a, -, h⟩ := forall₂_mem_right hglobals g hg
      exact TyOk.of_empty _ (h.tyOk0 hs)
    · intro t htb
      obtain ⟨a, -, h⟩ := forall₂_mem_right htables t htb
      exact TyOk.of_empty _ (h.tyOk0 hs)
    · intro d hd
      obtain ⟨a, -, h⟩ := forall₂_mem_right hfuncs d hd
      exact TyOk.of_empty _ (h.tyOk0 hs)
    · intro lt hlt
      simp only [List.nil_append] at hlt
      obtain ⟨v, -, h⟩ := forall₂_mem_right hl lt hlt
      refine TyOk.of_empty _ ?_
      cases h with
      | set h => exact h.tyOk_empty hs
      | unset h => exact h
    · intro ts h; simp at h
    · intro ts h; simp at h
    · intro rt hrt
      obtain ⟨a, -, ei, -, hei, rfl⟩ := forall₂_mem_right helems rt hrt
      exact TyOk.of_empty _ hei.1

theorem _root_.Silmaril.Wasm.Validation.Context.Wf.withReturn {C : Context} (hC : C.Wf)
    {ts : List CValType} (h : ResultOk C.toTypeCtx ts) :
    ({ C with return_ := some ts } : Context).Wf :=
  ⟨hC.types, hC.tags, hC.globals, hC.tables, hC.funcs, hC.locals, hC.labels,
    fun ts' e => by cases e; exact h, hC.elems⟩

theorem _root_.Silmaril.Wasm.Validation.Context.Wf.withLabel {C : Context} (hC : C.Wf)
    {ts : List CValType} (h : ResultOk C.toTypeCtx ts) : (C.withLabel ts).Wf := by
  refine ⟨hC.types, hC.tags, hC.globals, hC.tables, hC.funcs, hC.locals, ?_, hC.return_, hC.elems⟩
  intro ts' hts'
  rcases List.mem_cons.mp hts' with rfl | h'
  · exact h
  · exact hC.labels ts' h'

/-! ## Full regularity (given `StoreTypesOk`) -/

mutual

theorem AdminOk.regular {s : Store H} (hs : StoreOk s) (ht : StoreTypesOk s) :
    ∀ {C : Context} {a : Admin} {it : InstrType}, C.Wf → AdminOk s C a it → InstrTypeOk C it
  | _, _, _, hC, .plain h => h.regular hC
  | C, _, _, _, .callRefType hok hex => by
    have hok := TyOk.of_empty C.toTypeCtx hok
    have := Expand.func_ok hok hex
    refine ⟨ResultOk.append this.1 ?_, this.2, by simp⟩
    simp [hok]
  | C, _, _, _, .returnCallRefType hok hex _ _ hit => by
    have hok := TyOk.of_empty C.toTypeCtx hok
    have := Expand.func_ok hok hex
    refine ⟨ResultOk.append (ResultOk.append hit.1 this.1) ?_, hit.2.1, by simp⟩
    simp [hok]
  | _, _, _, _, .ref h => by
    refine ⟨by simp, ?_, by simp⟩
    simp only [ResultOk.cons_iff, ResultOk.nil_iff, and_true]
    exact .refv (TyOk.of_empty _ (h.tyOk_empty hs))
  | _, _, _, hC, .label _ hc _ => ⟨by simp, (AdminsOk.regular hs ht hC hc).2.1, by simp⟩
  | _, _, _, _, .frame _ _ _ hok => ⟨by simp, fun t h => TyOk.of_empty _ (hok t h), by simp⟩
  | _, _, _, hC, .handler _ hb => ⟨by simp, (AdminsOk.regular hs ht hC hb).2.1, by simp⟩
  | _, _, _, _, .trap hok => hok
  | _, _, _, _, .throwRefInits hok => hok

theorem AdminsOk.regular {s : Store H} (hs : StoreOk s) (ht : StoreTypesOk s) :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, C.Wf → AdminsOk s C as it →
      InstrTypeOk C it
  | _, _, _, _, .nil => ⟨by simp, by simp, by simp⟩
  | _, _, _, hC, .single h => AdminOk.regular hs ht hC h
  | _, _, _, hC, .seq h₁ hx h₂ => by
    have r₁ := AdminsOk.regular hs ht hC h₁
    have r₂ := AdminsOk.regular hs ht (hC.initLocals _) h₂
    refine ⟨r₁.1, by simpa using r₂.2.1, fun x hx' => ?_⟩
    rcases List.mem_append.mp hx' with h | h
    · exact hx x h
    · exact Context.initLocals_exists.mp (r₂.2.2 x h)
  | _, _, _, hC, .cons ha hx hs' => by
    have r₁ := AdminOk.regular hs ht hC ha
    have r₂ := AdminsOk.regular hs ht (hC.initLocals _) hs'
    refine ⟨r₁.1, by simpa using r₂.2.1, fun x hx' => ?_⟩
    rcases List.mem_append.mp hx' with h | h
    · exact hx x h
    · exact Context.initLocals_exists.mp (r₂.2.2 x h)
  | _, _, _, _, .sub _ _ hok => hok
  | _, _, _, hC, .frame h hok => by
    have r := AdminsOk.regular hs ht hC h
    exact ⟨ResultOk.append hok r.1, ResultOk.append hok r.2.1, r.2.2⟩

end

/-! ## Values initialise no locals -/

theorem AdminOk.toAdmin_inits {s : Store H} {C : Context} {v : Val} {it : InstrType}
    (h : AdminOk s C v.toAdmin it) : it.inits = [] := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ | b | r
  · cases h with
    | plain h =>
      cases h <;> try (rename_i hh; cases hh)
      all_goals rfl
  · cases h with
    | plain h =>
      cases h <;> try (rename_i hh; cases hh)
      all_goals rfl
  · cases h with
    | plain h =>
      cases h <;> try (rename_i hh; cases hh)
      all_goals rfl
  · cases h with
    | ref h => rfl

/-! ## Replacing the single instruction of a typed singleton -/

/-- A typed singleton `[a]` has a unique leaf `AdminOk s C a it₀`; replacing it by any
`a'` of the same type, in a context with more locals set and an extended store,
types `[a']` at the original type. -/
theorem AdminsOk.single_decomp {s : Store H} (hS : StoreOk s) :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → ∀ a, as = [a] →
      C.toTypeCtx.Ok →
      ∃ it₀, AdminOk s C a it₀ ∧ ∀ (s' : Store H) (C' : Context) (a' : Admin),
        Extend s s' → CtxLe C C' → AdminOk s' C' a' it₀ → AdminsOk s' C' [a'] it
  | _, _, _, .nil, _, e, _ => by cases e
  | _, _, it, .single h, a, e, _ => by
    cases e
    exact ⟨it, h, fun _ _ _ _ _ h' => .single h'⟩
  | _, _, _, .cons ha hx hs, a, e, _ => by
    obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp e
    exact ⟨_, ha, fun s' C' a' he hle h' =>
      .cons h' (fun x hx' => hle.le.exists (hx x hx'))
        ((hs.extend hS he).weaken (hle.initLocals _))⟩
  | C, _, _, .seq (xs₁ := xs₁) h₁ hx h₂, a, e, hΔ => by
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    rcases List.append_eq_singleton_iff.mp e with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · obtain ⟨_, _, _, i₁⟩ := AdminsOk.nil_aux h₁ e₁ hΔ
      have hC : C.initLocals xs₁ = C := Context.initLocals_of_set i₁
      obtain ⟨it₀, ha, k⟩ := AdminsOk.single_decomp hS h₂ a e₂ hΔ'
      rw [hC] at ha
      subst e₁
      refine ⟨it₀, ha, fun s' C' a' he hle h' => ?_⟩
      have hle' : CtxLe (C.initLocals xs₁) C' := by rw [hC]; exact hle
      have hC' : C'.initLocals xs₁ = C' :=
        Context.initLocals_of_set fun x hx' => by
          obtain ⟨t, ht⟩ := i₁ x hx'; exact ⟨t, hle.le.set ht⟩
      have h₂' := k s' C' a' he hle' h'
      rw [← hC'] at h₂'
      exact .seq ((h₁.extend hS he).weaken hle) (fun x hx' => hle.le.exists (hx x hx')) h₂'
    · obtain ⟨it₀, ha, k⟩ := AdminsOk.single_decomp hS h₁ a e₁ hΔ
      subst e₂
      refine ⟨it₀, ha, fun s' C' a' he hle h' => ?_⟩
      have := AdminsOk.seq (k s' C' a' he hle h') (fun x hx' => hle.le.exists (hx x hx'))
        ((h₂.extend hS he).weaken (hle.initLocals _))
      simpa using this
  | _, _, _, .sub h hs hok, a, e, hΔ => by
    obtain ⟨it₀, ha, k⟩ := AdminsOk.single_decomp hS h a e hΔ
    exact ⟨it₀, ha, fun s' C' a' he hle h' =>
      .sub (k s' C' a' he hle h') (hle.instrTypeSub hs) (hle.instrTypeOk hok)⟩
  | _, _, _, .frame h hok, a, e, hΔ => by
    obtain ⟨it₀, ha, k⟩ := AdminsOk.single_decomp hS h a e hΔ
    exact ⟨it₀, ha, fun s' C' a' he hle h' => .frame (k s' C' a' he hle h') (hle.toTypeCtx ▸ hok)⟩

end Silmaril.Wasm.Execution.Core
