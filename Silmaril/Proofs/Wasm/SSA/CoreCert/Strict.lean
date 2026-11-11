module

public import Silmaril.Wasm.SSA.CoreCert.Leaf.Defs
public import Silmaril.Wasm.Execution.Core.Sim.Closure

@[expose] public section

/-!
# Strict leaf frames (proofs)

A Core 3.0 frame running **strict leaf code** (`SAdmins`: `strictInstr` instructions, numeric
and vector constants, labels and traps; no references, calls, handlers or nested frames) on
reference-free locals (`FrameS`) evolves independently of everything around it:

* `step_strict`: a step of strict leaf code keeps the store and the frame's module instance,
  stays strict, and is a step from the same code in **any** store, under **any** host, with the
  frame's module instance replaced by **any** other (`withMod`);
* `frame_step`: a step of a strict frame administrative instruction `FRAME_n{fr} b` keeps the
  store and the enclosing frame, is a step under any store, host, enclosing frame and module
  instance of `fr` (`swapA`), and leads to a strict frame or to a result (values or a trap);
* `frame_behaviours`: hence the Core behaviours of a strict frame, in any store and enclosing
  frame, are those of its canonical form `canon X` (empty store, closed host, the frame's module
  instance replaced by the empty one), `LBeh P X`.

New proofs, by induction on the rules of `Step` in the style of
`Silmaril.Proofs.Wasm.SSA.CoreCert.step_swap`.
-/

namespace Silmaril.Proofs.Wasm.SSA.CoreCert

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SSA
open Silmaril.Wasm.SSA.CoreCert

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- The locals of a strict leaf frame hold no references. -/
def FrameS (fr : Frame) : Prop := ∀ v, some v ∈ fr.locals → ValS v

mutual
/-- Administrative instructions of strict leaf code. -/
def SAdmin : Admin → Prop
  | .plain i => strictInstr i = true
  | .label _ cont body => strictInstrs cont = true ∧ SAdmins body
  | .trap => True
  | _ => False
/-- `SAdmin` on a sequence. -/
def SAdmins : List Admin → Prop
  | [] => True
  | c :: cs => SAdmin c ∧ SAdmins cs
end

section Simp

@[simp] theorem sAdmins_nil : SAdmins [] := trivial
@[simp] theorem sAdmins_cons {c : Admin} {cs : List Admin} :
    SAdmins (c :: cs) ↔ SAdmin c ∧ SAdmins cs := Iff.rfl
@[simp] theorem sAdmins_append {as bs : List Admin} :
    SAdmins (as ++ bs) ↔ SAdmins as ∧ SAdmins bs := by
  induction as with
  | nil => simp
  | cons c as ih => simp [ih, and_assoc]
@[simp] theorem sAdmin_plain {i : Instr} : SAdmin (.plain i) ↔ strictInstr i = true := Iff.rfl
@[simp] theorem sAdmin_label {n : Nat} {cont : List Instr} {body : List Admin} :
    SAdmin (.label n cont body) ↔ strictInstrs cont = true ∧ SAdmins body := Iff.rfl
@[simp] theorem sAdmin_trap : SAdmin .trap := trivial
@[simp] theorem not_sAdmin_ref {r : Ref} : ¬ SAdmin (.ref r) := id
@[simp] theorem not_sAdmin_frame {n : Nat} {fr : Frame} {b : List Admin} :
    ¬ SAdmin (.frame n fr b) := id
@[simp] theorem not_sAdmin_handler {n : Nat} {cs : List Catch} {b : List Admin} :
    ¬ SAdmin (.handler n cs b) := id
@[simp] theorem not_sAdmin_callRefType {d : Validation.DefType} : ¬ SAdmin (.callRefType d) := id
@[simp] theorem not_sAdmin_returnCallRefType {d : Validation.DefType} :
    ¬ SAdmin (.returnCallRefType d) := id

@[simp] theorem sAdmin_toAdmin (v : Val) : SAdmin v.toAdmin ↔ ValS v := by
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [Val.toAdmin, ValS, strictInstr]

@[simp] theorem sAdmins_vals (vs : List Val) : SAdmins (vals vs) ↔ ∀ v ∈ vs, ValS v := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih => simp [vals] at ih ⊢; simp [ih]

@[simp] theorem sAdmin_constI32 (b : BitVec 32) : SAdmin (constI32 b) :=
  (sAdmin_toAdmin (Val.i32 b)).mpr trivial

@[simp] theorem sAdmins_expression_iff {is : List Instr} :
    SAdmins (expression is) ↔ strictInstrs is = true := by
  induction is with
  | nil => exact iff_of_true trivial rfl
  | cons i is ih =>
    have e : expression (i :: is) = .plain i :: expression is := rfl
    rw [e, sAdmins_cons, ih, sAdmin_plain]
    simp only [strictInstrs, Bool.and_eq_true]

theorem not_sAdmin_returnCallRef {c : Admin} (hc : c.IsReturnCallRef) : ¬ SAdmin c := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · simp [strictInstr]
  · exact id
  · exact absurd hc id

theorem sAdmin_of_mem {l : List Admin} (h : SAdmins l) {x : Admin} (hx : x ∈ l) : SAdmin x := by
  induction l with
  | nil => cases hx
  | cons y l ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact ih h.2 hx

@[simp] theorem withMod_local? (fr : Frame) (mi : ModuleInst) (x : LocalIdx) :
    (withMod fr mi).local? x = fr.local? x := rfl
@[simp] theorem withMod_locals (fr : Frame) (mi : ModuleInst) :
    (withMod fr mi).locals = fr.locals := rfl
@[simp] theorem withMod_module (fr : Frame) (mi : ModuleInst) : (withMod fr mi).module = mi := rfl
theorem withMod_setLocal (fr : Frame) (mi : ModuleInst) (x : LocalIdx) (v : Val) :
    withMod (fr.setLocal x v) mi = (withMod fr mi).setLocal x v := rfl
@[simp] theorem withMod_withMod (fr : Frame) (mi mi' : ModuleInst) :
    withMod (withMod fr mi) mi' = withMod fr mi' := rfl
theorem withMod_self (fr : Frame) : withMod fr fr.module = fr := rfl

end Simp

/-- An inline block type has the same arities in every module instance. -/
theorem blockType_inline {bt : BlockType} (hb : inlineBT bt = true) {m : ModuleInst}
    {t₁ t₂ : List Validation.CValType} (h : m.blockType? bt = some (t₁, t₂)) (m' : ModuleInst) :
    ∃ t₁' t₂', m'.blockType? bt = some (t₁', t₂') ∧ t₁'.length = t₁.length ∧
      t₂'.length = t₂.length := by
  cases bt with
  | empty =>
    simp only [ModuleInst.blockType?, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], [], ⟨rfl, rfl⟩, rfl, rfl⟩
  | value t =>
    simp only [ModuleInst.blockType?, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], _, ⟨rfl, rfl⟩, rfl, rfl⟩
  | typeIdx x => simp [inlineBT] at hb

theorem frameS_setLocal {f : Frame} (hf : FrameS f) (x : LocalIdx) {v : Val} (hv : ValS v) :
    FrameS (f.setLocal x v) := by
  intro w hw
  simp only [Frame.setLocal] at hw
  rcases List.mem_or_eq_of_mem_set hw with hw | hw
  · exact hf w hw
  · cases hw
    exact hv

/-! ## One step of strict leaf code -/

/-- What a step of strict leaf code gives. -/
def SSwap (P : Numerics.Profile) (c c' : Config H) : Prop :=
  c'.store = c.store ∧ c'.frame.module = c.frame.module ∧ SAdmins c'.code ∧ FrameS c'.frame ∧
    ∀ {H' : Type} (host' : HostSemantics H') (t : Store H') (mi : ModuleInst),
      Step P host' ⟨t, withMod c.frame mi, c.code⟩ ⟨t, withMod c'.frame mi, c'.code⟩

macro "s_simp" : tactic => `(tactic| simp_all [strictInstr, strictInstrs, ValS, throwing,
  Admin.IsCallRef, Admin.IsReturnCallRef])

/-- Local variable steps of strict leaf code. -/
theorem strict_variable {c c' : Config H} (h : VariableStep c c') (hp : SAdmins c.code)
    (hfr : FrameS c.frame) : SSwap P c c' := by
  cases h with
  | localGet hv =>
    exact ⟨rfl, rfl, by simpa using hfr _ (List.mem_of_getElem? hv), hfr,
      fun _ _ _ => .variable (.localGet hv)⟩
  | @localSet s f x v hx =>
    have hv : ValS v := (sAdmin_toAdmin v).mp hp.1
    exact ⟨rfl, rfl, trivial, frameS_setLocal hfr _ hv, fun _ _ mi => by
      rw [withMod_setLocal]; exact .variable (.localSet hx)⟩
  | @localTee s f x v =>
    have hv : ValS v := (sAdmin_toAdmin v).mp hp.1
    exact ⟨rfl, rfl, by simp [hv, strictInstr], hfr, fun _ _ _ => .variable .localTee⟩
  | globalGet => exfalso; s_simp
  | globalSet => exfalso; s_simp

/-- `block` in strict leaf code. -/
theorem strict_block {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr}
    {vs : List Val} {t₁ t₂ : List Validation.CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length) (hp : SAdmins (vals vs ++ [.plain (.block bt body)]))
    (hfr : FrameS f) :
    SSwap P ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
      ⟨s, f, [.label t₂.length [] (vals vs ++ expression body)]⟩ := by
  have hp₀ : SAdmins (vals vs) ∧ SAdmins [.plain (.block bt body)] := sAdmins_append.mp hp
  have hb : inlineBT bt = true ∧ strictInstrs body = true := by
    simpa [strictInstr] using hp₀.2.1
  refine ⟨rfl, rfl, ⟨⟨rfl, sAdmins_append.mpr ⟨hp₀.1, by simpa using hb.2⟩⟩, trivial⟩, hfr,
    fun host' t mi => ?_⟩
  obtain ⟨t₁', t₂', hbt', h1, h2⟩ := blockType_inline hb.1 hbt mi
  have hst : Step P host' ⟨t, withMod f mi, vals vs ++ [.plain (.block bt body)]⟩
      ⟨t, withMod f mi, [.label t₂'.length [] (vals vs ++ expression body)]⟩ :=
    Step.block hbt' (hm.trans h1.symm)
  rwa [h2] at hst

/-- `loop` in strict leaf code. -/
theorem strict_loop {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr}
    {vs : List Val} {t₁ t₂ : List Validation.CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length) (hp : SAdmins (vals vs ++ [.plain (.loop bt body)]))
    (hfr : FrameS f) :
    SSwap P ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
      ⟨s, f, [.label t₁.length [.loop bt body] (vals vs ++ expression body)]⟩ := by
  have hp₀ : SAdmins (vals vs) ∧ SAdmins [.plain (.loop bt body)] := sAdmins_append.mp hp
  have hb : inlineBT bt = true ∧ strictInstrs body = true := by
    simpa [strictInstr] using hp₀.2.1
  refine ⟨rfl, rfl, ⟨⟨by simpa [strictInstrs] using hp₀.2.1,
    sAdmins_append.mpr ⟨hp₀.1, by simpa using hb.2⟩⟩, trivial⟩, hfr, fun host' t mi => ?_⟩
  obtain ⟨t₁', t₂', hbt', h1, h2⟩ := blockType_inline hb.1 hbt mi
  have hst : Step P host' ⟨t, withMod f mi, vals vs ++ [.plain (.loop bt body)]⟩
      ⟨t, withMod f mi, [.label t₁'.length [.loop bt body] (vals vs ++ expression body)]⟩ :=
    Step.loop hbt' (hm.trans h1.symm)
  rwa [h1] at hst

/-- **A step of strict leaf code** keeps the store and the module instance, stays strict, and
is a step in any store, under any host, with any module instance. -/
theorem step_strict {c c' : Config H} (h : Step P host c c') (hp : SAdmins c.code)
    (hfr : FrameS c.frame) : SSwap P c c' := by
  induction h with
  | parametric h => exact ⟨rfl, rfl, by cases h <;> s_simp, hfr, fun _ _ _ => .parametric h⟩
  | numeric h => exact ⟨rfl, rfl, by cases h <;> s_simp, hfr, fun _ _ _ => .numeric h⟩
  | vector h => exfalso; cases h <;> s_simp
  | «variable» h => exact strict_variable h hp hfr
  | table h => exfalso; cases h <;> s_simp
  | memory h => exfalso; cases h <;> s_simp
  | reference h => exfalso; cases h <;> s_simp
  | aggregate h => exfalso; cases h <;> s_simp
  | @ctxtInstrs s s' f f' vs is is' rest _ hne ih =>
    have hp₀ : (SAdmins (vals vs) ∧ SAdmins is) ∧ SAdmins rest := by
      simpa only [sAdmins_append] using hp
    obtain ⟨hs, hm, hp₁, hf₁, hst⟩ := ih hp₀.1.2 hfr
    exact ⟨hs, hm, sAdmins_append.mpr ⟨sAdmins_append.mpr ⟨hp₀.1.1, hp₁⟩, hp₀.2⟩, hf₁,
      fun host' t mi => .ctxtInstrs (hst host' t mi) hne⟩
  | ctxtLabel _ ih =>
    obtain ⟨hs, hm, hp₁, hf₁, hst⟩ := ih hp.1.2 hfr
    exact ⟨hs, hm, ⟨⟨hp.1.1, hp₁⟩, trivial⟩, hf₁, fun host' t mi => .ctxtLabel (hst host' t mi)⟩
  | ctxtHandler => exact absurd hp.1 not_sAdmin_handler
  | ctxtFrame => exact absurd hp.1 not_sAdmin_frame
  | block hbt hm => exact strict_block hbt hm hp hfr
  | loop hbt hm => exact strict_loop hbt hm hp hfr
  | ifTrue hc => exact ⟨rfl, rfl, by s_simp, hfr, fun _ _ _ => .ifTrue hc⟩
  | ifFalse => exact ⟨rfl, rfl, by s_simp, hfr, fun _ _ _ => .ifFalse⟩
  | labelVals => exact ⟨rfl, rfl, by s_simp, hfr, fun _ _ _ => .labelVals⟩
  | brLabelZero hl hn => exact ⟨rfl, rfl, by s_simp, hfr, fun _ _ _ => .brLabelZero hl hn⟩
  | brLabelSucc hl => exact ⟨rfl, rfl, by s_simp, hfr, fun _ _ _ => .brLabelSucc hl⟩
  | brIfTrue hc => exact ⟨rfl, rfl, by s_simp, hfr, fun _ _ _ => .brIfTrue hc⟩
  | brIfFalse => exact ⟨rfl, rfl, by s_simp, hfr, fun _ _ _ => .brIfFalse⟩
  | brTableLt hi => exact ⟨rfl, rfl, by s_simp, hfr, fun _ _ _ => .brTableLt hi⟩
  | brTableGe hi => exact ⟨rfl, rfl, by s_simp, hfr, fun _ _ _ => .brTableGe hi⟩
  | returnLabel => exact ⟨rfl, rfl, by s_simp, hfr, fun _ _ _ => .returnLabel⟩
  | trapInstrs hne => exact ⟨rfl, rfl, by s_simp, hfr, fun _ _ _ => .trapInstrs hne⟩
  | trapLabel => exact ⟨rfl, rfl, by s_simp, hfr, fun _ _ _ => .trapLabel⟩
  | returnCallRefLabel hc =>
    exact absurd (sAdmin_of_mem hp.1.2 (by simp)) (not_sAdmin_returnCallRef hc)
  | _ => exfalso; s_simp

/-! ## Strict frames -/

/-- A strict frame administrative instruction `FRAME_n{fr} b`. -/
def LFrame (X : Admin) : Prop := ∃ n fr b, X = .frame n fr b ∧ SAdmins b ∧ FrameS fr

/-- `swapA` on a sequence. -/
def swapL (mi : ModuleInst) (l : List Admin) : List Admin := l.map (swapA mi)

/-- What a strict frame steps to: a strict frame, values, or a trap. -/
def FrameNext (l : List Admin) : Prop :=
  (∃ X, l = [X] ∧ LFrame X) ∨ (∃ vs, l = vals vs ∧ ∀ v ∈ vs, ValS v) ∨ l = [.trap]

@[simp] theorem swapA_toAdmin (mi : ModuleInst) (v : Val) : swapA mi v.toAdmin = v.toAdmin := by
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> rfl

@[simp] theorem swapL_vals (mi : ModuleInst) (vs : List Val) : swapL mi (vals vs) = vals vs := by
  simp [swapL, vals, List.map_map, Function.comp_def]

@[simp] theorem swapL_trap (mi : ModuleInst) : swapL mi [.trap] = [.trap] := rfl

@[simp] theorem swapA_trap (mi : ModuleInst) : swapA mi .trap = .trap := rfl
@[simp] theorem swapA_ref (mi : ModuleInst) (r : Ref) : swapA mi (.ref r) = .ref r := rfl
@[simp] theorem swapA_plain (mi : ModuleInst) (i : Instr) : swapA mi (.plain i) = .plain i := rfl

@[simp] theorem swapL_toAdmin (mi : ModuleInst) (r : Result) : swapL mi r.toAdmin = r.toAdmin := by
  cases r with
  | values vs => exact swapL_vals mi vs
  | throw a => rfl
  | trap => rfl

@[simp] theorem swapL_single (mi : ModuleInst) (X : Admin) : swapL mi [X] = [swapA mi X] := rfl

theorem swapA_swapA (mi mi' : ModuleInst) (X : Admin) :
    swapA mi (swapA mi' X) = swapA mi X := by
  cases X <;> rfl

theorem lFrame_swapA {X : Admin} (h : LFrame X) (mi : ModuleInst) : LFrame (swapA mi X) := by
  obtain ⟨n, fr, b, rfl, hb, hf⟩ := h
  exact ⟨n, withMod fr mi, b, rfl, hb, hf⟩

/-- The module instance of a frame administrative instruction. -/
def modOf : Admin → ModuleInst
  | .frame _ fr _ => fr.module
  | _ => {}

theorem swapA_modOf {X : Admin} (h : LFrame X) : swapA (modOf X) X = X := by
  obtain ⟨n, fr, b, rfl, -, -⟩ := h
  rfl

/-- `[trap]` does not step. -/
theorem not_step_trap {s : Store H} {f : Frame} {c : Config H} :
    ¬ Step P host ⟨s, f, [.trap]⟩ c := fun h => by
  obtain ⟨-, -, p, w, q, hu, hw, -⟩ := Sim.Step.trap_redex_aux h [] rfl
  have hnil : p ++ w ++ q = [] := hu.symm
  exact hw (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hnil).1).2

/-- A result (values or trap) does not step. -/
theorem not_step_next {s : Store H} {f : Frame} {l : List Admin} {c : Config H}
    (hl : (∃ vs, l = vals vs ∧ ∀ v ∈ vs, ValS v) ∨ l = [.trap]) : ¬ Step P host ⟨s, f, l⟩ c := by
  rcases hl with ⟨vs, rfl, -⟩ | rfl
  · exact Step.not_vals
  · exact not_step_trap

/-- **A step of a strict frame**: same store and enclosing frame, a strict frame or a result,
and a step under any store, host, enclosing frame and module instance. -/
theorem frame_step {s s' : Store H} {F F' : Frame} {X : Admin} {l : List Admin}
    (hX : LFrame X) (h : Step P host ⟨s, F, [X]⟩ ⟨s', F', l⟩) :
    s' = s ∧ F' = F ∧ FrameNext l ∧
      ∀ {H' : Type} (host' : HostSemantics H') (t : Store H') (F₀ : Frame) (mi : ModuleInst),
        Step P host' ⟨t, F₀, [swapA mi X]⟩ ⟨t, F₀, swapL mi l⟩ := by
  obtain ⟨n, fr, b, rfl, hb, hf⟩ := hX
  obtain ⟨is₀, his, hr⟩ : ∃ is₀, l = vals [] ++ is₀ ∧
      Sim.Closure.FrameRedex P host s F n fr b s' F' is₀ :=
    Sim.Closure.Step.frame_redex_aux h [] n fr b rfl
  have hl : l = is₀ := by simpa [vals] using his
  subst hl
  cases hr with
  | ctxt hs =>
    obtain ⟨hs', -, hb', hf', hst⟩ := step_strict hs hb hf
    exact ⟨hs', rfl, .inl ⟨_, rfl, _, _, _, rfl, hb', hf'⟩,
      fun host' t F₀ mi => .ctxtFrame (hst host' t mi)⟩
  | values hn =>
    have hv : ∀ v ∈ _, ValS v := (sAdmins_vals _).mp hb
    exact ⟨rfl, rfl, .inr (.inl ⟨_, rfl, hv⟩), fun _ _ _ mi => by
      rw [swapL_vals]; exact .frameVals hn⟩
  | ret hn =>
    have hvs : SAdmins (vals _) := (sAdmins_append.mp (sAdmins_append.mp (sAdmins_append.mp hb).1).1).2
    have hv : ∀ v ∈ _, ValS v := (sAdmins_vals _).mp hvs
    exact ⟨rfl, rfl, .inr (.inl ⟨_, rfl, hv⟩), fun _ _ _ mi => by
      rw [swapL_vals]; exact .returnFrame hn⟩
  | callNull hc => exact absurd hb (by simp)
  | callAddr hc hf he hn => exact absurd hb (by simp)
  | throw => exact absurd hb (by simp [throwing])
  | trap => exact ⟨rfl, rfl, .inr (.inr rfl), fun _ _ _ _ => .trapFrame⟩

/-! ## Runs and divergence of strict frames, transported -/

/-- The invariant of a run from a strict frame `X` in store `s` and enclosing frame `F`. -/
def FrameRun (P : Numerics.Profile) (s : Store H) (F : Frame) (X : Admin) (c : Config H) : Prop :=
  c.store = s ∧ c.frame = F ∧ FrameNext c.code ∧
    ∀ {H' : Type} (host' : HostSemantics H') (t : Store H') (F₀ : Frame) (mi : ModuleInst),
      Steps P host' ⟨t, F₀, [swapA mi X]⟩ ⟨t, F₀, swapL mi c.code⟩

theorem frameRun_step {s : Store H} {F : Frame} {X : Admin} {c c' : Config H}
    (hc : FrameRun P s F X c) (h : Step P host c c') : FrameRun P s F X c' := by
  obtain ⟨hs, hF, hn, hrun⟩ := hc
  obtain ⟨s₁, f₁, l₁⟩ := c
  obtain ⟨s₂, f₂, l₂⟩ := c'
  dsimp only at hs hF hn hrun ⊢
  subst hs hF
  rcases hn with ⟨X', rfl, hX'⟩ | hres
  · obtain ⟨rfl, rfl, hn', hst⟩ := frame_step hX' h
    exact ⟨rfl, rfl, hn', fun host' t F₀ mi =>
      (hrun host' t F₀ mi).tail (by simpa using hst host' t F₀ mi)⟩
  · exact (not_step_next hres h).elim

/-- **Runs of a strict frame transport** to any store, host, enclosing frame and module. -/
theorem frame_steps {s : Store H} {F : Frame} {X : Admin} (hX : LFrame X) {c : Config H}
    (h : Steps P host ⟨s, F, [X]⟩ c) : FrameRun P s F X c := by
  induction h with
  | refl => exact ⟨rfl, rfl, .inl ⟨X, rfl, hX⟩, fun _ _ _ _ => by simpa using .refl⟩
  | tail _ hs ih => exact frameRun_step ih hs

/-- **Divergence of a strict frame transports** to any store, host, enclosing frame and
module. -/
theorem frame_diverges {s : Store H} {F : Frame} {X : Admin} (hX : LFrame X)
    (h : Diverges P host ⟨s, F, [X]⟩) {H' : Type} (host' : HostSemantics H') (t : Store H')
    (F₀ : Frame) (mi : ModuleInst) : Diverges P host' ⟨t, F₀, [swapA mi X]⟩ := by
  obtain ⟨g, hg0, hg⟩ := h
  have inv : ∀ n, FrameRun P s F X (g n) ∧ ∃ X', (g n).code = [X'] ∧ LFrame X' := by
    intro n
    induction n with
    | zero =>
      rw [hg0]
      exact ⟨frame_steps (host := host) hX .refl, X, rfl, hX⟩
    | succ n ih =>
      show FrameRun P s F X (g (n + 1)) ∧ ∃ X', (g (n + 1)).code = [X'] ∧ LFrame X'
      have hr : FrameRun P s F X (g (n + 1)) := frameRun_step ih.1 (hg n)
      refine ⟨hr, ?_⟩
      rcases hr.2.2.1 with h' | hres
      · exact h'
      · obtain ⟨c'', hc''⟩ : ∃ c'', Step P host (g (n + 1)) c'' := ⟨_, hg (n + 1)⟩
        have e : g (n + 1) = ⟨s, F, (g (n + 1)).code⟩ := by
          rw [← hr.1, ← hr.2.1]
        rw [e] at hc''
        exact (not_step_next hres hc'').elim
  refine ⟨fun n => ⟨t, F₀, swapL mi (g n).code⟩, by simp [hg0], fun n => ?_⟩
  obtain ⟨⟨hs, hF, -, -⟩, X', hX'c, hX'⟩ := inv n
  have hstep : Step P host (g n) (g (n + 1)) := hg n
  have e : g n = ⟨s, F, [X']⟩ := by
    rw [← hs, ← hF, ← hX'c]
  rw [e] at hstep
  generalize hg' : g (n + 1) = c₂ at hstep
  obtain ⟨s₂, f₂, l₂⟩ := c₂
  obtain ⟨-, -, -, hst⟩ := frame_step hX' hstep
  simpa [hX'c, hg'] using hst host' t F₀ mi

/-- Behaviours of a strict frame are included in those of the same frame anywhere else. -/
theorem frame_behaviours_sub {s : Store H} {F : Frame} {X : Admin} (hX : LFrame X)
    {H' : Type} (host' : HostSemantics H') (t : Store H') (F₀ : Frame) (mi : ModuleInst) :
    behavioursOf P host ⟨s, F, [X]⟩ ⊆ behavioursOf P host' ⟨t, F₀, [swapA mi X]⟩ := by
  rintro b (⟨c', r, hst, hcode, rfl⟩ | ⟨rfl, hd⟩)
  · have hr := (frame_steps hX hst).2.2.2 host' t F₀ mi
    refine .inl ⟨⟨t, F₀, swapL mi c'.code⟩, r, hr, ?_, rfl⟩
    rw [hcode, swapL_toAdmin]
  · exact .inr ⟨rfl, frame_diverges hX hd host' t F₀ mi⟩

/-- **The Core behaviours of a strict frame**, in any store and enclosing frame, are its
canonical behaviours. -/
theorem frame_behaviours {s : Store H} {F : Frame} {X : Admin} (hX : LFrame X) :
    behavioursOf P host ⟨s, F, [X]⟩ = LBeh P X := by
  apply Set.Subset.antisymm (frame_behaviours_sub hX _ _ _ _)
  have h := frame_behaviours_sub (P := P) (host := Binaryen.closedHost) (s := ({} : Store Empty))
    (F := {}) (lFrame_swapA hX {}) host s F (modOf X)
  rwa [swapA_swapA, swapA_modOf hX] at h

end Silmaril.Proofs.Wasm.SSA.CoreCert
