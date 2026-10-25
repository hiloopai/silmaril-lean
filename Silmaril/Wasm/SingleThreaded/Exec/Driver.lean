module

public import Silmaril.Wasm.SingleThreaded.Determinism

@[expose] public section

/-! # Computable interpreter driver (single-threaded profile)

A small-step driver generic over a *head-step function*
`head : Store H → Frame → List Val → Admin → Option (Nat × Config H)`: given the
value prefix `vs` and the first non-value `e`, it returns the number `k` of
values consumed and the result of the head step on `vals (last k of vs) ++ [e]`.

`step?` splits the code at its first non-value, bubbles `TRAP` and
`THROW_REF`, tries `head`, and otherwise descends into label, handler and frame
bodies. It is sound for any `head` that is sound, and complete for any `head`
that only fails on context steps (`IsCtxtHead`).
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-! ## Head steps, decomposed steps and bubbles are steps -/

theorem _root_.Silmaril.Wasm.SingleThreaded.Det.Head.toStep {P : Profile} {s : Store H}
    {f : Frame} {args : List Val} {e : Admin} {c : Config H} (h : Head P s f args e c) :
    Step P noHost ⟨s, f, vals args ++ [e]⟩ c := by
  cases h with
  | parametric h => exact .parametric h
  | numeric h => exact .numeric h
  | vector h => exact .vector h
  | «variable» h => exact .variable h
  | table h => exact .table h
  | memory h => exact .memory h
  | reference h => exact .reference h
  | aggregate h => exact .aggregate h
  | ctxtLabel h => exact .ctxtLabel h
  | ctxtHandler h => exact .ctxtHandler h
  | ctxtFrame h => exact .ctxtFrame h
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | ifTrue hc => exact .ifTrue hc
  | ifFalse hc => subst hc; exact .ifFalse
  | labelVals hb => subst hb; exact .labelVals
  | brLabelZero hb hl hn => subst hb; exact .brLabelZero hl hn
  | brLabelSucc hb hl => subst hb; exact .brLabelSucc hl
  | brHandler hb => subst hb; exact .brHandler
  | brIfTrue hc => exact .brIfTrue hc
  | brIfFalse hc => subst hc; exact .brIfFalse
  | brTableLt hi => exact .brTableLt hi
  | brTableGe hi => exact .brTableGe hi
  | brOnNullNull => exact .brOnNullNull
  | brOnNullAddr hv => exact .brOnNullAddr hv
  | brOnNonNullNull => exact .brOnNonNullNull
  | brOnNonNullAddr hv => exact .brOnNonNullAddr hv
  | brOnCastSucceed h => exact .brOnCastSucceed h
  | brOnCastFail h => exact .brOnCastFail h
  | brOnCastFailSucceed h => exact .brOnCastFailSucceed h
  | brOnCastFailFail h => exact .brOnCastFailFail h
  | call hx hf => exact .call hx hf
  | callRefNull hc => exact .callRefNull hc
  | callRefFunc ha hc hf he hn hcode =>
    subst ha
    rw [vals_append, List.append_assoc]
    exact .callRefFunc hc hf he hn hcode
  | returnCall hx hf => exact .returnCall hx hf
  | returnCallRefLabel hb hc => subst hb; exact .returnCallRefLabel hc
  | returnCallRefHandler hb hc => subst hb; exact .returnCallRefHandler hc
  | returnCallRefFrameNull hb hc => subst hb; exact .returnCallRefFrameNull hc
  | returnCallRefFrameAddr hb hc hf he hn => subst hb; exact .returnCallRefFrameAddr hc hf he hn
  | callIndirect => exact .callIndirect
  | returnCallIndirect => exact .returnCallIndirect
  | frameVals hb hn => subst hb; exact .frameVals hn
  | returnFrame hb hn => subst hb; exact .returnFrame hn
  | returnLabel hb => subst hb; exact .returnLabel
  | returnHandler hb => subst hb; exact .returnHandler
  | throw ht he hn => exact .throw ht he hn
  | throwRefNull => exact .throwRefNull
  | throwRefLabel => exact .throwRefLabel
  | throwRefFrame => exact .throwRefFrame
  | throwRefHandlerEmpty => exact .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact .throwRefHandlerCatch he ht
  | throwRefHandlerCatchRef he ht => exact .throwRefHandlerCatchRef he ht
  | throwRefHandlerCatchAll => exact .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact .throwRefHandlerNext h
  | tryTable hbt hm => exact .tryTable hbt hm
  | handlerVals hb => subst hb; exact .handlerVals
  | trapLabel => exact .trapLabel
  | trapHandler => exact .trapHandler
  | trapFrame => exact .trapFrame

theorem _root_.Silmaril.Wasm.SingleThreaded.Det.HeadDec.toStep {P : Profile} {s : Store H}
    {f : Frame} {code : List Admin} {c : Config H} (h : HeadDec P s f code c) :
    Step P noHost ⟨s, f, code⟩ c := by
  obtain ⟨vs, args, e, rest, c₀, rfl, hh, rfl⟩ := h
  have := lift_instrs vs rest ⟨s, f, vals args ++ [e]⟩ c₀ hh.toStep
  simpa using this

theorem _root_.Silmaril.Wasm.SingleThreaded.Det.Bubble.toStep {P : Profile} {s : Store H}
    {f : Frame} {code : List Admin} {c : Config H} (h : Bubble s f code c) :
    Step P noHost ⟨s, f, code⟩ c := by
  obtain ⟨p, q, X, u, r, rfl, hX, hqu, rfl⟩ := h
  have hin : Step P noHost ⟨s, f, vals q ++ X ++ u⟩ ⟨s, f, X⟩ := by
    rcases hX with rfl | ⟨a, rfl⟩
    · exact .trapInstrs hqu
    · exact .throwRefInstrs hqu
  have := lift_instrs p r _ _ hin
  simpa using this

/-! ## The driver -/

namespace Drv

/-- Is this the administrative `TRAP`? -/
def isTrap : Admin → Bool
  | .trap => true
  | _ => false

/-- A `THROW_REF` whose operand is an exception address. -/
def throwAddr? (vs : List Val) : Admin → Option Nat
  | .plain .throwRef =>
    match vs.getLast? with
    | some (.ref (.exn a)) => some a
    | _ => none
  | _ => none

theorem sizeOf_label_body {n : Nat} {cont : List Instr} {is : List Admin} :
    sizeOf is < sizeOf (Admin.label n cont is) := by simp

theorem sizeOf_handler_body {n : Nat} {cs : List Catch} {is : List Admin} :
    sizeOf is < sizeOf (Admin.handler n cs is) := by simp

theorem sizeOf_frame_body {n : Nat} {fi : Frame} {is : List Admin} :
    sizeOf is < sizeOf (Admin.frame n fi is) := by simp

/-- One layer of the driver, given a recursor for smaller codes. -/
def layer (head : Store H → Frame → List Val → Admin → Option (Nat × Config H))
    (s : Store H) (f : Frame) (vs : List Val) (e : Admin) (rest : List Admin)
    (rec : (c' : Config H) → sizeOf c'.code < sizeOf e → Option (Config H)) :
    Option (Config H) :=
  match isTrap e with
  | true => if vs.isEmpty && rest.isEmpty then none else some ⟨s, f, [.trap]⟩
  | false =>
  match throwAddr? vs e with
  | some a => if vs.dropLast.isEmpty && rest.isEmpty then none else some ⟨s, f, throwing a⟩
  | none =>
  match head s f vs e with
  | some (k, c₀) => some ⟨c₀.store, c₀.frame, vals (vs.take (vs.length - k)) ++ c₀.code ++ rest⟩
  | none =>
  match he : e with
  | .label n cont is =>
    (rec ⟨s, f, is⟩ (by exact sizeOf_label_body)).map fun c' =>
      ⟨c'.store, c'.frame, vals vs ++ [.label n cont c'.code] ++ rest⟩
  | .handler n cs is =>
    (rec ⟨s, f, is⟩ (by exact sizeOf_handler_body)).map fun c' =>
      ⟨c'.store, c'.frame, vals vs ++ [.handler n cs c'.code] ++ rest⟩
  | .frame n fi is =>
    (rec ⟨s, fi, is⟩ (by exact sizeOf_frame_body)).map fun c' =>
      ⟨c'.store, f, vals vs ++ [.frame n c'.frame c'.code] ++ rest⟩
  | _ => none

theorem sizeOf_lt_of_split {code : List Admin} {vs : List Val} {e : Admin} {rest : List Admin}
    (hs : splitVals code = (vs, e :: rest)) : sizeOf e < sizeOf code := by
  have h := splitVals_snd_sizeOf code
  rw [hs] at h
  simp only [List.cons.sizeOf_spec] at h
  omega

end Drv

/-- One step of the driver. -/
def step? (head : Store H → Frame → List Val → Admin → Option (Nat × Config H))
    (c : Config H) : Option (Config H) :=
  match _hs : splitVals c.code with
  | (_, []) => none
  | (vs, e :: rest) =>
    Drv.layer head c.store c.frame vs e rest fun c' _ => step? head c'
termination_by sizeOf c.code
decreasing_by exact lt_trans ‹_› (Drv.sizeOf_lt_of_split _hs)

theorem step?_nil {head : Store H → Frame → List Val → Admin → Option (Nat × Config H)}
    {c : Config H} {vs : List Val} (hs : splitVals c.code = (vs, [])) : step? head c = none := by
  rw [step?]
  split
  · rfl
  · rename_i hs'; rw [hs] at hs'; cases hs'

theorem step?_cons {head : Store H → Frame → List Val → Admin → Option (Nat × Config H)}
    {c : Config H} {vs : List Val} {e : Admin} {rest : List Admin}
    (hs : splitVals c.code = (vs, e :: rest)) :
    step? head c = Drv.layer head c.store c.frame vs e rest fun c' _ => step? head c' := by
  rw [step?]
  split
  · rename_i hs'; rw [hs] at hs'; cases hs'
  · rename_i hs'; rw [hs] at hs'; cases hs'; rfl

/-! ## Deep invariants -/

mutual
/-- `Inv` holds at every administrative instruction, recursively into label and
handler bodies (same frame) and frame bodies (inner frame). -/
def DeepAll (Inv : Frame → Admin → Prop) : Frame → List Admin → Prop
  | _, [] => True
  | f, e :: es => Drv.DeepAt Inv f e ∧ DeepAll Inv f es

def Drv.DeepAt (Inv : Frame → Admin → Prop) : Frame → Admin → Prop
  | f, .label n cont is => Inv f (.label n cont is) ∧ DeepAll Inv f is
  | f, .handler n cs is => Inv f (.handler n cs is) ∧ DeepAll Inv f is
  | f, .frame n fi is => Inv f (.frame n fi is) ∧ DeepAll Inv fi is
  | f, .plain i => Inv f (.plain i)
  | f, .ref r => Inv f (.ref r)
  | f, .trap => Inv f .trap
  | f, .callRefType d => Inv f (.callRefType d)
  | f, .returnCallRefType d => Inv f (.returnCallRefType d)
end

namespace Drv

theorem DeepAt.inv {Inv : Frame → Admin → Prop} {f : Frame} {e : Admin} (h : DeepAt Inv f e) :
    Inv f e := by
  cases e <;> simp only [DeepAt] at h <;> first | exact h | exact h.1

theorem deepAll_append {Inv : Frame → Admin → Prop} {f : Frame} {l₁ l₂ : List Admin} :
    DeepAll Inv f (l₁ ++ l₂) ↔ DeepAll Inv f l₁ ∧ DeepAll Inv f l₂ := by
  induction l₁ with
  | nil => simp [DeepAll]
  | cons a l ih => simp only [List.cons_append, DeepAll, ih, and_assoc]

theorem deepAll_split {Inv : Frame → Admin → Prop} {f : Frame} {vs : List Val} {e : Admin}
    {rest : List Admin} (h : DeepAll Inv f (vals vs ++ e :: rest)) : DeepAt Inv f e :=
  ((deepAll_append.mp h).2).1

end Drv

/-! ## Soundness -/

section
variable {o : GrowOracle} {s : Store H}
  {head : Store H → Frame → List Val → Admin → Option (Nat × Config H)}
  {Inv : Frame → Admin → Prop}

theorem step?_sound_aux
    (hhead : ∀ f vs e k c, Inv f e → head s f vs e = some (k, c) →
      k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c) :
    ∀ (n : Nat) (c c' : Config H), sizeOf c.code = n → c.store = s → DeepAll Inv c.frame c.code →
      step? head c = some c' → Step (profile o) noHost c c' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro ⟨s₀, f, code⟩ c' hn hst hinv hstep
  simp only at hst hinv hn
  subst hst
  rcases hs : splitVals code with ⟨vs, _ | ⟨e, rest⟩⟩
  · rw [step?_nil (c := ⟨s₀, f, code⟩) hs] at hstep; cases hstep
  obtain ⟨hcode, hev⟩ := splitVals_eq hs
  have hlt : sizeOf e < sizeOf code := Drv.sizeOf_lt_of_split hs
  rw [step?_cons (c := ⟨s₀, f, code⟩) hs] at hstep
  subst hcode
  have hat := Drv.deepAll_split hinv
  simp only [Drv.layer] at hstep
  split at hstep
  · -- trap
    rename_i ht
    have he : e = .trap := by cases e <;> simp_all [Drv.isTrap]
    subst he
    split at hstep
    · cases hstep
    · cases hstep
      rename_i hne
      have hne' : vs ≠ [] ∨ rest ≠ [] := by
        simp only [Bool.and_eq_true, List.isEmpty_iff, not_and_or] at hne; exact hne
      have := Step.trapInstrs (P := profile o) (host := noHost) (s := s₀) (f := f) hne'
      simpa using this
  split at hstep
  · -- throw_ref
    rename_i a ha
    have : e = .plain .throwRef ∧ vs.getLast? = some (.ref (.exn a)) := by
      unfold Drv.throwAddr? at ha
      split at ha
      · split at ha
        · rename_i hl; cases ha; exact ⟨rfl, hl⟩
        · cases ha
      · cases ha
    obtain ⟨rfl, hl⟩ := this
    split at hstep
    · cases hstep
    · cases hstep
      rename_i hne
      rw [List.getLast?_eq_some_iff] at hl
      obtain ⟨ys, rfl⟩ := hl
      have hne' : ys ≠ [] ∨ rest ≠ [] := by
        simp only [List.dropLast_concat, Bool.and_eq_true, List.isEmpty_iff, not_and_or] at hne
        exact hne
      have := Step.throwRefInstrs (P := profile o) (host := noHost) (s := s₀) (f := f) (a := a) hne'
      rw [List.append_assoc] at this
      rw [vals_append, List.append_assoc]
      exact this
  split at hstep
  · -- head
    rename_i k c₀ hh
    cases hstep
    obtain ⟨hk, hH⟩ := hhead f vs e k c₀ hat.inv hh
    have := lift_instrs (vs.take (vs.length - k)) rest ⟨s₀, f, _⟩ c₀ hH.toStep
    have hsplit : vals vs ++ e :: rest =
        vals (vs.take (vs.length - k)) ++ (vals (vs.drop (vs.length - k)) ++ [e]) ++ rest := by
      rw [← List.append_assoc, ← vals_append, List.take_append_drop]; simp
    rw [hsplit]
    exact this
  · -- contexts
    split at hstep
    · rename_i n cont is _ _ _ _
      obtain ⟨c₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp hstep
      have hat' : DeepAll Inv f is := hat.2
      have hin := ih (sizeOf is)
        (by rw [← hn]; have := Drv.sizeOf_label_body (n := n) (cont := cont) (is := is); omega)
        ⟨s₀, f, is⟩ c₁ rfl rfl hat' h₁
      have := lift_instrs vs rest _ _ (lift_label n cont _ _ hin)
      simpa using this
    · rename_i n cs is _ _ _ _
      obtain ⟨c₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp hstep
      have hat' : DeepAll Inv f is := hat.2
      have hin := ih (sizeOf is)
        (by rw [← hn]; have := Drv.sizeOf_handler_body (n := n) (cs := cs) (is := is); omega)
        ⟨s₀, f, is⟩ c₁ rfl rfl hat' h₁
      have := lift_instrs vs rest _ _ (lift_handler n cs _ _ hin)
      simpa using this
    · rename_i n fi is _ _ _ _
      obtain ⟨c₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp hstep
      have hat' : DeepAll Inv fi is := hat.2
      have hin := ih (sizeOf is)
        (by rw [← hn]; have := Drv.sizeOf_frame_body (n := n) (fi := fi) (is := is); omega)
        ⟨s₀, fi, is⟩ c₁ rfl rfl hat' h₁
      have := lift_instrs vs rest ⟨s₀, f, _⟩ ⟨c₁.store, f, _⟩ (lift_frame n f _ _ hin)
      simpa using this
    · cases hstep

/-- **Soundness** of the driver. -/
theorem step?_sound
    (hhead : ∀ f vs e k c, Inv f e → head s f vs e = some (k, c) →
      k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c)
    {c c' : Config H} :
    c.store = s → DeepAll Inv c.frame c.code → step? head c = some c' →
      Step (profile o) noHost c c' :=
  step?_sound_aux hhead _ c c' rfl

/-! ## Completeness -/

/-- The head step is a context step into a label, handler or frame body. -/
def IsCtxtHead (P : Profile) (s : Store H) (f : Frame) (e : Admin) (c : Config H) : Prop :=
  (∃ n cont is s' f' is', e = .label n cont is ∧ c = ⟨s', f', [.label n cont is']⟩ ∧
      Step P noHost ⟨s, f, is⟩ ⟨s', f', is'⟩) ∨
  (∃ n cs is s' f' is', e = .handler n cs is ∧ c = ⟨s', f', [.handler n cs is']⟩ ∧
      Step P noHost ⟨s, f, is⟩ ⟨s', f', is'⟩) ∨
  (∃ n fi is s' fi' is', e = .frame n fi is ∧ c = ⟨s', f, [.frame n fi' is']⟩ ∧
      Step P noHost ⟨s, fi, is⟩ ⟨s', fi', is'⟩)

theorem step?_complete_aux
    (hcomp : ∀ f vs args e c, Inv f e → Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
      head s f vs e = none → IsCtxtHead (profile o) s f e c) :
    ∀ (n : Nat) (c c' : Config H), sizeOf c.code = n → c.store = s → DeepAll Inv c.frame c.code →
      Step (profile o) noHost c c' → (step? head c).isSome := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro ⟨s₀, f, code⟩ c' hn hst hinv hstep
  simp only at hst hinv hn
  subst hst
  rcases Step.decomp hstep with hd | hb
  · obtain ⟨vs₀, args, e, rest, c₀, hcode, hH, -⟩ := hd
    simp only at hcode hH
    have hg := hH.good
    have hs : splitVals code = (vs₀ ++ args, e :: rest) := by
      rw [hcode, ← List.append_assoc, ← vals_append]; exact splitVals_vals_cons hg.val_none rest
    have hlt : sizeOf e < sizeOf code := Drv.sizeOf_lt_of_split hs
    rw [step?_cons (c := ⟨s₀, f, code⟩) hs]
    have hat : Drv.DeepAt Inv f e := by
      rw [hcode, ← List.append_assoc, ← vals_append] at hinv; exact Drv.deepAll_split hinv
    simp only [Drv.layer]
    have htrap : Drv.isTrap e = false := by
      cases e <;> simp [Drv.isTrap]; exact hg.ne_trap rfl
    have hthrow : Drv.throwAddr? (vs₀ ++ args) e = none := by
      unfold Drv.throwAddr?
      split
      · rw [hg.throwRef rfl]; simp
      · rfl
    rw [htrap]
    simp only [hthrow]
    split
    · rfl
    · rename_i hnone
      rcases hcomp f (vs₀ ++ args) args e c₀ hat.inv hH ⟨vs₀, rfl⟩ hnone with
        ⟨n', cont, is, s', f', is', rfl, -, hin⟩ | ⟨n', cs, is, s', f', is', rfl, -, hin⟩ |
        ⟨n', fi, is, s', fi', is', rfl, -, hin⟩
      · have := ih (sizeOf is) (by rw [← hn]; have := Drv.sizeOf_label_body (n := n') (cont := cont) (is := is); omega)
          ⟨s₀, f, is⟩ _ rfl rfl hat.2 hin
        simp only [Option.isSome_map]; exact this
      · have := ih (sizeOf is) (by rw [← hn]; have := Drv.sizeOf_handler_body (n := n') (cs := cs) (is := is); omega)
          ⟨s₀, f, is⟩ _ rfl rfl hat.2 hin
        simp only [Option.isSome_map]; exact this
      · have := ih (sizeOf is) (by rw [← hn]; have := Drv.sizeOf_frame_body (n := n') (fi := fi) (is := is); omega)
          ⟨s₀, fi, is⟩ _ rfl rfl hat.2 hin
        simp only [Option.isSome_map]; exact this
  · obtain ⟨p, q, u, r, hqu, ⟨-, hcode, -⟩ | ⟨a, -, hcode, -⟩⟩ := fnv_bubble hb <;>
      simp only at hcode
    · have hs : splitVals code = (p ++ q, .trap :: (u ++ r)) := by
        rw [hcode]; exact splitVals_vals_cons rfl _
      rw [step?_cons (c := ⟨s₀, f, code⟩) hs]
      simp only [Drv.layer, Drv.isTrap]
      split
      · rename_i hemp
        simp only [Bool.and_eq_true, List.isEmpty_iff, List.append_eq_nil_iff] at hemp
        rcases hqu with h | h <;> simp_all
      · rfl
    · have hs : splitVals code = (p ++ q ++ [.ref (.exn a)], .plain .throwRef :: (u ++ r)) := by
        rw [hcode]; exact splitVals_vals_cons rfl _
      rw [step?_cons (c := ⟨s₀, f, code⟩) hs]
      simp only [Drv.layer, Drv.isTrap, Drv.throwAddr?, List.getLast?_append, List.getLast?_singleton,
        Option.some_or, List.dropLast_concat]
      split
      · rename_i hemp
        simp only [Bool.and_eq_true, List.isEmpty_iff, List.append_eq_nil_iff] at hemp
        rcases hqu with h | h <;> simp_all
      · rfl

/-- **Completeness** of the driver: if the configuration steps, the driver
returns a successor. -/
theorem step?_complete
    (hcomp : ∀ f vs args e c, Inv f e → Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
      head s f vs e = none → IsCtxtHead (profile o) s f e c)
    {c c' : Config H} :
    c.store = s → DeepAll Inv c.frame c.code → Step (profile o) noHost c c' →
      (step? head c).isSome :=
  step?_complete_aux hcomp _ c c' rfl

end

end Silmaril.Wasm.SingleThreaded.Exec
