module

public import Silmaril.Wasm.Lime1.Execution.Callout
public import Silmaril.Wasm.Lime1.Execution.Instantiation

/-!
# Callout decomposition: properties

Generic facts about `Runtime.EvalCtx` and `Runtime.decomposeFrom?` (for any value coding), and
the Lime1 theorems relating the open machine to `Lime1.Execution.Step`.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Runtime

namespace ValueCoding

variable {I : Type*} (C : ValueCoding I)

theorem decode_eq_none {x : AdminInstr I} (h : ∀ i, x ≠ .source i) : C.decode x = none := by
  cases hx : C.decode x with
  | none => rfl
  | some v =>
    obtain ⟨i, rfl⟩ := C.source_of_decode hx
    exact absurd rfl (h i)

@[simp] theorem decode_invoke (a : FuncAddr) : C.decode (.invoke a) = none :=
  C.decode_eq_none (by simp)

@[simp] theorem decode_label (n : Nat) (cont : List I) (body : List (AdminInstr I)) :
    C.decode (.label n cont body) = none := C.decode_eq_none (by simp)

@[simp] theorem decode_frame (n : Nat) (fr : Frame) (body : List (AdminInstr I)) :
    C.decode (.frame n fr body) = none := C.decode_eq_none (by simp)

@[simp] theorem decode_trap : C.decode (.trap : AdminInstr I) = none :=
  C.decode_eq_none (by simp)

end ValueCoding

namespace EvalCtx

variable {I : Type*}

theorem plug_comp (e : Value → AdminInstr I) (outer inner : EvalCtx I)
    (code : List (AdminInstr I)) :
    (outer.comp inner).plug e code = outer.plug e (inner.plug e code) := by
  induction outer with
  | hole => rfl
  | seq vs outer tail ih => simp only [comp, plug, ih]
  | label n cont outer ih => simp only [comp, plug, ih]
  | frame n fr outer ih => simp only [comp, plug, ih]

end EvalCtx

section Decompose

variable {Code Host I : Type*} (C : ValueCoding I) (s : Store Code Host)

@[simp] theorem decomposeFrom?_nil (acc : List Value) :
    decomposeFrom? C s acc ([] : List (AdminInstr I)) = none := by
  simp only [decomposeFrom?]

theorem decomposeFrom?_cons_of_decode {acc : List Value} {x : AdminInstr I}
    (l : List (AdminInstr I)) (h : C.decode x = none) :
    decomposeFrom? C s acc (x :: l) = decomposeHead? C s acc l x := by
  simp only [decomposeFrom?, h]

@[simp] theorem decomposeFrom?_cons_encode (acc : List Value) (v : Value)
    (l : List (AdminInstr I)) :
    decomposeFrom? C s acc (C.encode v :: l) = decomposeFrom? C s (acc ++ [v]) l := by
  simp only [decomposeFrom?, C.decode_encode]

@[simp] theorem decomposeFrom?_encode_append (acc vs : List Value) (l : List (AdminInstr I)) :
    decomposeFrom? C s acc (vs.map C.encode ++ l) = decomposeFrom? C s (acc ++ vs) l := by
  induction vs generalizing acc with
  | nil => simp
  | cons v vs ih => simp [ih]

@[simp] theorem decomposeFrom?_map_encode (acc vs : List Value) :
    decomposeFrom? C s acc (vs.map C.encode) = none := by
  simpa using decomposeFrom?_encode_append C s acc vs []

@[simp] theorem decomposeHead?_source (acc : List Value) (tail : List (AdminInstr I)) (i : I) :
    decomposeHead? C s acc tail (.source i) = none := by
  simp only [decomposeHead?]

@[simp] theorem decomposeHead?_trap (acc : List Value) (tail : List (AdminInstr I)) :
    decomposeHead? C s acc tail .trap = none := by
  simp only [decomposeHead?]

@[simp] theorem decomposeHead?_label (acc : List Value) (tail : List (AdminInstr I)) (n : Nat)
    (cont : List I) (body : List (AdminInstr I)) :
    decomposeHead? C s acc tail (.label n cont body) =
      (decomposeFrom? C s [] body).map fun c =>
        { c with context := .seq acc (.label n cont c.context) tail } := by
  simp only [decomposeHead?]

@[simp] theorem decomposeHead?_frame (acc : List Value) (tail : List (AdminInstr I)) (n : Nat)
    (fr : Frame) (body : List (AdminInstr I)) :
    decomposeHead? C s acc tail (.frame n fr body) =
      (decomposeFrom? C s [] body).map fun c =>
        { c with context := .seq acc (.frame n fr c.context) tail } := by
  simp only [decomposeHead?]

/-- Whether the head is a callout does not depend on what follows it. -/
theorem decomposeHead?_eq_none_iff (acc : List Value) (tail tail' : List (AdminInstr I))
    (x : AdminInstr I) :
    decomposeHead? C s acc tail x = none ↔ decomposeHead? C s acc tail' x = none := by
  cases x with
  | invoke a =>
    simp only [decomposeHead?]
    split <;> [split <;> simp; simp]
  | label n cont body => simp
  | frame n fr body => simp
  | source i => simp
  | trap => simp

/-- Appending code after a non-value instruction does not create a callout. -/
theorem decomposeFrom?_append_eq_none {acc : List Value} {code : List (AdminInstr I)}
    (tail : List (AdminInstr I)) (nonvalue : ∃ x ∈ code, C.decode x = none)
    (h : decomposeFrom? C s acc code = none) :
    decomposeFrom? C s acc (code ++ tail) = none := by
  induction code generalizing acc with
  | nil => simp at nonvalue
  | cons x xs ih =>
    cases hx : C.decode x with
    | some v =>
      have hv : C.encode v = x := C.encode_of_decode hx
      subst hv
      simp only [decomposeFrom?_cons_encode, List.cons_append] at h ⊢
      apply ih _ h
      obtain ⟨y, hy, hyd⟩ := nonvalue
      rcases List.mem_cons.mp hy with rfl | hy
      · simp [C.decode_encode] at hyd
      · exact ⟨y, hy, hyd⟩
    | none =>
      rw [decomposeFrom?_cons_of_decode C s _ hx] at h
      rw [List.cons_append, decomposeFrom?_cons_of_decode C s _ hx]
      exact (decomposeHead?_eq_none_iff C s acc _ _ x).mp h

mutual
/-- Soundness of the decomposer: a returned callout is located at the scanned code. -/
theorem decomposeFrom?_sound : ∀ (acc : List Value) (code : List (AdminInstr I))
    (c : Callout Host I), decomposeFrom? C s acc code = some c →
    c.Located C s (acc.map C.encode ++ code)
  | _, [], _, h => by simp at h
  | acc, x :: tail, c, h => by
    cases hx : C.decode x with
    | some v =>
      have hv : C.encode v = x := C.encode_of_decode hx
      subst hv
      simp only [decomposeFrom?_cons_encode] at h
      have := decomposeFrom?_sound (acc ++ [v]) tail c h
      simpa using this
    | none =>
      rw [decomposeFrom?_cons_of_decode C s _ hx] at h
      exact decomposeHead?_sound acc tail x c h
termination_by structural _ code => code

theorem decomposeHead?_sound : ∀ (acc : List Value) (tail : List (AdminInstr I))
    (x : AdminInstr I) (c : Callout Host I), decomposeHead? C s acc tail x = some c →
    c.Located C s (acc.map C.encode ++ x :: tail)
  | acc, tail, .invoke a, c, h => by
    simp only [decomposeHead?] at h
    split at h
    · next ft hh found =>
      split at h
      · next le =>
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨?_, found, ?_⟩
        · simp only [Callout.fill, Callout.redex, EvalCtx.plug]
          simp only [List.map_take, List.map_drop]
          rw [← List.append_assoc, List.take_append_drop]
          simp
        · simp only [List.length_drop]
          omega
      · contradiction
    · contradiction
  | acc, tail, .label n cont body, c, h => by
    simp only [decomposeHead?_label, Option.map_eq_some_iff] at h
    obtain ⟨c', hc', rfl⟩ := h
    have ih := decomposeFrom?_sound [] body c' hc'
    obtain ⟨plugged, found, arity⟩ := ih
    refine ⟨?_, found, arity⟩
    simp only [List.map_nil, List.nil_append] at plugged
    rw [plugged]
    simp [Callout.fill, Callout.redex, EvalCtx.plug]
  | acc, tail, .frame n fr body, c, h => by
    simp only [decomposeHead?_frame, Option.map_eq_some_iff] at h
    obtain ⟨c', hc', rfl⟩ := h
    have ih := decomposeFrom?_sound [] body c' hc'
    obtain ⟨plugged, found, arity⟩ := ih
    refine ⟨?_, found, arity⟩
    simp only [List.map_nil, List.nil_append] at plugged
    rw [plugged]
    simp [Callout.fill, Callout.redex, EvalCtx.plug]
  | _, _, .source _, _, h => by simp at h
  | _, _, .trap, _, h => by simp at h
termination_by structural _ _ x => x
end

/-- Completeness of the decomposer, relative to any context: a host redex plugged into a
context (after an already scanned prefix `acc` and before `tail`) is found, with the same
function, host code, type and arguments, and a context that plugs every code identically. -/
theorem decomposeFrom?_plug {a : FuncAddr} {ft : V1.FuncType} {h : Host} {args : List Value}
    (found : s.funcs[a.value]? = some (.host ft h)) (arity : args.length = ft.params.length)
    (K : EvalCtx I) (acc : List Value) (tail : List (AdminInstr I)) :
    ∃ c, decomposeFrom? C s acc (K.plug C.encode (args.map C.encode ++ [.invoke a]) ++ tail) =
        some c ∧ c.function = a ∧ c.type = ft ∧ c.host = h ∧ c.args = args ∧
        ∀ code, c.fill C code = acc.map C.encode ++ K.plug C.encode code ++ tail := by
  induction K generalizing acc tail with
  | hole =>
    have hlen : (acc ++ args).length - ft.params.length = acc.length := by simp; omega
    have hle : ft.params.length ≤ (acc ++ args).length := by simp; omega
    refine ⟨⟨.seq ((acc ++ args).take ((acc ++ args).length - ft.params.length)) .hole tail, a,
      ft, h, (acc ++ args).drop ((acc ++ args).length - ft.params.length)⟩, ?_, rfl, rfl, rfl,
      ?_, ?_⟩
    · simp only [EvalCtx.plug, List.append_assoc, List.singleton_append,
        decomposeFrom?_encode_append]
      rw [decomposeFrom?_cons_of_decode C s _ (C.decode_invoke a)]
      simp only [decomposeHead?, found, hle, ite_true]
    · show List.drop _ _ = _
      rw [hlen, List.drop_left]
    · intro code
      simp only [Callout.fill, EvalCtx.plug]
      rw [hlen, List.take_left]
  | seq vs K t ih =>
    obtain ⟨c, hc, hf, ht, hh, ha, hfill⟩ := ih (acc ++ vs) (t ++ tail)
    refine ⟨c, ?_, hf, ht, hh, ha, ?_⟩
    · simpa [EvalCtx.plug, List.append_assoc] using hc
    · intro code
      simp [hfill, EvalCtx.plug, List.append_assoc]
  | label n cont K ih =>
    obtain ⟨c, hc, hf, ht, hh, ha, hfill⟩ := ih [] []
    simp only [List.append_nil] at hc
    refine ⟨{ c with context := .seq acc (.label n cont c.context) tail }, ?_, hf, ht, hh, ha, ?_⟩
    · simp only [EvalCtx.plug, List.singleton_append]
      rw [decomposeFrom?_cons_of_decode C s _ (C.decode_label n cont _), decomposeHead?_label, hc]
      rfl
    · intro code
      have := hfill code
      simp only [Callout.fill, List.map_nil, List.nil_append, List.append_nil] at this
      simp [Callout.fill, EvalCtx.plug, this]
  | frame n fr K ih =>
    obtain ⟨c, hc, hf, ht, hh, ha, hfill⟩ := ih [] []
    simp only [List.append_nil] at hc
    refine ⟨{ c with context := .seq acc (.frame n fr c.context) tail }, ?_, hf, ht, hh, ha, ?_⟩
    · simp only [EvalCtx.plug, List.singleton_append]
      rw [decomposeFrom?_cons_of_decode C s _ (C.decode_frame n fr _), decomposeHead?_frame, hc]
      rfl
    · intro code
      have := hfill code
      simp only [Callout.fill, List.map_nil, List.nil_append, List.append_nil] at this
      simp [Callout.fill, EvalCtx.plug, this]

/-- The decomposer finds every located callout, up to the (unobservable) shape of its
context. -/
theorem decomposeFrom?_complete {code : List (AdminInstr I)} {c : Callout Host I}
    (h : c.Located C s code) :
    ∃ c', decomposeFrom? C s [] code = some c' ∧ c'.function = c.function ∧ c'.type = c.type ∧
      c'.host = c.host ∧ c'.args = c.args ∧ ∀ code', c'.fill C code' = c.fill C code' := by
  obtain ⟨c', hc, hf, ht, hh, ha, hfill⟩ :=
    decomposeFrom?_plug C s h.found h.arity c.context [] []
  refine ⟨c', ?_, hf, ht, hh, ha, fun code' => by simpa [Callout.fill] using hfill code'⟩
  simpa [h.plugged, Callout.fill, Callout.redex] using hc

/-- Located callouts are unique up to the plugged code. -/
theorem Callout.Located.unique {code : List (AdminInstr I)} {c d : Callout Host I}
    (hc : c.Located C s code) (hd : d.Located C s code) :
    c.function = d.function ∧ c.type = d.type ∧ c.host = d.host ∧ c.args = d.args ∧
      ∀ code', c.fill C code' = d.fill C code' := by
  obtain ⟨c', hc', hcf, hct, hch, hca, hcfill⟩ := decomposeFrom?_complete C s hc
  obtain ⟨d', hd', hdf, hdt, hdh, hda, hdfill⟩ := decomposeFrom?_complete C s hd
  rw [hc'] at hd'
  cases hd'
  exact ⟨hcf ▸ hdf, hct ▸ hdt, hch ▸ hdh, hca ▸ hda, fun code' => (hcfill code').symm.trans
    (hdfill code')⟩

end Decompose

end Silmaril.Wasm.Execution.Runtime

namespace Silmaril.Wasm.Lime1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

/-! ## Lime1 decomposition lemmas -/

@[simp] theorem asValue?_value (v : Value) : asValue? (value v) = some v := coding.decode_encode v

@[simp] theorem coding_encode : coding.encode = value := rfl

@[simp] theorem coding_decode : coding.decode = asValue? := rfl

section Decompose

variable {H : Type*} (s : Store H)

@[simp] theorem decomposeFrom?_values_append (acc vs : List Value) (l : List Admin) :
    decomposeFrom? coding s acc (values vs ++ l) = decomposeFrom? coding s (acc ++ vs) l :=
  decomposeFrom?_encode_append coding s acc vs l

@[simp] theorem decomposeFrom?_values (acc vs : List Value) :
    decomposeFrom? coding s acc (values vs) = none :=
  decomposeFrom?_map_encode coding s acc vs

@[simp] theorem decomposeFrom?_value_cons (acc : List Value) (v : Value) (l : List Admin) :
    decomposeFrom? coding s acc (value v :: l) = decomposeFrom? coding s (acc ++ [v]) l :=
  decomposeFrom?_cons_encode coding s acc v l

@[simp] theorem decomposeFrom?_source_cons (acc : List Value) (i : Instr) (l : List Admin) :
    decomposeFrom? coding s acc (.source i :: l) =
      (asValue? (.source i)).bind fun v => decomposeFrom? coding s (acc ++ [v]) l := by
  cases h : asValue? (.source i) with
  | none => rw [decomposeFrom?_cons_of_decode coding s l h, decomposeHead?_source]; rfl
  | some v =>
    have hv : value v = .source i := coding.encode_of_decode h
    rw [← hv, decomposeFrom?_value_cons]
    rfl

@[simp] theorem decomposeFrom?_trap_cons (acc : List Value) (l : List Admin) :
    decomposeFrom? coding s acc (.trap :: l) = none := by
  rw [decomposeFrom?_cons_of_decode coding s l (coding.decode_trap), decomposeHead?_trap]

@[simp] theorem decomposeFrom?_label_cons (acc : List Value) (n : Nat) (cont : Expr)
    (body l : List Admin) :
    decomposeFrom? coding s acc (.label n cont body :: l) =
      (decomposeFrom? coding s [] body).map fun c =>
        { c with context := .seq acc (.label n cont c.context) l } := by
  rw [decomposeFrom?_cons_of_decode coding s l (coding.decode_label _ _ _), decomposeHead?_label]

@[simp] theorem decomposeFrom?_frame_cons (acc : List Value) (n : Nat) (fr : Frame)
    (body l : List Admin) :
    decomposeFrom? coding s acc (.frame n fr body :: l) =
      (decomposeFrom? coding s [] body).map fun c =>
        { c with context := .seq acc (.frame n fr c.context) l } := by
  rw [decomposeFrom?_cons_of_decode coding s l (coding.decode_frame _ _ _), decomposeHead?_frame]

theorem decomposeFrom?_invoke_cons (acc : List Value) (a : FuncAddr) (l : List Admin) :
    decomposeFrom? coding s acc (.invoke a :: l) = decomposeHead? coding s acc l (.invoke a) :=
  decomposeFrom?_cons_of_decode coding s l (coding.decode_invoke a)

end Decompose

/-! ## Plugging and the atomic host rule -/

/-- A step that is uniform in the frame lifts through any evaluation context. -/
theorem Step.plug {H : Type*} {host : HostSemantics H} {s s' : Store H} {x y : List Admin}
    (h : ∀ g, Step host ⟨s, g, x⟩ ⟨s', g, y⟩) (K : EvalCtx Instr) (f : Frame) :
    Step host ⟨s, f, K.plug value x⟩ ⟨s', f, K.plug value y⟩ := by
  induction K generalizing f with
  | hole => exact h f
  | seq vs K tail ih => exact .context (ih f) vs tail
  | label n cont K ih => exact .label (ih f) n cont
  | frame n fr K ih => exact .frame (ih fr) n f

/-- A step at the hole, taken in the frame in force there (`EvalCtx.activeFrame`) and leaving
that frame unchanged, lifts through the context. This is the sense in which `activeFrame` is the
caller frame of a callout (the frame whose module instance a canonical built-in would consult). -/
theorem Step.plug_activeFrame {H : Type*} {host : HostSemantics H} {s s' : Store H}
    {x y : List Admin} (K : EvalCtx Instr) (f : Frame)
    (h : Step host ⟨s, K.activeFrame f, x⟩ ⟨s', K.activeFrame f, y⟩) :
    Step host ⟨s, f, K.plug value x⟩ ⟨s', f, K.plug value y⟩ := by
  induction K generalizing f with
  | hole => exact h
  | seq vs K tail ih => exact .context (ih f h) vs tail
  | label n cont K ih => exact .label (ih f h) n cont
  | frame n fr K ih => exact .frame (ih fr h) n f

/-- Atomic host step = callout, then resume with the host's answer. -/
theorem Step.callout_returned {H : Type*} {host : HostSemantics H} {cfg : Config H}
    {c : Runtime.Callout H Instr} {s' : Store H} {r : Result} (hc : CalloutAt cfg c)
    (hr : host c.host cfg.store c.args (.returned s' r)) :
    Step host cfg (resume cfg c s' r) := by
  obtain ⟨s, f, code⟩ := cfg
  obtain ⟨plugged, found, arity⟩ := hc
  simp only at plugged found hr
  subst plugged
  exact Step.plug (fun g => .invokeHost s s' g c.function c.type c.host c.args r found arity hr)
    c.context f

/-- A diverging host answer is the machine's self-loop at the callout. -/
theorem Step.callout_diverged {H : Type*} {host : HostSemantics H} {cfg : Config H}
    {c : Runtime.Callout H Instr} (hc : CalloutAt cfg c)
    (hd : host c.host cfg.store c.args .diverged) : Step host cfg cfg := by
  obtain ⟨s, f, code⟩ := cfg
  obtain ⟨plugged, found, arity⟩ := hc
  simp only at plugged found hd
  subst plugged
  exact Step.plug (fun g => .invokeHostDiverges s g c.function c.type c.host c.args found arity hd)
    c.context f

theorem Answer.step {H : Type*} {host : HostSemantics H} {a b : Config H}
    {c : Runtime.Callout H Instr} (hc : CalloutAt a c) (h : Answer host a c b) : Step host a b := by
  cases h with
  | returned s' r hr => exact Step.callout_returned hc hr
  | diverged hd => exact Step.callout_diverged hc hd

theorem Answer.iff {H : Type*} {host : HostSemantics H} {a b : Config H}
    {c : Runtime.Callout H Instr} :
    Answer host a c b ↔ (∃ s' r, host c.host a.store c.args (.returned s' r) ∧
      b = resume a c s' r) ∨ (host c.host a.store c.args .diverged ∧ b = a) := by
  constructor
  · rintro (⟨s', r, hr⟩ | hd)
    · exact .inl ⟨s', r, hr, rfl⟩
    · exact .inr ⟨hd, rfl⟩
  · rintro (⟨s', r, hr, rfl⟩ | ⟨hd, rfl⟩)
    · exact .returned s' r hr
    · exact .diverged hd

/-- Host-free steps are steps under every host. -/
theorem Step.of_internal {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : Internal a b) : Step host a b := by
  induction h with
  | context _ vs tail ih => exact .context ih vs tail
  | label _ n cont ih => exact .label ih n cont
  | frame _ n outer ih => exact .frame ih n outer
  | invokeHost _ _ _ _ _ _ _ _ _ _ hb => exact hb.elim
  | invokeHostDiverges _ _ _ _ _ _ _ _ hb => exact hb.elim
  | _ =>
    first
    | (apply Step.pure <;> assumption)
    | (apply Step.localGet <;> assumption)
    | (apply Step.localSet <;> assumption)
    | (apply Step.globalGet <;> assumption)
    | (apply Step.globalSet <;> assumption)
    | (apply Step.call <;> assumption)
    | (apply Step.callIndirect <;> assumption)
    | (apply Step.callIndirectBounds <;> assumption)
    | (apply Step.callIndirectNull <;> assumption)
    | (apply Step.callIndirectType <;> assumption)
    | (apply Step.invokeWasm <;> assumption)
    | (apply Step.intLoad <;> assumption)
    | (apply Step.intLoadTrap <;> assumption)
    | (apply Step.floatLoad <;> assumption)
    | (apply Step.floatLoadTrap <;> assumption)
    | (apply Step.intStore <;> assumption)
    | (apply Step.intStoreTrap <;> assumption)
    | (apply Step.floatStore <;> assumption)
    | (apply Step.floatStoreTrap <;> assumption)
    | (apply Step.memorySize <;> assumption)
    | (apply Step.memoryGrow <;> assumption)
    | (apply Step.memoryCopy <;> assumption)
    | (apply Step.memoryCopyTrap <;> assumption)
    | (apply Step.memoryFill <;> assumption)
    | (apply Step.memoryFillTrap <;> assumption)

theorem Steps.of_internal {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : Relation.ReflTransGen Internal a b) : Steps host a b := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (Step.of_internal hs)

/-- Every machine step is a host-free step, or a callout completed by the host relation. -/
theorem Step.internal_or_callout {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : Step host a b) :
    Internal a b ∨ ∃ c, CalloutAt a c ∧ Answer host a c b := by
  induction h with
  | invokeHost s s' f a ft fn args r found arity behavior =>
    exact .inr ⟨⟨.hole, a, ft, fn, args⟩, ⟨rfl, found, arity⟩, .returned s' r behavior⟩
  | invokeHostDiverges s f a ft fn args found arity behavior =>
    exact .inr ⟨⟨.hole, a, ft, fn, args⟩, ⟨rfl, found, arity⟩, .diverged behavior⟩
  | context h vs tail ih =>
    rcases ih with ih | ⟨c, hc, hans⟩
    · exact .inl (.context ih vs tail)
    · refine .inr ⟨{ c with context := .seq vs c.context tail }, ⟨?_, hc.found, hc.arity⟩, ?_⟩
      · simp only [CalloutAt] at hc ⊢
        rw [hc.plugged]
        rfl
      · rcases Answer.iff.mp hans with ⟨s'', r, hr, heq⟩ | ⟨hd, heq⟩
        · simp only [resume, Config.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact .returned _ r hr
        · simp only [Config.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact .diverged hd
  | label h n cont ih =>
    rcases ih with ih | ⟨c, hc, hans⟩
    · exact .inl (.label ih n cont)
    · refine .inr ⟨{ c with context := .label n cont c.context }, ⟨?_, hc.found, hc.arity⟩, ?_⟩
      · simp only [CalloutAt] at hc ⊢
        rw [hc.plugged]
        rfl
      · rcases Answer.iff.mp hans with ⟨s'', r, hr, heq⟩ | ⟨hd, heq⟩
        · simp only [resume, Config.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact .returned _ r hr
        · simp only [Config.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact .diverged hd
  | frame h n outer ih =>
    rcases ih with ih | ⟨c, hc, hans⟩
    · exact .inl (.frame ih n outer)
    · rename_i inner _ _ _
      refine .inr ⟨{ c with context := .frame n inner c.context }, ⟨?_, hc.found, hc.arity⟩, ?_⟩
      · simp only [CalloutAt] at hc ⊢
        rw [hc.plugged]
        rfl
      · rcases Answer.iff.mp hans with ⟨s'', r, hr, heq⟩ | ⟨hd, heq⟩
        · simp only [resume, Config.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact .returned _ r hr
        · simp only [Config.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact .diverged hd
  | _ =>
    refine .inl ?_
    first
    | (apply Step.pure <;> assumption)
    | (apply Step.localGet <;> assumption)
    | (apply Step.localSet <;> assumption)
    | (apply Step.globalGet <;> assumption)
    | (apply Step.globalSet <;> assumption)
    | (apply Step.call <;> assumption)
    | (apply Step.callIndirect <;> assumption)
    | (apply Step.callIndirectBounds <;> assumption)
    | (apply Step.callIndirectNull <;> assumption)
    | (apply Step.callIndirectType <;> assumption)
    | (apply Step.invokeWasm <;> assumption)
    | (apply Step.intLoad <;> assumption)
    | (apply Step.intLoadTrap <;> assumption)
    | (apply Step.floatLoad <;> assumption)
    | (apply Step.floatLoadTrap <;> assumption)
    | (apply Step.intStore <;> assumption)
    | (apply Step.intStoreTrap <;> assumption)
    | (apply Step.floatStore <;> assumption)
    | (apply Step.floatStoreTrap <;> assumption)
    | (apply Step.memorySize <;> assumption)
    | (apply Step.memoryGrow <;> assumption)
    | (apply Step.memoryCopy <;> assumption)
    | (apply Step.memoryCopyTrap <;> assumption)
    | (apply Step.memoryFill <;> assumption)
    | (apply Step.memoryFillTrap <;> assumption)

/-- **Adequacy of the open machine.** A step of the atomic machine is exactly a host-free step,
or a callout followed by the host's answer (resumption, or the divergence self-loop). -/
theorem step_iff {H : Type*} {host : HostSemantics H} {a b : Config H} :
    Step host a b ↔ Internal a b ∨ ∃ c, CalloutAt a c ∧ Answer host a c b := by
  constructor
  · exact Step.internal_or_callout
  · rintro (h | ⟨c, hc, hans⟩)
    · exact Step.of_internal h
    · exact hans.step hc

/-! ## The executable decomposition, and parking -/

theorem decompose?_sound {H : Type*} {cfg : Config H} {c : Runtime.Callout H Instr}
    (h : decompose? cfg = some c) : CalloutAt cfg c := by
  have h' := decomposeFrom?_sound coding cfg.store [] cfg.code c h
  simp only [List.map_nil, List.nil_append] at h'
  exact h'

/-- `decompose?` finds every callout; the context it returns plugs every code identically, so
resumption does not depend on which decomposition is used. -/
theorem decompose?_complete {H : Type*} {cfg : Config H} {c : Runtime.Callout H Instr}
    (h : CalloutAt cfg c) :
    ∃ c', decompose? cfg = some c' ∧ c'.function = c.function ∧ c'.type = c.type ∧
      c'.host = c.host ∧ c'.args = c.args ∧ ∀ s' r, resume cfg c' s' r = resume cfg c s' r := by
  obtain ⟨c', hc, hf, ht, hh, ha, hfill⟩ := decomposeFrom?_complete coding cfg.store h
  exact ⟨c', hc, hf, ht, hh, ha, fun s' r => by simp only [resume, hfill]⟩

/-- Whether a configuration is parked at a callout is decided by `decompose?`. -/
theorem exists_callout_iff {H : Type*} {cfg : Config H} :
    (∃ c, CalloutAt cfg c) ↔ (decompose? cfg).isSome := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c', hc', -⟩ := decompose?_complete hc
    simp [hc']
  · intro h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
    exact ⟨c, decompose?_sound hc⟩

theorem CalloutAt.unique {H : Type*} {cfg : Config H} {c d : Runtime.Callout H Instr}
    (hc : CalloutAt cfg c) (hd : CalloutAt cfg d) :
    c.function = d.function ∧ c.type = d.type ∧ c.host = d.host ∧ c.args = d.args ∧
      ∀ s' r, resume cfg c s' r = resume cfg d s' r := by
  obtain ⟨hf, ht, hh, ha, hfill⟩ := Callout.Located.unique coding cfg.store hc hd
  exact ⟨hf, ht, hh, ha, fun s' r => by simp only [resume, hfill]⟩

/-- Code that takes a step contains a non-value instruction. -/
theorem Step.nonvalue {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : Step host a b) : ∃ x ∈ a.code, asValue? x = none := by
  induction h with
  | pure s f hp =>
    cases hp <;> first | (simp [values, asValue?]; done) | exact ⟨.trap, by simp, rfl⟩
  | context _ vs tail ih =>
    obtain ⟨x, hx, hv⟩ := ih
    exact ⟨x, by simp [hx], hv⟩
  | _ => simp [values, asValue?]

/-- Host-free steps never start at a callout: `decomposeFrom?` fails on their code, whatever
value prefix precedes it. -/
theorem Internal.decompose_none {H : Type*} {a b : Config H} (h : Internal a b) :
    ∀ acc, decomposeFrom? coding a.store acc a.code = none := by
  induction h with
  | pure s f hp =>
    intro acc
    cases hp <;> simp [asValue?]
  | context h vs tail ih =>
    intro acc
    obtain ⟨x, hx, hv⟩ := h.nonvalue
    simp only [List.append_assoc, decomposeFrom?_values_append]
    exact decomposeFrom?_append_eq_none coding _ tail ⟨x, hx, hv⟩ (ih _)
  | label h n cont ih =>
    intro acc
    simp [ih []]
  | frame h n outer ih =>
    intro acc
    simp [ih []]
  | invokeWasm s f a ft module fn args found arity =>
    intro acc
    simp [decomposeFrom?_invoke_cons, decomposeHead?, found]
  | invokeHost _ _ _ _ _ _ _ _ _ _ hb => exact hb.elim
  | invokeHostDiverges _ _ _ _ _ _ _ _ hb => exact hb.elim
  | _ => intro acc; simp [asValue?]

/-- A configuration parked at a callout has no host-free step. -/
theorem CalloutAt.not_internal {H : Type*} {a b : Config H} {c : Runtime.Callout H Instr}
    (hc : CalloutAt a c) (h : Internal a b) : False := by
  obtain ⟨c', hc', -⟩ := decompose?_complete hc
  simp [decompose?, h.decompose_none []] at hc'

/-- On a configuration that is not parked at a callout, the atomic machine under any host takes
exactly the host-free steps: the open machine agrees with `Step host` on non-host redexes. -/
theorem Step.internal_iff_of_not_callout {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : ∀ c, ¬ CalloutAt a c) : Step host a b ↔ Internal a b := by
  refine ⟨fun hs => ?_, Step.of_internal⟩
  rcases hs.internal_or_callout with hi | ⟨c, hc, -⟩
  · exact hi
  · exact (h c hc).elim

/-! ## The open machine -/

theorem openStep_internal_iff {H : Type*} {a b : Config H} :
    OpenStep a (.internal b) ↔ Internal a b :=
  ⟨fun | .internal h => h, .internal⟩

theorem openStep_callout_iff {H : Type*} {a : Config H} {c : Runtime.Callout H Instr} :
    OpenStep a (.callout c) ↔ CalloutAt a c :=
  ⟨fun | .callout h => h, .callout⟩

/-- The open machine stops at callouts: they have no internal successor. -/
theorem OpenStep.callout_stops {H : Type*} {a b : Config H} {c : Runtime.Callout H Instr}
    (hc : OpenStep a (.callout c)) (hb : OpenStep a (.internal b)) : False :=
  (openStep_callout_iff.mp hc).not_internal (openStep_internal_iff.mp hb)

/-- The atomic machine is the open machine with callouts answered by the host relation. -/
theorem step_iff_openStep {H : Type*} {host : HostSemantics H} {a b : Config H} :
    Step host a b ↔
      OpenStep a (.internal b) ∨ ∃ c, OpenStep a (.callout c) ∧ Answer host a c b := by
  simp only [openStep_internal_iff, openStep_callout_iff]
  exact step_iff

/-- The only host step out of a parked configuration is the answer to its callout. -/
theorem CalloutAt.step_iff {H : Type*} {host : HostSemantics H} {a b : Config H}
    {c : Runtime.Callout H Instr} (hc : CalloutAt a c) :
    Step host a b ↔ Answer host a c b := by
  constructor
  · intro h
    rcases h.internal_or_callout with h | ⟨d, hd, hans⟩
    · exact (hc.not_internal h).elim
    · obtain ⟨-, -, hh, ha, hres⟩ := hd.unique hc
      rcases Answer.iff.mp hans with ⟨s', r, hr, rfl⟩ | ⟨hdv, rfl⟩
      · rw [hres]
        exact .returned s' r (hh ▸ ha ▸ hr)
      · exact .diverged (hh ▸ ha ▸ hdv)
  · exact fun h => h.step hc

/-! ## Executable stepping: soundness -/

theorem numOf?_eq {t : NumType} {v : Value} {x : BitVec t.width} (h : numOf? t v = some x) :
    v = ⟨t, x⟩ := by
  rcases v with ⟨vt, b⟩
  rcases t with (t | t) <;> cases t <;> rcases vt with (vt | vt) <;> cases vt <;>
    simp only [numOf?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl

theorem splitValues_eq {l : List Admin} {vs : List Value} {rest : List Admin}
    (h : splitValues l = (vs, rest)) : l = values vs ++ rest := by
  induction l generalizing vs rest with
  | nil =>
    simp only [splitValues, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | cons x xs ih =>
    simp only [splitValues] at h
    split at h
    · next v hv =>
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hx : value v = x := coding.encode_of_decode hv
      subst hx
      simp only [values, List.map_cons, List.cons_append]
      exact congrArg _ (ih rfl)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

theorem Step.context_eq {H : Type*} {s s' : Store H} {f f' : Frame}
    {before after code code' : List Admin} (h : Step noHostCalls ⟨s, f, before⟩ ⟨s', f', after⟩)
    (vs : List Value) (tail : List Admin) (hc : code = values vs ++ before ++ tail)
    (hc' : code' = values vs ++ after ++ tail) : Step noHostCalls ⟨s, f, code⟩ ⟨s', f', code'⟩ := by
  subst hc hc'
  exact .context h vs tail

/-- Soundness of one instruction: the consumed operands and the instruction are a redex. -/
theorem stepInstr?_sound {H : Type*} {s : Store H} {f : Frame} {stack : List Value} {i : Instr}
    {rest : List Value} {s' : Store H} {f' : Frame} {after : List Admin}
    (h : stepInstr? s f stack i = some (rest, s', f', after)) :
    ∃ ops, stack = ops.reverse ++ rest ∧
      Internal ⟨s, f, values ops ++ [.source i]⟩ ⟨s', f', after⟩ := by
  cases i with
  | nop =>
    simp only [stepInstr?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨[], by simp, .pure _ _ .nop⟩
  | unreachable =>
    simp only [stepInstr?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨[], by simp, .pure _ _ .unreachable⟩
  | drop =>
    simp only [stepInstr?] at h
    split at h
    · next v rest' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨[v], by simp, .pure _ _ (.drop v)⟩
    · contradiction
  | select =>
    simp only [stepInstr?] at h
    split at h
    · next c b a rest' =>
      split at h
      · next c' hc =>
        obtain rfl := numOf?_eq hc
        split at h
        · next same =>
          split at h
          · next zero =>
            subst zero
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            exact ⟨[a, b, ⟨.int .i32, 0⟩], by simp; rfl, .pure _ _ (.selectZero a b same)⟩
          · next nonzero =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            exact ⟨[a, b, ⟨.int .i32, c'⟩], by simp,
              .pure _ _ (.selectNonzero a b same c' nonzero)⟩
        · contradiction
      · contradiction
    · contradiction
  | block bt body =>
    simp only [stepInstr?] at h
    split at h
    · next ft resolved =>
      split at h
      · next le =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        refine ⟨(stack.take ft.params.length).reverse, by simp, ?_⟩
        exact .pure _ _ (.block bt body ft resolved _ (by simp; omega))
      · contradiction
    · contradiction
  | loop bt body =>
    simp only [stepInstr?] at h
    split at h
    · next ft resolved =>
      split at h
      · next le =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        refine ⟨(stack.take ft.params.length).reverse, by simp, ?_⟩
        exact .pure _ _ (.loop bt body ft resolved _ (by simp; omega))
      · contradiction
    · contradiction
  | if_ bt left right =>
    simp only [stepInstr?] at h
    split at h
    · next c rest' =>
      split at h
      · next c' hc =>
        obtain rfl := numOf?_eq hc
        split at h
        · next zero =>
          subst zero
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, 0⟩], by simp; rfl, .pure _ _ (.ifZero bt left right)⟩
        · next nonzero =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩], by simp, .pure _ _ (.ifNonzero bt left right c' nonzero)⟩
      · contradiction
    · contradiction
  | br l => simp only [stepInstr?, reduceCtorEq] at h
  | brIf l =>
    simp only [stepInstr?] at h
    split at h
    · next c rest' =>
      split at h
      · next c' hc =>
        obtain rfl := numOf?_eq hc
        split at h
        · next zero =>
          subst zero
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, 0⟩], by simp; rfl, .pure _ _ (.brIfZero l)⟩
        · next nonzero =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩], by simp, .pure _ _ (.brIfNonzero l c' nonzero)⟩
      · contradiction
    · contradiction
  | brTable ls d =>
    simp only [stepInstr?] at h
    split at h
    · next c rest' =>
      split at h
      · next c' hc =>
        obtain rfl := numOf?_eq hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨[⟨.int .i32, c'⟩], by simp, .pure _ _ (.brTable ls d c')⟩
      · contradiction
    · contradiction
  | call i =>
    simp only [stepInstr?] at h
    split at h
    · next a found =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨[], by simp, .call _ _ i a found⟩
    · contradiction
  | callIndirect i =>
    simp only [stepInstr?] at h
    split at h
    · next c rest' =>
      split at h
      · next c' table hc tableFound =>
        obtain rfl := numOf?_eq hc
        split at h
        · next outOfBounds =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩], by simp,
            .callIndirectBounds _ _ i c' table tableFound outOfBounds⟩
        · next null =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩], by simp, .callIndirectNull _ _ i c' table tableFound null⟩
        · next a element =>
          split at h
          · next ft fn typeFound found =>
            split at h
            · next typeMatch =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              exact ⟨[⟨.int .i32, c'⟩], by simp, .callIndirect _ _ i c' table a fn ft tableFound
                typeFound element found typeMatch⟩
            · next typeMismatch =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              exact ⟨[⟨.int .i32, c'⟩], by simp, .callIndirectType _ _ i c' table a fn ft
                tableFound typeFound element found typeMismatch⟩
          · contradiction
      · contradiction
    · contradiction
  | return_ => simp only [stepInstr?, reduceCtorEq] at h
  | localGet i =>
    simp only [stepInstr?] at h
    split at h
    · next v found =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨[], by simp, .localGet _ _ i v found⟩
    · contradiction
  | localSet i =>
    simp only [stepInstr?] at h
    split at h
    · next v rest' old found =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨[v], by simp, .localSet _ _ i v old found⟩
    · contradiction
  | localTee i =>
    simp only [stepInstr?] at h
    split at h
    · next v rest' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨[v], by simp, .pure _ _ (.localTee i v)⟩
    · contradiction
  | globalGet i =>
    simp only [stepInstr?] at h
    split at h
    · next a index =>
      split at h
      · next g found =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨[], by simp, .globalGet _ _ i a g index found⟩
      · contradiction
    · contradiction
  | globalSet i =>
    simp only [stepInstr?] at h
    split at h
    · next v rest' =>
      split at h
      · next a index =>
        split at h
        · next g found =>
          split at h
          · next mutable =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            exact ⟨[v], by simp, .globalSet _ _ i a g v index found mutable⟩
          · contradiction
        · contradiction
      · contradiction
    · contradiction
  | intLoad t packed arg =>
    simp only [stepInstr?] at h
    split at h
    · next c rest' =>
      split at h
      · next c' a m hc memory =>
        obtain rfl := numOf?_eq hc
        split at h
        · next v loaded =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩], by simp, .intLoad _ _ t packed arg c' a m v memory loaded⟩
        · next loaded =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩], by simp, .intLoadTrap _ _ t packed arg c' a m memory loaded⟩
      · contradiction
    · contradiction
  | floatLoad t arg =>
    simp only [stepInstr?] at h
    split at h
    · next c rest' =>
      split at h
      · next c' a m hc memory =>
        obtain rfl := numOf?_eq hc
        split at h
        · next v loaded =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩], by simp, .floatLoad _ _ t arg c' a m v memory loaded⟩
        · next loaded =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩], by simp, .floatLoadTrap _ _ t arg c' a m memory loaded⟩
      · contradiction
    · contradiction
  | intStore t packed arg =>
    simp only [stepInstr?] at h
    split at h
    · next x c rest' =>
      split at h
      · next x' c' a m hx hc memory =>
        obtain rfl := numOf?_eq hx
        obtain rfl := numOf?_eq hc
        split at h
        · next bytes stored =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩, ⟨.int t, x'⟩], by simp,
            .intStore _ _ t packed arg c' x' a m bytes memory stored⟩
        · next stored =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩, ⟨.int t, x'⟩], by simp,
            .intStoreTrap _ _ t packed arg c' x' a m memory stored⟩
      · contradiction
    · contradiction
  | floatStore t arg =>
    simp only [stepInstr?] at h
    split at h
    · next x c rest' =>
      split at h
      · next x' c' a m hx hc memory =>
        obtain rfl := numOf?_eq hx
        obtain rfl := numOf?_eq hc
        split at h
        · next bytes stored =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩, ⟨.float t, x'⟩], by simp,
            .floatStore _ _ t arg c' x' a m bytes memory stored⟩
        · next stored =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩, ⟨.float t, x'⟩], by simp,
            .floatStoreTrap _ _ t arg c' x' a m memory stored⟩
      · contradiction
    · contradiction
  | memorySize =>
    simp only [stepInstr?] at h
    split at h
    · next a m memory =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨[], by simp, .memorySize _ _ a m memory⟩
    · contradiction
  | memoryGrow =>
    simp only [stepInstr?] at h
    split at h
    · next c rest' =>
      split at h
      · next c' a m hc memory =>
        obtain rfl := numOf?_eq hc
        split at h
        · next bytes grown =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩], by simp,
            .memoryGrow _ _ a m c' _ bytes memory (.success bytes grown)⟩
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, c'⟩], by simp, .memoryGrow _ _ a m c' _ m.data memory .failure⟩
      · contradiction
    · contradiction
  | memoryFill =>
    simp only [stepInstr?] at h
    split at h
    · next n b d rest' =>
      split at h
      · next n' b' d' a m hn hb hd memory =>
        obtain rfl := numOf?_eq hn
        obtain rfl := numOf?_eq hb
        obtain rfl := numOf?_eq hd
        split at h
        · next bytes filled =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, d'⟩, ⟨.int .i32, b'⟩, ⟨.int .i32, n'⟩], by simp,
            .memoryFill _ _ d' b' n' a m bytes memory filled⟩
        · next filled =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, d'⟩, ⟨.int .i32, b'⟩, ⟨.int .i32, n'⟩], by simp,
            .memoryFillTrap _ _ d' b' n' a m memory filled⟩
      · contradiction
    · contradiction
  | memoryCopy =>
    simp only [stepInstr?] at h
    split at h
    · next n src d rest' =>
      split at h
      · next n' src' d' a m hn hsrc hd memory =>
        obtain rfl := numOf?_eq hn
        obtain rfl := numOf?_eq hsrc
        obtain rfl := numOf?_eq hd
        split at h
        · next bytes copied =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, d'⟩, ⟨.int .i32, src'⟩, ⟨.int .i32, n'⟩], by simp,
            .memoryCopy _ _ d' src' n' a m bytes memory copied⟩
        · next copied =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int .i32, d'⟩, ⟨.int .i32, src'⟩, ⟨.int .i32, n'⟩], by simp,
            .memoryCopyTrap _ _ d' src' n' a m memory copied⟩
      · contradiction
    · contradiction
  | intConst t b => simp only [stepInstr?, reduceCtorEq] at h
  | floatConst t b => simp only [stepInstr?, reduceCtorEq] at h
  | intUnOp t op =>
    simp only [stepInstr?] at h
    split at h
    · next x rest' =>
      split at h
      · next x' hx =>
        obtain rfl := numOf?_eq hx
        split at h
        · next valid =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int t, x'⟩], by simp, .pure _ _ (.intUnary t op x' valid)⟩
        · contradiction
      · contradiction
    · contradiction
  | intBinOp t op =>
    simp only [stepInstr?] at h
    split at h
    · next y x rest' =>
      split at h
      · next x' y' hx hy =>
        obtain rfl := numOf?_eq hx
        obtain rfl := numOf?_eq hy
        split at h
        · next z hz =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int t, x'⟩, ⟨.int t, y'⟩], by simp, .pure _ _ (.intBinary t op x' y' z hz)⟩
        · next err hz =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨.int t, x'⟩, ⟨.int t, y'⟩], by simp,
            .pure _ _ (.intBinaryTrap t op x' y' err hz)⟩
      · contradiction
    · contradiction
  | intTestOp t op =>
    simp only [stepInstr?] at h
    split at h
    · next x rest' =>
      split at h
      · next x' hx =>
        obtain rfl := numOf?_eq hx
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨[⟨.int t, x'⟩], by simp, .pure _ _ (.intTest t op x')⟩
      · contradiction
    · contradiction
  | intRelOp t op =>
    simp only [stepInstr?] at h
    split at h
    · next y x rest' =>
      split at h
      · next x' y' hx hy =>
        obtain rfl := numOf?_eq hx
        obtain rfl := numOf?_eq hy
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨[⟨.int t, x'⟩, ⟨.int t, y'⟩], by simp, .pure _ _ (.intRel t op x' y')⟩
      · contradiction
    · contradiction
  | floatUnOp t op =>
    simp only [stepInstr?] at h
    split at h
    · next x rest' =>
      split at h
      · next x' hx =>
        obtain rfl := numOf?_eq hx
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨[⟨.float t, x'⟩], by simp,
          .pure _ _ (.floatUnary t op x' _ (Numerics.floatUnOpRel_self t op x'))⟩
      · contradiction
    · contradiction
  | floatBinOp t op =>
    simp only [stepInstr?] at h
    split at h
    · next y x rest' =>
      split at h
      · next x' y' hx hy =>
        obtain rfl := numOf?_eq hx
        obtain rfl := numOf?_eq hy
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨[⟨.float t, x'⟩, ⟨.float t, y'⟩], by simp,
          .pure _ _ (.floatBinary t op x' y' _ (Numerics.floatBinOpRel_self t op x' y'))⟩
      · contradiction
    · contradiction
  | floatRelOp t op =>
    simp only [stepInstr?] at h
    split at h
    · next y x rest' =>
      split at h
      · next x' y' hx hy =>
        obtain rfl := numOf?_eq hx
        obtain rfl := numOf?_eq hy
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨[⟨.float t, x'⟩, ⟨.float t, y'⟩], by simp, .pure _ _ (.floatRel t op x' y')⟩
      · contradiction
    · contradiction
  | convert op =>
    simp only [stepInstr?] at h
    split at h
    · next x rest' =>
      split at h
      · next x' hx =>
        obtain rfl := numOf?_eq hx
        have hrel := Numerics.convertRel_self op x'
        split at h
        · next y hy =>
          rw [hy] at hrel
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨op.source, x'⟩], by simp, .pure _ _ (.convert op x' y hrel)⟩
        · next err hy =>
          rw [hy] at hrel
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨[⟨op.source, x'⟩], by simp, .pure _ _ (.convertTrap op x' err hrel)⟩
      · contradiction
    · contradiction

mutual
/-- Soundness of the executable stepper against the host-free machine. -/
theorem stepFrom?_sound {H : Type*} : ∀ (s : Store H) (f : Frame) (stack : List Value)
    (code : List Admin) (s' : Store H) (f' : Frame) (code' : List Admin),
    stepFrom? s f stack code = some (s', f', code') →
    Internal ⟨s, f, values stack.reverse ++ code⟩ ⟨s', f', code'⟩
  | _, _, _, [], _, _, _, h => by simp only [stepFrom?, reduceCtorEq] at h
  | s, f, stack, x :: tail, s', f', code', h => by
    simp only [stepFrom?] at h
    split at h
    · next v hv =>
      have hx : value v = x := coding.encode_of_decode hv
      subst hx
      have := stepFrom?_sound s f (v :: stack) tail s' f' code' h
      simpa [List.append_assoc, values] using this
    · exact stepHead?_sound s f stack tail x s' f' code' h
termination_by structural _ _ _ code => code

theorem stepHead?_sound {H : Type*} : ∀ (s : Store H) (f : Frame) (stack : List Value)
    (tail : List Admin) (x : Admin) (s' : Store H) (f' : Frame) (code' : List Admin),
    stepHead? s f stack tail x = some (s', f', code') →
    Internal ⟨s, f, values stack.reverse ++ x :: tail⟩ ⟨s', f', code'⟩
  | s, f, stack, tail, .source i, s', f', code', h => by
    simp only [stepHead?, Option.map_eq_some_iff] at h
    obtain ⟨⟨rest, s1, f1, after⟩, hi, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    obtain ⟨ops, rfl, hstep⟩ := stepInstr?_sound hi
    exact hstep.context_eq rest.reverse tail (by simp) rfl
  | s, f, stack, tail, .invoke a, s', f', code', h => by
    simp only [stepHead?] at h
    split at h
    · next ft module fn found =>
      split at h
      · next le =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine (Step.invokeWasm s f a ft module fn (stack.take ft.params.length).reverse found
          (by simp; omega)).context_eq (stack.drop ft.params.length).reverse tail ?_ rfl
        rw [show stack.reverse = (stack.drop ft.params.length).reverse ++
          (stack.take ft.params.length).reverse by
            rw [← List.reverse_append, List.take_append_drop]]
        simp
      · contradiction
    · contradiction
  | s, f, stack, tail, .trap, s', f', code', h => by
    simp only [stepHead?] at h
    split at h
    · contradiction
    · next hne =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      cases stack with
      | nil =>
        cases tail with
        | nil => exact (hne rfl rfl).elim
        | cons i t => exact .pure _ _ (.trapTail i t)
      | cons v vs =>
        obtain ⟨w, ws, hw⟩ := List.exists_cons_of_ne_nil (by simp : (v :: vs).reverse ≠ [])
        rw [hw]
        have := PureStep.trapValues (types := f.module.types) w ws tail
        exact .pure _ _ (by simpa using this)
  | s, f, stack, tail, .label n cont body, s', f', code', h => by
    simp only [stepHead?] at h
    split at h
    · next vs heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hb := splitValues_eq heq
      simp only [List.append_nil] at hb
      subst hb
      exact (Step.pure s f (.labelDone n cont vs)).context_eq stack.reverse tail (by simp) rfl
    · next heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hb := splitValues_eq heq
      simp only [values, List.map_nil, List.nil_append] at hb
      subst hb
      exact (Step.pure s f (.labelTrap n cont)).context_eq stack.reverse tail (by simp) rfl
    · next vs l t heq =>
      have hb := splitValues_eq heq
      subst hb
      split at h
      · next zero =>
        have hl : l = ⟨0⟩ := Idx.toNat_injective zero
        subst hl
        split at h
        · next le =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have step := PureStep.labelBranch (types := f.module.types) n cont
            (vs.take (vs.length - n)) (vs.drop (vs.length - n)) t (by simp; omega)
          refine (Step.pure s f step).context_eq stack.reverse tail ?_ rfl
          rw [← values_append, List.take_append_drop]
          simp
        · contradiction
      · next outer =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact (Step.pure s f (.labelBranchOuter n cont vs t l outer)).context_eq stack.reverse
          tail (by simp) rfl
    · next vs t heq =>
      have hb := splitValues_eq heq
      subst hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (Step.pure s f (.labelReturn n cont vs t)).context_eq stack.reverse tail
        (by simp) rfl
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s1, f1, body'⟩, hbody, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      have ih := stepFrom?_sound s f [] body s1 f1 body' hbody
      simp only [List.reverse_nil, values, List.map_nil, List.nil_append] at ih
      exact (Step.label ih n cont).context_eq stack.reverse tail (by simp) rfl
  | s, f, stack, tail, .frame n fr body, s', f', code', h => by
    simp only [stepHead?] at h
    split at h
    · next vs heq =>
      split at h
      · next arity =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hb := splitValues_eq heq
        simp only [List.append_nil] at hb
        subst hb
        exact (Step.pure s f (.frameDone n fr vs arity)).context_eq stack.reverse tail
          (by simp) rfl
      · contradiction
    · next heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hb := splitValues_eq heq
      simp only [values, List.map_nil, List.nil_append] at hb
      subst hb
      exact (Step.pure s f (.frameTrap n fr)).context_eq stack.reverse tail (by simp) rfl
    · next vs t heq =>
      have hb := splitValues_eq heq
      subst hb
      split at h
      · next le =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have step := PureStep.frameReturn (types := f.module.types) n fr
          (vs.take (vs.length - n)) (vs.drop (vs.length - n)) t (by simp; omega)
        refine (Step.pure s f step).context_eq stack.reverse tail ?_ rfl
        rw [← values_append, List.take_append_drop]
        simp
      · contradiction
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s1, fr1, body'⟩, hbody, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      have ih := stepFrom?_sound s fr [] body s1 fr1 body' hbody
      simp only [List.reverse_nil, values, List.map_nil, List.nil_append] at ih
      exact (Step.frame ih n f).context_eq stack.reverse tail (by simp) rfl
termination_by structural _ _ _ _ x => x
end

theorem step?_sound {H : Type*} {cfg cfg' : Config H} (h : step? cfg = some cfg') :
    Internal cfg cfg' := by
  obtain ⟨s, f, code⟩ := cfg
  simp only [step?, Option.map_eq_some_iff] at h
  obtain ⟨⟨s1, f1, code1⟩, h1, rfl⟩ := h
  simpa [values] using stepFrom?_sound s f [] code s1 f1 code1 h1

/-! ## The fuel driver -/

theorem terminal?_sound {code : List Admin} {r : Result} (h : terminal? code = some r) :
    code = result r := by
  unfold terminal? at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · split at h
    · next vs heq =>
      simp only [Option.some.injEq] at h
      subst h
      simpa [result] using splitValues_eq heq
    · contradiction

/-- What each driver status guarantees about the configuration returned with it. -/
def Status.Holds {H : Type*} (cfg : Config H) : Status H → Prop
  | .returned r => cfg.code = result r
  | .callout c => CalloutAt cfg c
  | .stuck => step? cfg = none ∧ decompose? cfg = none
  | .exhausted => True

/-- Soundness of `run`: it follows host-free steps, and its status is truthful. -/
theorem run_sound {H : Type*} (n : Nat) (cfg : Config H) :
    Relation.ReflTransGen Internal cfg (run n cfg).1 ∧ (run n cfg).2.Holds (run n cfg).1 := by
  induction n generalizing cfg with
  | zero =>
    rw [run]
    split
    · next r hr => exact ⟨.refl, terminal?_sound hr⟩
    · split
      · next c hc => exact ⟨.refl, decompose?_sound hc⟩
      · exact ⟨.refl, trivial⟩
  | succ n ih =>
    rw [run]
    split
    · next r hr => exact ⟨.refl, terminal?_sound hr⟩
    · split
      · next c hc => exact ⟨.refl, decompose?_sound hc⟩
      · next hc =>
        split
        · next next hs =>
          obtain ⟨steps, holds⟩ := ih next
          exact ⟨.head (step?_sound hs) steps, holds⟩
        · next hs => exact ⟨.refl, hs, hc⟩

theorem run_steps {H : Type*} (host : HostSemantics H) (n : Nat) (cfg : Config H) :
    Steps host cfg (run n cfg).1 :=
  Steps.of_internal (run_sound n cfg).1

theorem run_returned {H : Type*} {n : Nat} {cfg final : Config H} {r : Result}
    (h : run n cfg = (final, .returned r)) : final.code = result r := by
  have := (run_sound n cfg).2
  rw [h] at this
  exact this

theorem run_callout {H : Type*} {n : Nat} {cfg parked : Config H} {c : Runtime.Callout H Instr}
    (h : run n cfg = (parked, .callout c)) : CalloutAt parked c := by
  have := (run_sound n cfg).2
  rw [h] at this
  exact this

/-- Driving to a callout, answering it, and driving the resumed configuration is a run of the
atomic machine under any host relation that admits the answer. -/
theorem run_resume_steps {H : Type*} {host : HostSemantics H} {n m : Nat}
    {cfg parked : Config H} {c : Runtime.Callout H Instr} {s' : Store H} {r : Result}
    (h : run n cfg = (parked, .callout c))
    (answer : host c.host parked.store c.args (.returned s' r)) :
    Steps host cfg (run m (resume parked c s' r)).1 := by
  have first := run_steps host n cfg
  rw [h] at first
  exact first.trans ((Step.callout_returned (run_callout h) answer).steps.trans
    (run_steps host m _))

/-! ## Example: an imported host function parks and resumes a stored Wasm function -/

namespace CalloutExamples

def unaryType : FuncType := ⟨[.i32], [.i32]⟩

def callerCode : Func :=
  ⟨⟨0⟩, [], [.localGet ⟨0⟩, .call ⟨0⟩, .intConst .i32 1, .intBinOp .i32 .add]⟩

/-- `(import "env" "double" (func (param i32) (result i32)))` and an exported function that
calls it and adds one. -/
def callerModule : Module where
  types := [unaryType]
  imports := [⟨"env", "double", .func ⟨0⟩⟩]
  funcs := [callerCode]
  exports := [⟨"run", .func ⟨1⟩⟩]

/-- The embedder allocated the host function first; its host code is the string tag. -/
def hostStore : Store String := {funcs := [.host unaryType "double"]}

def callerInst : ModuleInst where
  types := [unaryType]
  funcs := [⟨0⟩, ⟨1⟩]
  exports := [⟨"run", .func ⟨1⟩⟩]

def callerStore : Store String where
  funcs := [.host unaryType "double", .wasm unaryType callerInst callerCode]

theorem callerModule_valid : Validation.ModuleValid callerModule where
  types := by intro ft hf; trivial
  imports := by
    intro i hi
    simp only [callerModule, List.mem_singleton] at hi
    subst i
    exact ⟨.func unaryType, rfl, trivial⟩
  functions := by
    intro f hf
    simp only [callerModule, List.mem_singleton] at hf
    subst f
    refine ⟨unaryType, rfl, trivial, ?_⟩
    exact .cons (.localGet _ rfl) (.cons (.call (ft := unaryType) _ rfl)
      (.cons (.frame [.i32] (.intConst .i32 1)) (.cons (.intBinOp .i32 .add) (.nil _))))
  tables := by simp [callerModule]
  memories := by simp [callerModule]
  globals := by simp [callerModule]
  elements := by simp [callerModule]
  data := by simp [callerModule]
  start := by simp [Validation.StartValid, callerModule]
  exports := by
    intro e he
    simp only [callerModule, List.mem_singleton] at he
    subst e
    exact ⟨.func unaryType, rfl⟩
  uniqueExports := by simp [callerModule]
  singleTable := by simp [Validation.moduleContext, callerModule]
  singleMemory := by simp [Validation.moduleContext, callerModule]

theorem callerModule_prepares :
    prepare? hostStore callerModule [.func ⟨0⟩] = some ⟨callerStore, callerInst, []⟩ := rfl

/-- Instantiation against the host import, for every host relation (there is no start). -/
theorem callerModule_instantiates (host : HostSemantics String) :
    Instantiation host hostStore callerModule [.func ⟨0⟩] callerStore callerInst (.values []) where
  valid := callerModule_valid
  importsMatch := .cons ⟨.func unaryType, rfl, .func ⟨0⟩ _ unaryType rfl rfl⟩ .nil
  prepared := ⟨⟨callerStore, callerInst, []⟩, rfl, rfl, .refl⟩

/-- Invoke the exported function on `x`. -/
def start (x : BitVec 32) : Config String :=
  ⟨callerStore, ⟨[], callerInst⟩, values [.int .i32 x] ++ [.invoke ⟨1⟩]⟩

/-- The configuration parked at the import call. -/
def parked (x : BitVec 32) : Config String :=
  ⟨callerStore, ⟨[], callerInst⟩, [.frame 1 ⟨[.int .i32 x], callerInst⟩
    [.label 1 [] [value (.int .i32 x), .invoke ⟨0⟩, .source (.intConst .i32 1),
      .source (.intBinOp .i32 .add)]]]⟩

def parkedCallout (x : BitVec 32) : Runtime.Callout String Instr :=
  ⟨.seq [] (.frame 1 ⟨[.int .i32 x], callerInst⟩ (.seq [] (.label 1 []
    (.seq [] .hole [.source (.intConst .i32 1), .source (.intBinOp .i32 .add)])) [])) [],
    ⟨0⟩, unaryType, "double", [.int .i32 x]⟩

/-- The driver runs the stored code (invocation, `local.get`, `call`) and stops at the host
function address `0` with host code `"double"` and the argument, for every `x`. -/
theorem run_start (x : BitVec 32) : run 8 (start x) = (parked x, .callout (parkedCallout x)) :=
  rfl

theorem parked_callout (x : BitVec 32) : CalloutAt (parked x) (parkedCallout x) :=
  run_callout (run_start x)

/-- Parking is observable: no host-free step exists there. -/
theorem parked_no_internal (x : BitVec 32) (cfg : Config String) : ¬ Internal (parked x) cfg :=
  (parked_callout x).not_internal

/-- Resuming with any host result `y` finishes the caller's computation. -/
theorem run_resume (x y : BitVec 32) :
    run 8 (resume (parked x) (parkedCallout x) callerStore (.values [.int .i32 y])) =
      (⟨callerStore, ⟨[], callerInst⟩, values [.int .i32 (y + 1 : BitVec 32)]⟩,
        .returned (.values [.int .i32 (y + 1 : BitVec 32)])) := rfl

/-- Resuming with a trap propagates it out of the label and frame. -/
theorem run_resume_trap (x : BitVec 32) :
    run 8 (resume (parked x) (parkedCallout x) callerStore .trap) =
      (⟨callerStore, ⟨[], callerInst⟩, [.trap]⟩, .returned .trap) := rfl

/-- A host relation that doubles its argument. -/
def doubleHost : HostSemantics String := fun h s args outcome =>
  h = "double" ∧ ∃ x, args = [.int .i32 x] ∧ outcome = .returned s (.values [.int .i32 (x + x)])

/-- End to end in the atomic machine: the open run, the host's answer, and the resumed run
compose to a `Steps` derivation of the existing semantics. -/
theorem start_steps (x : BitVec 32) :
    Steps doubleHost (start x)
      ⟨callerStore, ⟨[], callerInst⟩, values [.int .i32 (x + x + 1 : BitVec 32)]⟩ := by
  have h := run_resume_steps (host := doubleHost) (m := 8) (run_start x)
    (s' := callerStore) (r := .values [.int .i32 (x + x)]) ⟨rfl, x, rfl, rfl⟩
  rwa [run_resume] at h

end CalloutExamples

end Silmaril.Wasm.Lime1.Execution
