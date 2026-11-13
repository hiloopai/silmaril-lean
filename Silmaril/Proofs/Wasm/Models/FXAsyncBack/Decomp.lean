module

public import Silmaril.Wasm.Models.FXVRuns.Thms

/-!
# Inversion of `StepFX'` under a value prefix and a suffix

Silmaril's `Step.decomp` shows that a host-free Core step is a *head step* at the first
non-value of the code (under a value prefix and a suffix), or the bubbling of a trap or an
exception. This module proves the same for `StepFX'` (no host calls), with FX values (Core
values and continuation references):

* `FHead`: the rules of `StepFX'` other than `seq`, `trapSeq` and `throwSeq`, applied to
  `fvals V ++ [e]`, with Core's head steps (`Silmaril.Wasm.SingleThreaded.Det.Head`) for the
  rule `core`;
* **`stepFX'_decomp`**: a `StepFX'` step of `L` is an `FHead` step at the first non-value `e` of
  `L` (`L = fvals V₁ ++ (fvals V₂ ++ e :: T)`, the head consuming the values `V₂`), or `L` has a
  trap or a `throw_ref` at its first non-value;
* `fhead_val`: the instruction of a head step is not an FX value.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fvals_append fvals_nil fvals_cons fval?_toAdmin)
open Silmaril.Proofs.Wasm.Models.FXLower (blockFX_noHost)
open Silmaril.Wasm.SingleThreaded.Det (noHost Head HeadDec Bubble IsBubble)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} (P : Profile) (fx : H → Option FuncFX)

/-- **Head steps of `StepFX'`**: a rule other than `seq`, `trapSeq` and `throwSeq`, at the
non-value `e` with the FX values `V` before it. -/
inductive FHead : Store H → List (Option ContFX) → Frame → List FVal → AdminFX → ConfigFX H →
    Prop where
  | core {s : Store H} {K : List (Option ContFX)} {f : Frame} {args : List Val} {e : Admin}
      {c₀ : Config H} (h : Head P s f args e c₀) :
      FHead s K f (liftV args) (.core e) ⟨c₀.store, K, c₀.frame, c₀.code.map .core⟩
  | ctxLabel {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {n : Nat}
      {k : List InstrFX} {es es' : List AdminFX}
      (h : StepFX' P noHost fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      FHead s K f [] (.label n k es) ⟨s', K', f', [.label n k es']⟩
  | ctxFrame {s s' : Store H} {K K' : List (Option ContFX)} {f fi fi' : Frame} {n : Nat}
      {es es' : List AdminFX} (h : StepFX' P noHost fx ⟨s, K, fi, es⟩ ⟨s', K', fi', es'⟩) :
      FHead s K f [] (.frame n fi es) ⟨s', K', f, [.frame n fi' es']⟩
  | ctxHandler {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
      {hs : List HClause} {es es' : List AdminFX}
      (h : StepFX' P noHost fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      FHead s K f [] (.handler hs es) ⟨s', K', f', [.handler hs es']⟩
  | block {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      FHead s K f vs (.block bt body)
        ⟨s, K, f, [.label t₂.length [] (fvals vs ++ body.map InstrFX.toAdmin)]⟩
  | loop {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      FHead s K f vs (.loop bt body)
        ⟨s, K, f, [.label t₁.length [.loop bt body] (fvals vs ++ body.map InstrFX.toAdmin)]⟩
  | ifTrue {s : Store H} {K : List (Option ContFX)} {f : Frame} {c : BitVec 32}
      {bt : BlockType} {b₁ b₂ : List InstrFX} (hc : c ≠ 0) :
      FHead s K f [.val (Val.i32 c)] (.if_ bt b₁ b₂) ⟨s, K, f, [.block bt b₁]⟩
  | ifFalse {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {b₁ b₂ : List InstrFX} :
      FHead s K f [.val (Val.i32 0)] (.if_ bt b₁ b₂) ⟨s, K, f, [.block bt b₂]⟩
  | labelVals {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} :
      FHead s K f [] (.label n k (fvals vs)) ⟨s, K, f, fvals vs⟩
  | brLabelZero {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs' vs : List FVal} {l : LabelIdx} {rest : List AdminFX}
      (hl : l.toNat = 0) (hn : vs.length = n) :
      FHead s K f [] (.label n k (fvals vs' ++ fvals vs ++ [.core (.plain (.br l))] ++ rest))
        ⟨s, K, f, fvals vs ++ k.map InstrFX.toAdmin⟩
  | brLabelSucc {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} {l : LabelIdx} {rest : List AdminFX}
      (hl : 0 < l.toNat) :
      FHead s K f [] (.label n k (fvals vs ++ [.core (.plain (.br l))] ++ rest))
        ⟨s, K, f, fvals vs ++ [.core (.plain (.br (labelPred l)))]⟩
  | brHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} {l : LabelIdx} {rest : List AdminFX} :
      FHead s K f [] (.handler hs (fvals vs ++ [.core (.plain (.br l))] ++ rest))
        ⟨s, K, f, fvals vs ++ [.core (.plain (.br l))]⟩
  | returnLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} {rest : List AdminFX} :
      FHead s K f [] (.label n k (fvals vs ++ [.core (.plain .return_)] ++ rest))
        ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩
  | returnHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} {rest : List AdminFX} :
      FHead s K f [] (.handler hs (fvals vs ++ [.core (.plain .return_)] ++ rest))
        ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩
  | frameVals {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat}
      {vs : List FVal} (hn : vs.length = n) :
      FHead s K f [] (.frame n fi (fvals vs)) ⟨s, K, f, fvals vs⟩
  | returnFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat}
      {vs' vs : List FVal} {rest : List AdminFX} (hn : vs.length = n) :
      FHead s K f [] (.frame n fi (fvals vs' ++ fvals vs ++ [.core (.plain .return_)] ++ rest))
        ⟨s, K, f, fvals vs⟩
  | handlerVals {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} :
      FHead s K f [] (.handler hs (fvals vs)) ⟨s, K, f, fvals vs⟩
  | dropCont {s : Store H} {K : List (Option ContFX)} {f : Frame} {k : Nat} :
      FHead s K f [.cont k] (.core (.plain .drop)) ⟨s, K, f, []⟩
  | trapLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} :
      FHead s K f [] (.label n k [.core .trap]) ⟨s, K, f, [.core .trap]⟩
  | trapFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat} :
      FHead s K f [] (.frame n fi [.core .trap]) ⟨s, K, f, [.core .trap]⟩
  | trapHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause} :
      FHead s K f [] (.handler hs [.core .trap]) ⟨s, K, f, [.core .trap]⟩
  | throwLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {a : Nat} :
      FHead s K f [] (.label n k (cthrowing a)) ⟨s, K, f, cthrowing a⟩
  | throwFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat} {a : Nat} :
      FHead s K f [] (.frame n fi (cthrowing a)) ⟨s, K, f, cthrowing a⟩
  | throwHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {a : Nat} :
      FHead s K f [] (.handler hs (cthrowing a)) ⟨s, K, f, cthrowing a⟩
  | invoke {s : Store H} {K : List (Option ContFX)} {f : Frame} {c : Admin} {vs : List Val}
      {a : Nat} {fi : FuncInst H} {h : H} {F : FuncFX} (hc : c.IsCallRef)
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host h) (hfx : fx h = some F)
      (hn : vs.length = F.nparams) :
      FHead s K f (liftV vs ++ [.val (.ref (.func a))]) (.core c)
        ⟨s, K, f, [.frame F.nresults (Frame.forCall F.module vs F.locals)
          [.label F.nresults [] (F.body.map InstrFX.toAdmin)]]⟩
  | contNew {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H}
      {ct : TypeIdx} (hf : s.funcs[a]? = some fi) :
      FHead s K f [.val (.ref (.func a))] (.fx (.contNew ct))
        ⟨s, K ++ [some ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩], f,
          [.contRef K.length]⟩
  | contNewNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx} :
      FHead s K f [.val (.ref .null)] (.fx (.contNew ct)) ⟨s, K, f, [.core .trap]⟩
  | contBind {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {C : ContFX} {ct ct' : TypeIdx} (hk : K[k]? = some (some C)) :
      FHead s K f (vs ++ [.cont k]) (.fx (.contBind ct ct'))
        ⟨s, K.set k none ++ [some ⟨fun c => C.plug (fvals vs ++ c)⟩], f, [.contRef K.length]⟩
  | contBindNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {ct ct' : TypeIdx} :
      FHead s K f (vs ++ [.val (.ref .null)]) (.fx (.contBind ct ct')) ⟨s, K, f, [.core .trap]⟩
  | contBindUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {ct ct' : TypeIdx} (hk : K[k]? = some none) :
      FHead s K f (vs ++ [.cont k]) (.fx (.contBind ct ct')) ⟨s, K, f, [.core .trap]⟩
  | resume {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {C : ContFX} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause}
      (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs') :
      FHead s K f (vs ++ [.cont k]) (.fx (.resume ct hs))
        ⟨s, K.set k none, f, [.handler hs' (C.plug (fvals vs))]⟩
  | resumeNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {ct : TypeIdx} {hs : List OnClause} :
      FHead s K f (vs ++ [.val (.ref .null)]) (.fx (.resume ct hs)) ⟨s, K, f, [.core .trap]⟩
  | resumeUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {ct : TypeIdx} {hs : List OnClause} (hk : K[k]? = some none) :
      FHead s K f (vs ++ [.cont k]) (.fx (.resume ct hs)) ⟨s, K, f, [.core .trap]⟩
  | resumeThrow {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val} {k : Nat}
      {C : ContFX} {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} {hs' : List HClause}
      {ta : Nat} {ti : TagInst} (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
      (hr : hs.mapM (resolve s f) = some hs') :
      FHead s K f (liftV vs ++ [.cont k]) (.fx (.resumeThrow ct x hs))
        ⟨s.addExn ⟨ta, vs⟩, K.set k none, f, [.handler hs' (C.plug (cthrowing s.exns.length))]⟩
  | resumeThrowNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val}
      {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} :
      FHead s K f (liftV vs ++ [.val (.ref .null)]) (.fx (.resumeThrow ct x hs))
        ⟨s, K, f, [.core .trap]⟩
  | suspend {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {E : CtxV} {vs : List FVal} {x : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx}
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
      FHead s K f [] (.handler hs (E.plug (fvals vs ++ [.fx (.suspend x)])))
        ⟨s, K ++ [some ⟨E.plug⟩], f, fvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩
  | switch {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {E : CtxV} {vs : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx} {ta : Nat}
      {ti : TagInst} (hk : K[k]? = some (some C))
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onSwitch ta)) :
      FHead s K f [] (.handler hs (E.plug (fvals vs ++ [.contRef k, .fx (.switch ct x)])))
        ⟨s, K.set k none ++ [some ⟨E.plug⟩], f,
          [.handler hs (C.plug (fvals vs ++ [.contRef K.length]))]⟩

/-- A bubbling trap or exception at the first non-value. -/
def FBub (L : List AdminFX) : Prop :=
  ∃ V T, L = fvals V ++ .core .trap :: T ∨ L = fvals V ++ .core (.plain .throwRef) :: T

/-- A head step at the first non-value, under a value prefix and a suffix. -/
def FDec (s : Store H) (K : List (Option ContFX)) (f : Frame) (L : List AdminFX)
    (d : ConfigFX H) : Prop :=
  ∃ V₁ V₂ e T d₀, L = fvals V₁ ++ (fvals V₂ ++ e :: T) ∧ fval? e = none ∧
    FHead P fx s K f V₂ e d₀ ∧ d = ⟨d₀.store, d₀.conts, d₀.frame, fvals V₁ ++ d₀.code ++ T⟩

variable {P fx}

theorem liftV_fvals (vs : List Val) : fvals (liftV vs) = cvals vs := by
  simp [fvals, liftV, cvals, vals, FVal.toAdmin, Function.comp_def]

@[simp] theorem fvals_map_val (vs : List Val) : fvals (vs.map FVal.val) = (vals vs).map .core := by
  simp [fvals, vals, FVal.toAdmin, Function.comp_def]

/-- A head step at the whole code. -/
theorem fdec_of_head {s : Store H} {K : List (Option ContFX)} {f : Frame} {V : List FVal}
    {e : AdminFX} {d : ConfigFX H} (he : fval? e = none) (h : FHead P fx s K f V e d) :
    FDec P fx s K f (fvals V ++ [e]) d :=
  ⟨[], V, e, [], d, by simp, he, h, by cases d; simp⟩

theorem fdec_seq {s : Store H} {K : List (Option ContFX)} {f : Frame} {es : List AdminFX}
    {d : ConfigFX H} (vs : List FVal) (rest : List AdminFX) (h : FDec P fx s K f es d) :
    FDec P fx s K f (fvals vs ++ es ++ rest)
      ⟨d.store, d.conts, d.frame, fvals vs ++ d.code ++ rest⟩ := by
  obtain ⟨V₁, V₂, e, T, d₀, rfl, he, hh, rfl⟩ := h
  exact ⟨vs ++ V₁, V₂, e, T ++ rest, d₀, by simp, he, hh, by simp⟩

theorem fbub_seq {es : List AdminFX} (vs : List FVal) (rest : List AdminFX) (h : FBub es) :
    FBub (fvals vs ++ es ++ rest) := by
  obtain ⟨V, T, rfl | rfl⟩ := h
  · exact ⟨vs ++ V, T ++ rest, Or.inl (by simp)⟩
  · exact ⟨vs ++ V, T ++ rest, Or.inr (by simp)⟩

theorem isCallRef_fval {c : Admin} (hc : c.IsCallRef) : fval? (.core c) = none := by
  simp [Silmaril.Proofs.Wasm.Models.FXLower.IsCallRef.val?_none hc]

/-- The `core` rule: Silmaril's decomposition of a Core step, on FX code. -/
theorem core_decomp {s s' : Store H} {K : List (Option ContFX)} {f f' : Frame}
    {cs cs' : List Admin} (h : Step P (blockFX noHost fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩) :
    FDec P fx s K f (cs.map .core) ⟨s', K, f', cs'.map .core⟩ ∨ FBub (cs.map .core) := by
  rw [blockFX_noHost fx] at h
  rcases Silmaril.Wasm.SingleThreaded.Det.Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, rest, c₀, hcs, hh, hc'⟩ := hd
    simp only at hcs hh hc'
    refine Or.inl ⟨liftV vs, liftV args, .core e, rest.map .core, _, ?_, ?_,
      FHead.core (K := K) hh, ?_⟩
    · rw [hcs]; simp [liftV]
    · simp [(Silmaril.Wasm.SingleThreaded.Det.Head.good hh).val_none]
    · rw [Config.mk.injEq] at hc'
      obtain ⟨rfl, rfl, rfl⟩ := hc'
      simp [liftV]
  · obtain ⟨p, q, X, u, r, hcs, hX, -, -⟩ := hb
    simp only at hcs
    rcases hX with rfl | ⟨a, rfl⟩
    · exact Or.inr ⟨liftV (p ++ q), (u ++ r).map .core, Or.inl (by rw [hcs]; simp [liftV])⟩
    · exact Or.inr ⟨liftV (p ++ q ++ [.ref (.exn a)]), (u ++ r).map .core,
        Or.inr (by rw [hcs]; simp [liftV, FVal.toAdmin, Val.toAdmin])⟩

theorem fdec_invoke {s : Store H} {K : List (Option ContFX)} {f : Frame} {c : Admin}
    {vs : List Val} {a : Nat} {fi : FuncInst H} {h : H} {F : FuncFX} (hc : c.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host h) (hfx : fx h = some F)
    (hn : vs.length = F.nparams) :
    FDec P fx s K f (cvals vs ++ [.core (.ref (.func a)), .core c])
      ⟨s, K, f, [.frame F.nresults (Frame.forCall F.module vs F.locals)
        [.label F.nresults [] (F.body.map InstrFX.toAdmin)]]⟩ := by
  have h₁ : FDec P fx s K f (fvals (liftV vs ++ [.val (.ref (.func a))]) ++ [.core c])
      ⟨s, K, f, [.frame F.nresults (Frame.forCall F.module vs F.locals)
        [.label F.nresults [] (F.body.map InstrFX.toAdmin)]]⟩ :=
    fdec_of_head (isCallRef_fval hc) (FHead.invoke hc hf hcode hfx hn)
  have e : fvals (liftV vs ++ [.val (.ref (.func a))]) ++ [.core c] =
      cvals vs ++ [.core (.ref (.func a)), .core c] := by
    simp [FVal.toAdmin, Val.toAdmin]
  exact e ▸ h₁

/-- **Decomposition of a `StepFX'` step** (no host calls). -/
theorem stepFX'_decomp {x y : ConfigFX H} (h : StepFX' P noHost fx x y) :
    FDec P fx x.store x.conts x.frame x.code y ∨ FBub x.code := by
  induction h with
  | core h => exact core_decomp h
  | seq _ _ ih =>
    rcases ih with hd | hb
    · exact Or.inl (fdec_seq _ _ hd)
    · exact Or.inr (fbub_seq _ _ hb)
  | ctxLabel h => exact Or.inl (fdec_of_head (V := []) rfl (.ctxLabel h))
  | ctxFrame h => exact Or.inl (fdec_of_head (V := []) rfl (.ctxFrame h))
  | ctxHandler h => exact Or.inl (fdec_of_head (V := []) rfl (.ctxHandler h))
  | block hbt hm => exact Or.inl (fdec_of_head rfl (.block hbt hm))
  | loop hbt hm => exact Or.inl (fdec_of_head rfl (.loop hbt hm))
  | ifTrue hc => exact Or.inl (fdec_of_head rfl (.ifTrue hc))
  | ifFalse => exact Or.inl (fdec_of_head rfl .ifFalse)
  | labelVals => exact Or.inl (fdec_of_head (V := []) rfl .labelVals)
  | brLabelZero hl hn => exact Or.inl (fdec_of_head (V := []) rfl (.brLabelZero hl hn))
  | brLabelSucc hl => exact Or.inl (fdec_of_head (V := []) rfl (.brLabelSucc hl))
  | brHandler => exact Or.inl (fdec_of_head (V := []) rfl .brHandler)
  | returnLabel => exact Or.inl (fdec_of_head (V := []) rfl .returnLabel)
  | returnHandler => exact Or.inl (fdec_of_head (V := []) rfl .returnHandler)
  | frameVals hn => exact Or.inl (fdec_of_head (V := []) rfl (.frameVals hn))
  | returnFrame hn => exact Or.inl (fdec_of_head (V := []) rfl (.returnFrame hn))
  | handlerVals => exact Or.inl (fdec_of_head (V := []) rfl .handlerVals)
  | dropCont => exact Or.inl (fdec_of_head (V := [.cont _]) rfl .dropCont)
  | @trapSeq _ _ _ vs rest _ => exact Or.inr ⟨vs, rest, Or.inl (by simp)⟩
  | trapLabel => exact Or.inl (fdec_of_head (V := []) rfl .trapLabel)
  | trapFrame => exact Or.inl (fdec_of_head (V := []) rfl .trapFrame)
  | trapHandler => exact Or.inl (fdec_of_head (V := []) rfl .trapHandler)
  | @throwSeq _ _ _ vs a rest _ =>
    exact Or.inr ⟨vs ++ [.val (.ref (.exn a))], rest,
      Or.inr (by simp [cthrowing, FVal.toAdmin, Val.toAdmin])⟩
  | throwLabel => exact Or.inl (fdec_of_head (V := []) rfl .throwLabel)
  | throwFrame => exact Or.inl (fdec_of_head (V := []) rfl .throwFrame)
  | throwHandler => exact Or.inl (fdec_of_head (V := []) rfl .throwHandler)
  | invoke hc hf hcode hfx hn => exact Or.inl (fdec_invoke hc hf hcode hfx hn)
  | contNew hf => exact Or.inl (by
      simpa [FVal.toAdmin, Val.toAdmin] using fdec_of_head rfl (FHead.contNew (P := P) (fx := fx) hf))
  | contNewNull => exact Or.inl (by
      simpa [FVal.toAdmin, Val.toAdmin] using fdec_of_head rfl (FHead.contNewNull (P := P) (fx := fx)))
  | contBind hk => exact Or.inl (by simpa [FVal.toAdmin] using fdec_of_head rfl (FHead.contBind (P := P) (fx := fx) hk))
  | contBindNull => exact Or.inl (by
      simpa [FVal.toAdmin, Val.toAdmin] using fdec_of_head rfl (FHead.contBindNull (P := P) (fx := fx)))
  | contBindUsed hk => exact Or.inl (by simpa [FVal.toAdmin] using fdec_of_head rfl (FHead.contBindUsed (P := P) (fx := fx) hk))
  | resume hk hr => exact Or.inl (by simpa [FVal.toAdmin] using fdec_of_head rfl (FHead.resume (P := P) (fx := fx) hk hr))
  | resumeNull => exact Or.inl (by
      simpa [FVal.toAdmin, Val.toAdmin] using fdec_of_head rfl (FHead.resumeNull (P := P) (fx := fx)))
  | resumeUsed hk => exact Or.inl (by simpa [FVal.toAdmin] using fdec_of_head rfl (FHead.resumeUsed (P := P) (fx := fx) hk))
  | resumeThrow hk ht hr => exact Or.inl (by
      simpa [FVal.toAdmin, liftV_fvals] using fdec_of_head rfl (FHead.resumeThrow (P := P) (fx := fx) hk ht hr))
  | resumeThrowNull => exact Or.inl (by
      simpa [FVal.toAdmin, Val.toAdmin, liftV_fvals] using
        fdec_of_head rfl (FHead.resumeThrowNull (P := P) (fx := fx)))
  | suspend ht hE hc => exact Or.inl (fdec_of_head (V := []) rfl (.suspend ht hE hc))
  | switch hk ht hE hc => exact Or.inl (fdec_of_head (V := []) rfl (.switch hk ht hE hc))

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
