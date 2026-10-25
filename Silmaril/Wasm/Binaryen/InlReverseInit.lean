module

public import Silmaril.Wasm.Binaryen.InlProfileInit
public import Silmaril.Wasm.SingleThreaded.HeadInversion

@[expose] public section

/-! # Forced normalization after entering an inlined activation

The selected transformed block entry fixes its result arity and argument list.
Its parameter stores and local initialization then have a uniquely forced finite
path to the ordinary caller-mode relation. The endpoint may immediately perform
nondeterministic computation; no terminal-state or deterministic-profile premise
is used here.
-/

namespace Silmaril.Wasm.Binaryen.GrowWrapper.Forced

open Silmaril.Wasm.Execution.Core

/-- Concatenate forced administrative prefixes without requiring a terminal
endpoint. -/
theorem trans {H : Type} {P : Numerics.Profile} {a b c : Config H}
    (first : GrowWrapper.Forced (P := P) a b)
    (second : GrowWrapper.Forced (P := P) b c) :
    GrowWrapper.Forced (P := P) a c := by
  induction first with
  | done => exact second
  | step step unique _ ih => exact .step step unique (ih second)

end Silmaril.Wasm.Binaryen.GrowWrapper.Forced

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- Normalize the actual parameter/local initialization to the exact callee
frame layout. This accepts any store, including one with live mutable state, and
any old values in the caller's added-local suffix. -/
theorem activation_initializes (hok : PrmOk p) (hC : PrmC p)
    (t : Store H) (fo : Frame) (E : List (Option Val))
    (hl : fo.locals.length = p.base) (he : E.length = p.ext)
    {args : List Val} {ps rs : Ty (.list .val)}
    (he' : Expand p.df (.func ps rs)) (hn : args.length = ps.length) :
    Initialization
      ⟨t, ⟨fo.locals ++ E, p.mi⟩,
        [.label rs.toList.length [] (vals args ++ expression p.SBL)]⟩
      ⟨t, ⟨fo.locals ++ (Frame.forCall p.mi args p.cf.locals).locals, p.mi⟩,
        [.label rs.toList.length [] (expression (InlineTy.xformL p.base 0 p.cf.body))]⟩ ∧
    (Frame.forCall p.mi args p.cf.locals).locals.length = p.ext := by
  have hnp := hC.np_eq ps rs he'
  have hext := hC.ext_eq
  have hbound := hok.bound
  have hnv : args.length = hC.np := by rw [← hnp]; exact hn
  set xs : List LocalIdx := (List.range hC.np).map fun j => lidx (p.base + j) with hxs
  set xz : List LocalIdx := (List.range hC.nl).map fun j => lidx (p.base + hC.np + j) with hxz
  set R : List Admin := expression (zerosI hC.zs xz) ++
    expression (InlineTy.xformL p.base 0 p.cf.body) with hR
  have hcode : vals args ++ expression p.SBL =
      vals args ++ expression (xs.reverse.map .localSet) ++ R := by
    rw [hC.SBL_eq, ← hxs, ← hxz, hR]
    simp only [expression, List.map_append, List.append_assoc]
  obtain ⟨fl₁, hs₁, hlen₁, hmid₁, hout₁⟩ := sets_initializes
    (s := t) (M := p.mi) (k := rs.toList.length) (base := p.base)
    (R := R) args xs (fo.locals ++ E) (by simp [hxs, hnv])
    (fun j x hx => getElem?_range_map_lidx (by omega) hx)
    (fun j hj => by simp [hxs] at hj; simp; omega)
  obtain ⟨fl₂, hs₂, hlen₂, hmid₂, hout₂⟩ := zeros_initializes
    (s := t) (M := p.mi) (k := rs.toList.length)
    (R := expression (InlineTy.xformL p.base 0 p.cf.body)) hC.zs hC.zvs xz fl₁
    (p.base + hC.np) (by simp [hxz, hC.zs_len]) hC.zs_val
    (fun j x hx => getElem?_range_map_lidx (by omega) hx)
    (fun j hj => by simp [hxz] at hj; rw [hlen₁]; simp; omega)
  -- the callee frame
  set F := Frame.forCall p.mi args p.cf.locals with hF
  have hFl : F.locals = args.map some ++ hC.zvs.map some := by
    simp only [hF, Frame.forCall]
    rw [hC.defaults]
  have hzl : hC.zvs.length = hC.nl := by
    rw [← hC.zs_len]; exact (List.Forall₂.length_eq hC.zs_val).symm
  have hfl₂ : fl₂ = fo.locals ++ F.locals := by
    apply List.ext_getElem?
    intro i
    rw [hFl]
    have hl₁ : fl₁.length = p.base + p.ext := by rw [hlen₁]; simp [hl, he]
    by_cases h1 : i < p.base
    · rw [hout₂ i (.inl (by omega)), hout₁ i (.inl h1), List.getElem?_append_left (by omega),
        List.getElem?_append_left (by omega)]
    · by_cases h2 : i < p.base + hC.np
      · have h' := hmid₁ (i - p.base) (by omega)
        have ei : p.base + (i - p.base) = i := by omega
        rw [ei] at h'
        have hj : i - p.base < args.length := by omega
        rw [hout₂ i (.inl h2), h', List.getElem?_append_right (by omega), hl,
          List.getElem?_append_left (by simp; omega), List.getElem?_map,
          List.getElem?_eq_getElem hj]
        rfl
      · by_cases h3 : i < p.base + hC.np + hC.nl
        · have h' := hmid₂ (i - (p.base + hC.np)) (by omega)
          have ei : p.base + hC.np + (i - (p.base + hC.np)) = i := by omega
          rw [ei] at h'
          have hj : i - (p.base + hC.np) < hC.zvs.length := by omega
          have ei2 : i - p.base - (args.map some).length = i - (p.base + hC.np) := by
            simp [hnv]; omega
          rw [h', List.getElem?_append_right (by omega), hl,
            List.getElem?_append_right (by simp; omega), ei2, List.getElem?_map,
            List.getElem?_eq_getElem hj]
          rfl
        · have hn₂ : fl₂.length ≤ i := by rw [hlen₂, hl₁]; omega
          have hn₃ : (fo.locals ++ (args.map some ++ hC.zvs.map some)).length ≤ i := by
            simp only [List.length_append, List.length_map, hl, hnv, hzl]; omega
          rw [List.getElem?_eq_none hn₂, List.getElem?_eq_none hn₃]
  constructor
  · rw [← hfl₂]
    rw [hcode]
    exact hs₁.trans (by simpa [hR] using hs₂)
  · rw [hFl]
    simp [hnv, hzl, hext]

/-- Forced-prefix projection of the stronger, context-stable initialization path. -/
theorem activation_forced (hok : PrmOk p) (hC : PrmC p)
    (t : Store H) (fo : Frame) (E : List (Option Val))
    (hl : fo.locals.length = p.base) (he : E.length = p.ext)
    {args : List Val} {ps rs : Ty (.list .val)}
    (he' : Expand p.df (.func ps rs)) (hn : args.length = ps.length) :
    GrowWrapper.Forced (P := P)
      ⟨t, ⟨fo.locals ++ E, p.mi⟩,
        [.label rs.toList.length [] (vals args ++ expression p.SBL)]⟩
      ⟨t, ⟨fo.locals ++ (Frame.forCall p.mi args p.cf.locals).locals, p.mi⟩,
        [.label rs.toList.length [] (expression (InlineTy.xformL p.base 0 p.cf.body))]⟩ ∧
    (Frame.forCall p.mi args p.cf.locals).locals.length = p.ext := by
  obtain ⟨initializes, length⟩ := activation_initializes hok hC t fo E hl he he' hn
  exact ⟨initializes.forced, length⟩

/-- Normalize the selected block initialization under actual outer values and
following code, preserving every uniquely forced local write. -/
theorem activation_forced_context (hok : PrmOk p) (hC : PrmC p)
    (t : Store H) (fo : Frame) (E : List (Option Val))
    (hl : fo.locals.length = p.base) (he : E.length = p.ext)
    {args : List Val} {ps rs : Ty (.list .val)}
    (expanded : Expand p.df (.func ps rs)) (arity : args.length = ps.length)
    (outerValues : List Val) (rest : List Admin) :
    GrowWrapper.Forced (P := P)
      ⟨t, ⟨fo.locals ++ E, p.mi⟩,
        vals outerValues ++ [.label rs.toList.length [] (vals args ++ expression p.SBL)] ++ rest⟩
      ⟨t, ⟨fo.locals ++ (Frame.forCall p.mi args p.cf.locals).locals, p.mi⟩,
        vals outerValues ++
          [.label rs.toList.length [] (expression (InlineTy.xformL p.base 0 p.cf.body))] ++ rest⟩ := by
  exact ((activation_initializes hok hC t fo E hl he expanded arity).1.context outerValues rest).forced

/-- Reverse the chosen entry into the actual inlined block. The source enters
its original callee; the selected target state then normalizes by uniquely forced
parameter/local initialization to the ordinary caller-mode relation. -/
theorem reverse_site_block_head_initializes (hok : PrmOk p) (hC : PrmC p)
    {s t : Store H} {fo : Frame} {E : List (Option Val)}
    (hm : fo.module = p.mi) (hl : fo.locals.length = p.base) (he : E.length = p.ext)
    {args : List Val} {next : Config H} (related : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args
      (.plain (.block (.typeIdx p.ty) p.SBL)) next) :
    ∃ originalNext normalized : Config H,
      Det.Head P s fo (args ++ [.ref (.func p.af)]) (.callRefType p.df) originalNext ∧
      Initialization next normalized ∧
      MR p .g originalNext normalized ∧ SR p originalNext.store normalized.store := by
  obtain ⟨argTypes, resultTypes, blockType, arity, rfl⟩ := head_block selected
  change (p.mi.types[p.ty.toNat]? >>= DefType.funcType?) = some (argTypes, resultTypes) at blockType
  rw [hC.ty_eq] at blockType
  change DefType.funcType? p.df = some (argTypes, resultTypes) at blockType
  unfold DefType.funcType? at blockType
  split at blockType
  · rename_i ps rs expanded
    simp only [Option.some.injEq, Prod.mk.injEq] at blockType
    obtain ⟨rfl, rfl⟩ := blockType
    have expanded' : Expand p.df (.func ps rs) := Expand.iff.mpr expanded
    have arity' : args.length = ps.length := arity
    obtain ⟨initializes, localsLength⟩ := activation_initializes hok hC t fo E hl he expanded' arity'
    refine ⟨_, _, Det.Head.callRefFunc rfl trivial related.hf expanded' arity' rfl,
      initializes, ?_, related⟩
    refine ⟨hm, hl, (Frame.forCall p.mi args p.cf.locals).locals, localsLength, rfl, ?_⟩
    exact .head (.site rfl rfl (.a (LI.of_xformL hC.ret))) .nil
  · simp at blockType

/-- The direct source call needs only its fetch and activation reductions to
match the selected transformed block entry and its forced initialization. -/
theorem reverse_site_call_block_head_initializes (hok : PrmOk p) (hC : PrmC p)
    (functionIndex : p.mi.funcs[p.fx.toNat]? = some p.af)
    {s t : Store H} {fo : Frame} {E : List (Option Val)}
    (hm : fo.module = p.mi) (hl : fo.locals.length = p.base) (he : E.length = p.ext)
    {args : List Val} {next : Config H} (related : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args
      (.plain (.block (.typeIdx p.ty) p.SBL)) next) :
    ∃ originalNext normalized : Config H,
      Relation.TransGen (Step P Det.noHost)
        ⟨s, fo, vals args ++ [.plain (.call p.fx)]⟩ originalNext ∧
      Initialization next normalized ∧
      MR p .g originalNext normalized ∧ SR p originalNext.store normalized.store := by
  obtain ⟨originalNext, normalized, enters, initializes, runtime, stores⟩ :=
    reverse_site_block_head_initializes hok hC hm hl he related selected
  have lookup : fo.module.funcs[p.fx.toNat]? = some p.af := by rw [hm]; exact functionIndex
  have fetch := Execution.Core.Sim.Step.vals_left (Det.Head.call (P := P) lookup related.hf).toStep args
  have fetch' : Step P Det.noHost ⟨s, fo, vals args ++ [.plain (.call p.fx)]⟩
      ⟨s, fo, vals (args ++ [.ref (.func p.af)]) ++ [.callRefType p.df]⟩ := by
    simpa [fO, vals, Val.toAdmin, List.map_append, List.append_assoc] using fetch
  exact ⟨originalNext, normalized, .head fetch' (.single enters.toStep),
    initializes, runtime, stores⟩

/-- Existing forced-prefix interface, projected only after the complete
context-stable site initialization has been retained. -/
theorem reverse_site_block_head (hok : PrmOk p) (hC : PrmC p)
    {s t : Store H} {fo : Frame} {E : List (Option Val)}
    (hm : fo.module = p.mi) (hl : fo.locals.length = p.base) (he : E.length = p.ext)
    {args : List Val} {next : Config H} (related : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args
      (.plain (.block (.typeIdx p.ty) p.SBL)) next) :
    ∃ originalNext normalized : Config H,
      Det.Head P s fo (args ++ [.ref (.func p.af)]) (.callRefType p.df) originalNext ∧
      GrowWrapper.Forced (P := P) next normalized ∧
      MR p .g originalNext normalized ∧ SR p originalNext.store normalized.store := by
  obtain ⟨originalNext, normalized, enters, initializes, runtime, stores⟩ :=
    reverse_site_block_head_initializes hok hC hm hl he related selected
  exact ⟨originalNext, normalized, enters, initializes.forced, runtime, stores⟩

/-- Existing direct-call interface, retaining its actual two source reductions. -/
theorem reverse_site_call_block_head (hok : PrmOk p) (hC : PrmC p)
    (functionIndex : p.mi.funcs[p.fx.toNat]? = some p.af)
    {s t : Store H} {fo : Frame} {E : List (Option Val)}
    (hm : fo.module = p.mi) (hl : fo.locals.length = p.base) (he : E.length = p.ext)
    {args : List Val} {next : Config H} (related : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args
      (.plain (.block (.typeIdx p.ty) p.SBL)) next) :
    ∃ originalNext normalized : Config H,
      Relation.TransGen (Step P Det.noHost)
        ⟨s, fo, vals args ++ [.plain (.call p.fx)]⟩ originalNext ∧
      GrowWrapper.Forced (P := P) next normalized ∧
      MR p .g originalNext normalized ∧ SR p originalNext.store normalized.store := by
  obtain ⟨originalNext, normalized, enters, initializes, runtime, stores⟩ :=
    reverse_site_call_block_head_initializes hok hC functionIndex hm hl he related selected
  exact ⟨originalNext, normalized, enters, initializes.forced, runtime, stores⟩

end Silmaril.Wasm.Binaryen.InlR
