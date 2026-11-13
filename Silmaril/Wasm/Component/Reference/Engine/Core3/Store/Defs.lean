module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Extends.Defs
public import Silmaril.Wasm.Execution.Memory
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc
import Silmaril.Wasm.Component.Reference.Engine.Core3.Grows.Defs
import Silmaril.Wasm.Component.Reference.Wasm.Execution.Memory.Lemmas.Defs

/-!
# Store laws of the concrete Core 3.0 engine

The store-level fields of `CoreEngine.Lawful` (Engine/Laws.lean) for `core3 o`, stated over the
concrete functions of the engine (`SingleThreaded.allocHost`, `funcTypeE?`,
`SingleThreaded.memRead?`/`memWrite?`/`memSize?`/`memAddrType?`, `prepareE?`, `statusE`), which
are the fields of `core3 o` by definition:

* host allocation (`SingleThreaded.allocHost`, the spec's `$allocfunc` of a host function)
  appends one function instance: it grows the store (`allocHost_grows`, hence
  `allocHost_extends`), the new address was free (`allocHost_fresh`), no other function type
  changes (`allocHost_frame`), the new function has type `ofFlatType ft`
  (`allocHost_funcType`), and invoking it with `ft.params.length` flat arguments is
  immediately a callout of its host code with those arguments (`statusE_allocHost_callout`);
* memory writes (`SingleThreaded.memWrite?`) grow the store (`memWrite?_grows`,
  `memWrite?_extends`), keep every memory size and address type (`memWrite?_memSize`,
  `memWrite?_memAddrType`), satisfy read-after-write and the frame law for other memories and
  disjoint ranges (`memWrite?_read`, `memWrite?_read_other`); reads and writes succeed exactly
  in bounds (`memRead?_isSome_iff`, `memWrite?_isSome_iff`), reads have the requested length
  (`memRead?_size`), and a memory has an address type exactly when it has a size
  (`memAddrType?_isSome_iff`);
* instantiation (`prepareE?`: `$evalglobals`, then allocation of the module instance of the
  global-free residue and direct element and data segment initialisation, `instantiateOnce?`)
  grows the store (`instantiateOnce?_grows`, `prepareE?_grows`, hence `prepareE?_extends`).

No typing is assumed anywhere.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## Host allocation -/

/-- `allocHost` appends the host function instance `⟨ofFlatType ft, {}, host h⟩`. -/
theorem allocHost_eq {s s' : Store H} {ft : V1.FuncType} {h : H} {a : Nat}
    (e : SingleThreaded.allocHost s ft h = (s', a)) :
    s' = { s with funcs := s.funcs ++ [⟨SingleThreaded.ofFlatType ft, {}, .host h⟩] } ∧
      a = s.funcs.length := by
  simp only [SingleThreaded.allocHost, allocFunc, Prod.mk.injEq] at e
  exact ⟨e.1.symm, e.2.symm⟩

theorem allocHost_grows {s s' : Store H} {ft : V1.FuncType} {h : H} {a : Nat}
    (e : SingleThreaded.allocHost s ft h = (s', a)) : Grows s s' := by
  obtain ⟨rfl, -⟩ := allocHost_eq e
  exact Grows.of_prefix (List.prefix_append _ _) (List.prefix_refl _) (List.prefix_refl _)

theorem allocHost_extends {o : SingleThreaded.GrowOracle} {s s' : Store H} {ft : V1.FuncType}
    {h : H} {a : Nat} (e : SingleThreaded.allocHost s ft h = (s', a)) :
    (core3 o).Extends s s' :=
  (allocHost_grows e).extends

/-- The allocated address was not in use. -/
theorem allocHost_fresh {s s' : Store H} {ft : V1.FuncType} {h : H} {a : Nat}
    (e : SingleThreaded.allocHost s ft h = (s', a)) : funcTypeE? s a = none := by
  obtain ⟨-, rfl⟩ := allocHost_eq e
  simp [funcTypeE?]

/-- `allocHost` changes no other function type. -/
theorem allocHost_frame {s s' : Store H} {ft : V1.FuncType} {h : H} {a b : Nat}
    (e : SingleThreaded.allocHost s ft h = (s', a)) (hb : b ≠ a) :
    funcTypeE? s' b = funcTypeE? s b := by
  obtain ⟨rfl, rfl⟩ := allocHost_eq e
  unfold funcTypeE?
  rcases Nat.lt_or_ge b s.funcs.length with hlt | hge
  · rw [List.getElem?_append_left hlt]
  · rw [List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega),
      List.getElem?_eq_none hge]

theorem allocHost_funcType {s s' : Store H} {ft : V1.FuncType} {h : H} {a : Nat}
    (e : SingleThreaded.allocHost s ft h = (s', a)) :
    funcTypeE? s' a = some (SingleThreaded.ofFlatType ft) := by
  obtain ⟨rfl, rfl⟩ := allocHost_eq e
  simp [funcTypeE?]

/-- A callout of the relational status is a callout of the computable status, for any step
function: both classify the code by the same tests up to the last branch. -/
theorem statusC_callout_of_status {o : SingleThreaded.GrowOracle}
    {stepC : Config H → Option (Config H)} {s : Store H} {t : SingleThreaded.Thread} {hc : H}
    {args : List Val} (hs : SingleThreaded.status o s t = .callout hc args) :
    SingleThreaded.statusC stepC s t = .callout hc args := by
  have h1 : ¬ ∃ vs, (t.config s).code = vals vs := fun e => by
    simp [SingleThreaded.status, e] at hs
  have h2 : ¬ (t.config s).code = [.trap] := fun e => by
    simp only [SingleThreaded.status, dite_eq_right h1, ite_eq_left e] at hs
    cases hs
  have h3 : ¬ ∃ a, (t.config s).code = throwing a := fun e => by
    simp only [SingleThreaded.status, dite_eq_right h1, ite_eq_right h2, ite_eq_left e] at hs
    cases hs
  rw [statusC_of_live (fun e => h1 ((SingleThreaded.exists_vals_iff _).mpr e))
    (fun e => h2 ((SingleThreaded.isTrap?_iff _).mp e))
    (fun e => h3 ((SingleThreaded.isThrowing?_iff _).mp e))]
  have hs' : SingleThreaded.status o s t = .callout hc args := hs
  simp only [SingleThreaded.status, dite_eq_right h1, ite_eq_right h2, ite_eq_right h3] at hs'
  revert hs'
  rcases SingleThreaded.decompose? s (t.config s).code with _ | ⟨E, a, h', args'⟩
  · dsimp only
    split_ifs <;> simp
  · exact id

/-- Flat values survive the round trip through Core values. -/
theorem mapM_toFlat?_map_ofFlat :
    ∀ args : List FlatValue, (args.map SingleThreaded.ofFlat).mapM SingleThreaded.toFlat? = some args
  | [] => rfl
  | v :: args => by
    simp only [List.map_cons, List.mapM_cons, SingleThreaded.toFlat?_ofFlat,
      mapM_toFlat?_map_ofFlat args, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- Invoking an allocated host function with matching arity is immediately a callout of its host
code, with the flat arguments unchanged. -/
theorem statusE_allocHost_callout {o : SingleThreaded.GrowOracle} {s s' : Store H}
    {ft : V1.FuncType} {h : H} {a : Nat} {args : List FlatValue}
    (e : SingleThreaded.allocHost s ft h = (s', a)) (hl : args.length = ft.params.length) :
    statusE o s' (SingleThreaded.Thread.invokeFlat a args) = .callout h args := by
  have hc := SingleThreaded.allocHost_callout (o := o) s ft h (args.map SingleThreaded.ofFlat)
    (by rw [List.length_map, hl])
  rw [e] at hc
  dsimp only at hc
  unfold statusE SingleThreaded.Thread.invokeFlat
  rw [statusC_callout_of_status hc]
  dsimp only
  rw [mapM_toFlat?_map_ofFlat]

/-! ## Memory reads and writes -/

/-- A successful write replaces the bytes of the written memory by `writeBytes` of them. -/
theorem memWrite?_eq_some {s s' : Store H} {m st : Nat} {bs : ByteArray}
    (h : SingleThreaded.memWrite? s m st bs = some s') :
    ∃ mi b, s.mems[m]? = some mi ∧
      Silmaril.Wasm.Execution.Memory.writeBytes mi.bytes st bs = some b ∧
      s' = s.setMem m { mi with bytes := b } := by
  unfold SingleThreaded.memWrite? at h
  cases hm : s.mems[m]? with
  | none => simp [hm] at h
  | some mi =>
    cases hw : Silmaril.Wasm.Execution.Memory.writeBytes mi.bytes st bs with
    | none => simp [hm, hw] at h
    | some b =>
      simp only [hm, hw, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨mi, b, rfl, hw, h.symm⟩

/-- The memories after a successful write: the written one gets the new bytes, the others are
unchanged. -/
theorem memWrite?_mems {s s' : Store H} {m st : Nat} {bs : ByteArray}
    (h : SingleThreaded.memWrite? s m st bs = some s') :
    ∃ mi b, s.mems[m]? = some mi ∧
      Silmaril.Wasm.Execution.Memory.writeBytes mi.bytes st bs = some b ∧
      s'.mems[m]? = some { mi with bytes := b } ∧
      ∀ m', m' ≠ m → s'.mems[m']? = s.mems[m']? := by
  obtain ⟨mi, b, hm, hw, rfl⟩ := memWrite?_eq_some h
  refine ⟨mi, b, hm, hw, ?_, fun m' hne => ?_⟩
  · exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp hm).1
  · exact List.getElem?_set_ne (Ne.symm hne)

theorem memWrite?_grows {s s' : Store H} {m st : Nat} {bs : ByteArray}
    (h : SingleThreaded.memWrite? s m st bs = some s') : Grows s s' := by
  obtain ⟨mi, b, hm, hw, rfl⟩ := memWrite?_eq_some h
  exact Grows.setMem hm rfl (Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ hw).ge

theorem memWrite?_extends {o : SingleThreaded.GrowOracle} {s s' : Store H} {m st : Nat}
    {bs : ByteArray} (h : SingleThreaded.memWrite? s m st bs = some s') :
    (core3 o).Extends s s' :=
  (memWrite?_grows h).extends

theorem memWrite?_memSize {s s' : Store H} {m st : Nat} {bs : ByteArray}
    (h : SingleThreaded.memWrite? s m st bs = some s') (m' : Nat) :
    SingleThreaded.memSize? s' m' = SingleThreaded.memSize? s m' := by
  obtain ⟨mi, b, hm, hw, hm', hne⟩ := memWrite?_mems h
  unfold SingleThreaded.memSize?
  by_cases e : m' = m
  · subst e
    rw [hm', hm, Option.map_some, Option.map_some,
      Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ hw]
  · rw [hne m' e]

theorem memWrite?_memAddrType {s s' : Store H} {m st : Nat} {bs : ByteArray}
    (h : SingleThreaded.memWrite? s m st bs = some s') (m' : Nat) :
    SingleThreaded.memAddrType? s' m' = SingleThreaded.memAddrType? s m' := by
  obtain ⟨mi, b, hm, hw, hm', hne⟩ := memWrite?_mems h
  unfold SingleThreaded.memAddrType?
  by_cases e : m' = m
  · subst e
    rw [hm', hm, Option.map_some, Option.map_some]
  · rw [hne m' e]

/-- Read after write. -/
theorem memWrite?_read {s s' : Store H} {m st : Nat} {bs : ByteArray}
    (h : SingleThreaded.memWrite? s m st bs = some s') :
    SingleThreaded.memRead? s' m st bs.size = some bs := by
  obtain ⟨mi, b, -, hw, hm', -⟩ := memWrite?_mems h
  unfold SingleThreaded.memRead?
  rw [hm']
  simp only [Option.bind_eq_bind, Option.bind_some]
  exact Silmaril.Wasm.Execution.Memory.readBytes_writeBytes _ _ _ _ hw

/-- Frame law: reads of another memory or of a disjoint range are unchanged. -/
theorem memWrite?_read_other {s s' : Store H} {m st : Nat} {bs : ByteArray} {m' st' len : Nat}
    (h : SingleThreaded.memWrite? s m st bs = some s')
    (hd : m' ≠ m ∨ st' + len ≤ st ∨ st + bs.size ≤ st') :
    SingleThreaded.memRead? s' m' st' len = SingleThreaded.memRead? s m' st' len := by
  obtain ⟨mi, b, hm, hw, hm', hne⟩ := memWrite?_mems h
  unfold SingleThreaded.memRead?
  by_cases e : m' = m
  · subst e
    have hdis : st' + len ≤ st ∨ st + bs.size ≤ st' := hd.resolve_left (fun h => h rfl)
    rw [hm', hm]
    simp only [Option.bind_eq_bind, Option.bind_some]
    exact Silmaril.Wasm.Execution.Memory.readBytes_writeBytes_disjoint _ _ _ _ _ _ hw hdis
  · rw [hne m' e]

theorem memRead?_isSome_iff {s : Store H} {m st len : Nat} :
    (SingleThreaded.memRead? s m st len).isSome ↔
      ∃ n, SingleThreaded.memSize? s m = some n ∧ st + len ≤ n := by
  unfold SingleThreaded.memRead? SingleThreaded.memSize?
  cases s.mems[m]? with
  | none => simp
  | some mi =>
    simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some, Option.some.injEq,
      exists_eq_left', Silmaril.Wasm.Execution.Memory.readBytes]
    split <;> simp_all

theorem memRead?_size {s : Store H} {m st len : Nat} {bs : ByteArray}
    (h : SingleThreaded.memRead? s m st len = some bs) : bs.size = len := by
  unfold SingleThreaded.memRead? at h
  cases hm : s.mems[m]? with
  | none => simp [hm] at h
  | some mi =>
    rw [hm] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    exact Silmaril.Wasm.Execution.Memory.readBytes_size _ _ _ _ h

theorem memWrite?_isSome_iff {s : Store H} {m st : Nat} {bs : ByteArray} :
    (SingleThreaded.memWrite? s m st bs).isSome ↔
      ∃ n, SingleThreaded.memSize? s m = some n ∧ st + bs.size ≤ n := by
  unfold SingleThreaded.memWrite? SingleThreaded.memSize?
  cases s.mems[m]? with
  | none => simp
  | some mi =>
    simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some, Option.some.injEq,
      exists_eq_left', Silmaril.Wasm.Execution.Memory.writeBytes]
    split <;> simp_all

theorem memAddrType?_isSome_iff {s : Store H} {m : Nat} :
    (SingleThreaded.memAddrType? s m).isSome ↔ (SingleThreaded.memSize? s m).isSome := by
  unfold SingleThreaded.memAddrType? SingleThreaded.memSize?
  cases s.mems[m]? <;> rfl

/-! ## Instantiation -/

section Instantiation

variable {P : Numerics.Profile}

/-- Evaluating a constant expression grows the store. -/
theorem EvalExpr.grows {s s' : Store H} {f f' : Frame} {e : Expr} {vs : List Val}
    (h : EvalExpr P SingleThreaded.Det.noHost s f e s' f' vs) : Grows s s' :=
  Steps.grows h

theorem EvalGlobals.grows {s s' : Store H} {f f' : Frame} {gs : List Validation.CGlobalType}
    {es : List Expr} {vs : List Val}
    (h : EvalGlobals P SingleThreaded.Det.noHost s f gs es s' f' vs) : Grows s s' := by
  induction h with
  | nil => exact Grows.refl _
  | @cons _ s₁ _ _ _ _ g _ _ _ v _ he _ ih =>
    exact (EvalExpr.grows he).trans
      ((Grows.of_eq (s := s₁) (s' := (allocGlobal s₁ g v).1) rfl rfl rfl).trans ih)

theorem EvalExprs.grows {s s' : Store H} {f f' : Frame} {es : List Expr} {rs : List Ref}
    (h : EvalExprs P SingleThreaded.Det.noHost s f es s' f' rs) : Grows s s' := by
  induction h with
  | nil => exact Grows.refl _
  | cons he _ ih => exact (EvalExpr.grows he).trans ih

theorem EvalExprss.grows {s s' : Store H} {f f' : Frame} {ess : List (List Expr)}
    {rss : List (List Ref)} (h : EvalExprss P SingleThreaded.Det.noHost s f ess s' f' rss) :
    Grows s s' := by
  induction h with
  | nil => exact Grows.refl _
  | cons he _ ih => exact (EvalExprs.grows he).trans ih

/-- `$allocmodule` appends to every store component. -/
theorem allocModule?_grows {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {valsG : List Val} {refsT : List Ref} {refsE : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas valsG refsT refsE = some (s', mi)) : Grows s s' := by
  obtain ⟨_, _, _, -, -, -, -, rfl⟩ := allocModule?_inv h
  exact Grows.of_prefix (List.prefix_append _ _) (List.prefix_append _ _) (List.prefix_append _ _)

/-- Allocation (`prepare?`: initializer evaluation, then `$allocmodule`) grows the store. -/
theorem prepare?_grows {ev : Store H → Frame → Expr → Option (Store H × Val)}
    (hev : EvalSound P SingleThreaded.Det.noHost ev) {s : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H} {st : Option FuncIdx}
    (h : prepare? ev s m xas = some (c, st)) : Grows s c.store := by
  unfold prepare? at h
  split at h
  · split at h
    · cases h
    · rename_i s₁ f₁ valsG hG
      split at h
      · cases h
      · rename_i s₂ f₂ refsT hT
        split at h
        · cases h
        · rename_i s₃ f₃ refsE hE
          split at h
          · cases h
          · rename_i s₄ mi hM
            cases h
            exact (EvalGlobals.grows (evalGlobals?_sound hev hG)).trans
              ((EvalExprs.grows (evalExprs?_sound hev hT)).trans
                ((EvalExprss.grows (evalExprss?_sound hev hE)).trans (allocModule?_grows hM)))
  · cases h

end Instantiation

/-- Direct instantiation (allocation, then direct segment initialisation) grows the store. -/
theorem instantiateDirect?_grows {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {f' : Frame} {st : Option FuncIdx} (h : instantiateDirect? s m xas = some (s', f', st)) :
    Grows s s' := by
  obtain ⟨c, hp, hs⟩ := prepareDirect?_steps
    (P := SingleThreaded.profile SingleThreaded.neverFail) (host := SingleThreaded.Det.noHost)
    evalConst?_evalSound h
  exact (prepare?_grows (P := SingleThreaded.profile SingleThreaded.neverFail)
    evalConst?_evalSound hp).trans (Steps.grows hs)

/-- Instantiation with every global allocated once (`$evalglobals`, then the direct
instantiation of the global-free residue) grows the store. -/
theorem instantiateOnce?_grows {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {f' : Frame} {st : Option FuncIdx} (h : instantiateOnce? s m xas = some (s', f', st)) :
    Grows s s' := by
  unfold instantiateOnce? at h
  split at h
  · cases h
  · rename_i s₁ f₁ vs hg
    exact (EvalGlobals.grows (evalGlobals?_sound
      (P := SingleThreaded.profile SingleThreaded.neverFail) evalConst?_evalSound hg)).trans
      (instantiateDirect?_grows h)

/-- Instantiation (`$evalglobals`, then allocation and direct segment initialisation of the
residue) grows the store. -/
theorem prepareE?_grows {s s' : Store H} {m : Module} {xas : List ExternAddr} {i : ModuleInst}
    {st : Option Nat} (h : prepareE? s m xas = some (s', i, st)) : Grows s s' := by
  unfold prepareE? at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · rename_i s₁ f₁ hi
        cases h
        exact instantiateOnce?_grows hi
      · rename_i s₁ f₁ x hi
        obtain ⟨a, -, e⟩ := Option.map_eq_some_iff.mp h
        cases e
        exact instantiateOnce?_grows hi
    · cases h

theorem prepareE?_extends {o : SingleThreaded.GrowOracle} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {i : ModuleInst} {st : Option Nat}
    (h : prepareE? s m xas = some (s', i, st)) : (core3 o).Extends s s' :=
  (prepareE?_grows h).extends

end Silmaril.Wasm.Component.Engine.Core3
