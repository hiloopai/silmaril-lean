module

public import Silmaril.Proofs.Wasm.Replace.Congruence.Store

/-!
# Classification of a reduction across `Store.replaceFunc`

A step out of a store `s` is either a saturated invocation of `a` in an evaluation context
(`InvokesAt`), or it is available verbatim out of `s.replaceFunc a b`, with the final store
replaced as well (`Step.classify_replace`). The mirror image, for a step out of a replaced
store, is `Step.classify_replace_back`; its second disjunct also says that the final store is
again a replacement, which the backward simulation needs in order to continue.

Of the rules of Wasm 1.0 reduction, only two `call_indirect` rules (`callIndirect` and
`callIndirectType`) and the three invocation rules read the function table; the other two
`call_indirect` rules read the table only. The `call_indirect` rules read a type, which
`SameFuncType` keeps. The invocation rules at an address other than `a` read an instance the
replacement keeps, and at `a` they are the first disjunct. The store-writing rules write a
global or a memory, which commutes with the replacement (`replaceFunc_setGlobal`,
`replaceFunc_setMemory`), except for host calls, which `HostRespectsReplace` covers.

Ported from an earlier development `Silmaril/Wasm/Equiv/Congruence.lean`. The source's
first disjunct is named here (`InvokesAt`), so that the three congruence rules and the three
invocation rules are one line each (`InvokesAt.context`, `InvokesAt.label`, `InvokesAt.frame`,
`invokesAt_or`), and the backward proof rewrites with the store equation instead of
substituting it.
-/

@[expose] public section

namespace Silmaril.Wasm.Replace

open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1 (Instr Expr)

variable {H : Type}

/-- `X` is a saturated invocation of `a` in an evaluation context. -/
def InvokesAt (s : Store H) (a : FuncAddr) (X : List Admin) : Prop :=
  ∃ (K : EvalCtx Silmaril.Wasm.V1.Instr) (args : List Runtime.Value),
    X = K.plug value (values args ++ [.invoke a]) ∧ Saturated s a args

/-- `InvokesAt` is preserved by a value prefix and a tail. -/
theorem InvokesAt.context {s : Store H} {a : FuncAddr} {X : List Admin} (h : InvokesAt s a X)
    (vs : List Runtime.Value) (tail : List Admin) : InvokesAt s a (values vs ++ X ++ tail) := by
  obtain ⟨K, args, hX, hsat⟩ := h
  exact ⟨.seq vs K tail, args, by rw [plug_seq, hX], hsat⟩

/-- `InvokesAt` is preserved under a label. -/
theorem InvokesAt.label {s : Store H} {a : FuncAddr} {X : List Admin} (h : InvokesAt s a X)
    (n : Nat) (cont : Silmaril.Wasm.V1.Expr) : InvokesAt s a [.label n cont X] := by
  obtain ⟨K, args, hX, hsat⟩ := h
  exact ⟨.label n cont K, args, by rw [plug_label, hX], hsat⟩

/-- `InvokesAt` is preserved under a frame. -/
theorem InvokesAt.frame {s : Store H} {a : FuncAddr} {X : List Admin} (h : InvokesAt s a X)
    (n : Nat) (fr : Frame) : InvokesAt s a [.frame n fr X] := by
  obtain ⟨K, args, hX, hsat⟩ := h
  exact ⟨.frame n fr K, args, by rw [plug_frame, hX], hsat⟩

/-- An invocation of `α` at a matching arity is an invocation of `a`, or `α ≠ a`. -/
theorem invokesAt_or {s : Store H} {a α : FuncAddr} {fi : FuncInst Silmaril.Wasm.V1.Func H}
    {args : List Runtime.Value} {P : Prop} (found : s.funcs[α.value]? = some fi)
    (arity : args.length = fi.type.params.length) (h : α ≠ a → P) :
    InvokesAt s a (values args ++ [.invoke α]) ∨ P := by
  by_cases hα : α = a
  · exact .inl ⟨.hole, args, by rw [hα, plug_hole], hα ▸ ⟨fi, found, arity⟩⟩
  · exact .inr (h hα)

/-- **Classification of a reduction across the replacement.** A step is an invocation of `a`
in a context, or it is available after the replacement, final store replaced too. -/
theorem Step.classify_replace {host : HostSemantics H} {a b : FuncAddr}
    (hhost : HostRespectsReplace host a b) :
    ∀ {c c' : Config H}, Step host c c' → SameFuncType c.store a b →
      InvokesAt c.store a c.code ∨
        Step host ⟨c.store.replaceFunc a b, c.frame, c.code⟩
          ⟨c'.store.replaceFunc a b, c'.frame, c'.code⟩ := by
  intro c c' h
  induction h with
  | pure s f hp => exact fun _ => .inr (Step.pure _ f hp)
  | context _ vs tail ih => exact fun hty => (ih hty).imp (·.context vs tail) (·.context vs tail)
  | label _ n cont ih => exact fun hty => (ih hty).imp (·.label n cont) (·.label n cont)
  | frame _ n outer ih => exact fun hty => (ih hty).imp (·.frame n _) (·.frame n outer)
  | localGet s f i v found => exact fun _ => .inr (Step.localGet _ f i v found)
  | localSet s f i v old found => exact fun _ => .inr (Step.localSet _ f i v old found)
  | globalGet s f i α g index found =>
    exact fun _ => .inr (Step.globalGet _ f i α g index (by simpa using found))
  | globalSet s f i α g v index found hmut =>
    refine fun _ => .inr ?_
    rw [replaceFunc_setGlobal]
    exact Step.globalSet _ f i α g v index (by simpa using found) hmut
  | call s f i α found => exact fun _ => .inr (Step.call _ f i α found)
  | callIndirect s f i cv table α fn ft tableFound typeFound element found typeMatch =>
    intro hty
    obtain ⟨fn', hfn', hty'⟩ := exists_funcInst_replaceFunc hty found
    exact .inr (Step.callIndirect _ f i cv table α fn' ft (by simpa using tableFound)
      typeFound element hfn' (hty'.trans typeMatch))
  | callIndirectBounds s f i cv table tableFound outOfBounds =>
    exact fun _ => .inr (Step.callIndirectBounds _ f i cv table
      (by simpa using tableFound) outOfBounds)
  | callIndirectNull s f i cv table tableFound null =>
    exact fun _ => .inr (Step.callIndirectNull _ f i cv table (by simpa using tableFound) null)
  | callIndirectType s f i cv table α fn ft tableFound typeFound element found typeMismatch =>
    intro hty
    obtain ⟨fn', hfn', hty'⟩ := exists_funcInst_replaceFunc hty found
    exact .inr (Step.callIndirectType _ f i cv table α fn' ft (by simpa using tableFound)
      typeFound element hfn' (by rw [hty']; exact typeMismatch))
  | invokeWasm s f α ft module fn args found arity resultArity =>
    exact fun _ => invokesAt_or found arity fun hα => Step.invokeWasm _ f α ft module fn args
      (by rw [getElem?_replaceFunc_of_ne' hα]; exact found) arity resultArity
  | invokeHost s s' f α ft fn args r found arity behavior =>
    exact fun _ => invokesAt_or found arity fun hα => Step.invokeHost _ _ f α ft fn args r
      (by rw [getElem?_replaceFunc_of_ne' hα]; exact found) arity
      (hhost.forward fn s s' args r behavior)
  | invokeHostDiverges s f α ft fn args found arity behavior =>
    exact fun _ => invokesAt_or found arity fun hα => Step.invokeHostDiverges _ f α ft fn args
      (by rw [getElem?_replaceFunc_of_ne' hα]; exact found) arity
      ((hhost.diverges fn s args).mp behavior)
  | intLoad s f t packed arg cv α m v memory loaded =>
    exact fun _ => .inr (Step.intLoad _ f t packed arg cv α m v (by simpa using memory) loaded)
  | intLoadTrap s f t packed arg cv α m memory loaded =>
    exact fun _ => .inr (Step.intLoadTrap _ f t packed arg cv α m (by simpa using memory) loaded)
  | floatLoad s f t arg cv α m v memory loaded =>
    exact fun _ => .inr (Step.floatLoad _ f t arg cv α m v (by simpa using memory) loaded)
  | floatLoadTrap s f t arg cv α m memory loaded =>
    exact fun _ => .inr (Step.floatLoadTrap _ f t arg cv α m (by simpa using memory) loaded)
  | intStore s f t packed arg cv x α m bytes memory stored =>
    refine fun _ => .inr ?_
    rw [replaceFunc_setMemory]
    exact Step.intStore _ f t packed arg cv x α m bytes (by simpa using memory) stored
  | intStoreTrap s f t packed arg cv x α m memory stored =>
    exact fun _ => .inr (Step.intStoreTrap _ f t packed arg cv x α m
      (by simpa using memory) stored)
  | floatStore s f t arg cv x α m bytes memory stored =>
    refine fun _ => .inr ?_
    rw [replaceFunc_setMemory]
    exact Step.floatStore _ f t arg cv x α m bytes (by simpa using memory) stored
  | floatStoreTrap s f t arg cv x α m memory stored =>
    exact fun _ => .inr (Step.floatStoreTrap _ f t arg cv x α m (by simpa using memory) stored)
  | memorySize s f α m memory =>
    exact fun _ => .inr (Step.memorySize _ f α m (by simpa using memory))
  | memoryGrow s f α m cv r bytes memory grown =>
    refine fun _ => .inr ?_
    rw [replaceFunc_setMemory]
    exact Step.memoryGrow _ f α m cv r bytes (by simpa using memory) grown

/-- **Classification of a reduction out of a replaced store.** A step out of
`s.replaceFunc a b` is an invocation of `a` in a context, or it comes from a step out of `s`
whose final store is again a replacement. -/
theorem Step.classify_replace_back {host : HostSemantics H} {a b : FuncAddr}
    (hhost : HostRespectsReplace host a b) :
    ∀ {c c' : Config H}, Step host c c' → ∀ s : Store H, c.store = s.replaceFunc a b →
      SameFuncType s a b →
      InvokesAt c.store a c.code ∨
        ∃ s' : Store H, c'.store = s'.replaceFunc a b ∧
          Step host ⟨s, c.frame, c.code⟩ ⟨s', c'.frame, c'.code⟩ := by
  intro c c' h
  induction h with
  | pure σ f hp => exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.pure s f hp⟩
  | context _ vs tail ih =>
    exact fun s hσ hty => (ih s hσ hty).imp (·.context vs tail)
      fun ⟨s', hs', hstep⟩ => ⟨s', hs', hstep.context vs tail⟩
  | label _ n cont ih =>
    exact fun s hσ hty => (ih s hσ hty).imp (·.label n cont)
      fun ⟨s', hs', hstep⟩ => ⟨s', hs', hstep.label n cont⟩
  | frame _ n outer ih =>
    exact fun s hσ hty => (ih s hσ hty).imp (·.frame n _)
      fun ⟨s', hs', hstep⟩ => ⟨s', hs', hstep.frame n outer⟩
  | localGet σ f i v found =>
    exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.localGet s f i v found⟩
  | localSet σ f i v old found =>
    exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.localSet s f i v old found⟩
  | globalGet σ f i α g index found =>
    exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.globalGet s f i α g index
      (by simpa [hσ] using found)⟩
  | globalSet σ f i α g v index found hmut =>
    exact fun s (hσ : σ = _) _ => .inr ⟨setGlobal s α {g with value := v},
      by rw [hσ, replaceFunc_setGlobal],
      Step.globalSet s f i α g v index (by simpa [hσ] using found) hmut⟩
  | call σ f i α found => exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.call s f i α found⟩
  | callIndirect σ f i cv table α fn ft tableFound typeFound element found typeMatch =>
    intro s (hσ : σ = _) hty
    obtain ⟨fn', hfn', hty'⟩ := exists_funcInst_of_replaceFunc hty (hσ ▸ found)
    exact .inr ⟨s, hσ, Step.callIndirect s f i cv table α fn' ft
      (by simpa [hσ] using tableFound) typeFound element hfn' (hty'.trans typeMatch)⟩
  | callIndirectBounds σ f i cv table tableFound outOfBounds =>
    exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.callIndirectBounds s f i cv table
      (by simpa [hσ] using tableFound) outOfBounds⟩
  | callIndirectNull σ f i cv table tableFound null =>
    exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.callIndirectNull s f i cv table
      (by simpa [hσ] using tableFound) null⟩
  | callIndirectType σ f i cv table α fn ft tableFound typeFound element found typeMismatch =>
    intro s (hσ : σ = _) hty
    obtain ⟨fn', hfn', hty'⟩ := exists_funcInst_of_replaceFunc hty (hσ ▸ found)
    exact .inr ⟨s, hσ, Step.callIndirectType s f i cv table α fn' ft
      (by simpa [hσ] using tableFound) typeFound element hfn' (by rw [hty']; exact typeMismatch)⟩
  | invokeWasm σ f α ft module fn args found arity resultArity =>
    exact fun s (hσ : σ = _) _ => invokesAt_or found arity fun hα => ⟨s, hσ,
      Step.invokeWasm s f α ft module fn args
        (by rw [← getElem?_replaceFunc_of_ne' (b := b) hα, ← hσ]; exact found) arity resultArity⟩
  | invokeHost σ σ' f α ft fn args r found arity behavior =>
    intro s (hσ : σ = _) _
    refine invokesAt_or found arity fun hα => ?_
    obtain ⟨t, ht, hbeh⟩ := hhost.backward fn s σ' args r (hσ ▸ behavior)
    exact ⟨t, ht, Step.invokeHost s t f α ft fn args r
      (by rw [← getElem?_replaceFunc_of_ne' (b := b) hα, ← hσ]; exact found) arity hbeh⟩
  | invokeHostDiverges σ f α ft fn args found arity behavior =>
    exact fun s (hσ : σ = _) _ => invokesAt_or found arity fun hα => ⟨s, hσ,
      Step.invokeHostDiverges s f α ft fn args
        (by rw [← getElem?_replaceFunc_of_ne' (b := b) hα, ← hσ]; exact found) arity
        ((hhost.diverges fn s args).mpr (hσ ▸ behavior))⟩
  | intLoad σ f t packed arg cv α m v memory loaded =>
    exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.intLoad s f t packed arg cv α m v
      (by simpa [hσ] using memory) loaded⟩
  | intLoadTrap σ f t packed arg cv α m memory loaded =>
    exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.intLoadTrap s f t packed arg cv α m
      (by simpa [hσ] using memory) loaded⟩
  | floatLoad σ f t arg cv α m v memory loaded =>
    exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.floatLoad s f t arg cv α m v
      (by simpa [hσ] using memory) loaded⟩
  | floatLoadTrap σ f t arg cv α m memory loaded =>
    exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.floatLoadTrap s f t arg cv α m
      (by simpa [hσ] using memory) loaded⟩
  | intStore σ f t packed arg cv x α m bytes memory stored =>
    exact fun s (hσ : σ = _) _ => .inr ⟨setMemory s α {m with data := bytes},
      by rw [hσ, replaceFunc_setMemory],
      Step.intStore s f t packed arg cv x α m bytes (by simpa [hσ] using memory) stored⟩
  | intStoreTrap σ f t packed arg cv x α m memory stored =>
    exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.intStoreTrap s f t packed arg cv x α m
      (by simpa [hσ] using memory) stored⟩
  | floatStore σ f t arg cv x α m bytes memory stored =>
    exact fun s (hσ : σ = _) _ => .inr ⟨setMemory s α {m with data := bytes},
      by rw [hσ, replaceFunc_setMemory],
      Step.floatStore s f t arg cv x α m bytes (by simpa [hσ] using memory) stored⟩
  | floatStoreTrap σ f t arg cv x α m memory stored =>
    exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.floatStoreTrap s f t arg cv x α m
      (by simpa [hσ] using memory) stored⟩
  | memorySize σ f α m memory =>
    exact fun s (hσ : σ = _) _ => .inr ⟨s, hσ, Step.memorySize s f α m (by simpa [hσ] using memory)⟩
  | memoryGrow σ f α m cv r bytes memory grown =>
    exact fun s (hσ : σ = _) _ => .inr ⟨setMemory s α {m with data := bytes},
      by rw [hσ, replaceFunc_setMemory],
      Step.memoryGrow s f α m cv r bytes (by simpa [hσ] using memory) grown⟩

end Silmaril.Wasm.Replace
