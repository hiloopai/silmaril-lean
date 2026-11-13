module

public import Silmaril.Wasm.Spec.Temporal.Thms

@[expose] public section

/-!
# Embedding the simple logics into the temporal ones

Logic maps (hence model-expansive comorphisms of the Wasm institutions, `LogicMap.coHom`, along
which entailment is borrowed):

```
neverCall ─┐
callPre ───┤                 ┌─→ ltlFin   (□ A)
neverCallFrom ┼─→ act ───────┼─→ ltlMax   (□ A, on good sets)
retPost ───┤                 ├─→ ctl      (AG of the invariant)
assertNeverFalse → callPre   └─→ tla      (□[A])
```

* `NeverCall.toAct`, `CallPre.toAct`, `NeverCallFrom.toAct`, `RetPost.toAct`,
  `AssertNeverFalse.toAct`: each simple property as an action invariant;
  `Basic.toAct`: their sum, by copairing.
* `Act.toLtlFin`, `Act.toLtlMax`, `Act.toCtl`, `Act.toTla`.
* `Basic.toLtlFin`, `Basic.toLtlMax`, `Basic.toCtl`, `Basic.toTla`: the composites.
* `Joint.toLtlFin`: the join `basic ⊕ ltlFin` of the simple logics and LTL maps into LTL (the
  sum's copairing of `Basic.toLtlFin` and the identity): specifications mixing both are LTL
  specifications.
-/

namespace Silmaril.Wasm.Spec

variable {Ty A R : Type}

/-- "Never called" as an action invariant. -/
def NeverCall.toAct (Ty A R : Type) : LogicMap (neverCall Ty A R) (act Ty A R) :=
  LogicMap.ofTrace (fun i _ e => ∀ a, e ≠ Event.icall i a) fun i t => by
    rw [everyPos_iff_mem]
    exact ⟨fun h a ha => h _ ha a rfl, fun h e he a hea => h a (hea ▸ he)⟩

/-- A call precondition as an action invariant. -/
def CallPre.toAct (Ty A R : Type) : LogicMap (callPre Ty A R) (act Ty A R) :=
  LogicMap.ofTrace (fun φ _ e => ∀ a, e = Event.icall φ.imp a → φ.pre a) fun φ t => by
    rw [everyPos_iff_mem]
    exact ⟨fun h a ha => h _ ha a rfl, fun h e he a hea => h a (hea ▸ he)⟩

/-- "Never called from `e`" as an action invariant (by definition). -/
def NeverCallFrom.toAct (Ty A R : Type) : LogicMap (neverCallFrom Ty A R) (act Ty A R) :=
  LogicMap.ofTrace (fun φ h ev => ∀ a, ev = Event.icall φ.1 a → activeExport h ≠ some φ.2)
    fun _ _ => Iff.rfl

/-- A return postcondition as an action invariant. -/
def RetPost.toAct (Ty A R : Type) : LogicMap (retPost Ty A R) (act Ty A R) :=
  LogicMap.ofTrace (fun φ _ e => ∀ r, e = Event.ret φ.exp r → φ.post r) fun φ t => by
    rw [everyPos_iff_mem]
    exact ⟨fun h r hr => h _ hr r rfl, fun h e he r her => h r (her ▸ he)⟩

/-- "Assert never false" as an action invariant. -/
def AssertNeverFalse.toAct (Ty R : Type) :
    LogicMap (assertNeverFalse Ty R) (act Ty (List Silmaril.Wasm.Execution.Core.Val) R) :=
  (AssertNeverFalse.toCallPre Ty R).comp (CallPre.toAct _ _ _)

/-- The simple logics, joined, as action invariants. -/
def Basic.toAct (Ty A R : Type) : LogicMap (basic Ty A R) (act Ty A R) :=
  (((NeverCall.toAct Ty A R).copair (CallPre.toAct Ty A R)).copair
    (NeverCallFrom.toAct Ty A R)).copair (RetPost.toAct Ty A R)

/-- `A` as `□ A` in finite-trace LTL. -/
def Act.toLtlFin (Ty A R : Type) : LogicMap (act Ty A R) (ltlFin Ty A R) :=
  ⟨fun p => LTL.alw (LTL.atom p), fun T _ p => ltlFin_alw_atom_iff T p⟩

/-- `A` as `□ A` in maximal-behaviour LTL. -/
def Act.toLtlMax (Ty A R : Type) : LogicMap (act Ty A R) (ltlMax Ty A R) :=
  ⟨fun p => LTL.alw (LTL.atom p), fun _ hG p => ltlMax_alw_atom_iff hG p⟩

/-- `A` as `AG` of the invariant in CTL. -/
def Act.toCtl (Ty A R : Type) : LogicMap (act Ty A R) (ctl Ty A R) :=
  ⟨fun p => CTL.ag (CTL.atom (EveryPos p)), fun T _ p => by
    show (∀ u, [] ++ u ∈ T → EveryPos p ([] ++ u)) ↔ ∀ t ∈ T, EveryPos p t
    simp only [List.nil_append]⟩

/-- `A` as `□[A]` in TLA. -/
def Act.toTla (Ty A R : Type) : LogicMap (act Ty A R) (tla Ty A R) :=
  ⟨fun p => TLA.box p, fun _ _ _ => Iff.rfl⟩

/-- The simple logics in finite-trace LTL. -/
def Basic.toLtlFin (Ty A R : Type) : LogicMap (basic Ty A R) (ltlFin Ty A R) :=
  (Basic.toAct Ty A R).comp (Act.toLtlFin Ty A R)

/-- The simple logics in maximal-behaviour LTL. -/
def Basic.toLtlMax (Ty A R : Type) : LogicMap (basic Ty A R) (ltlMax Ty A R) :=
  (Basic.toAct Ty A R).comp (Act.toLtlMax Ty A R)

/-- The simple logics in CTL. -/
def Basic.toCtl (Ty A R : Type) : LogicMap (basic Ty A R) (ctl Ty A R) :=
  (Basic.toAct Ty A R).comp (Act.toCtl Ty A R)

/-- The simple logics in TLA. -/
def Basic.toTla (Ty A R : Type) : LogicMap (basic Ty A R) (tla Ty A R) :=
  (Basic.toAct Ty A R).comp (Act.toTla Ty A R)

/-- The join of the simple logics and finite-trace LTL is finite-trace LTL. -/
def Joint.toLtlFin (Ty A R : Type) : LogicMap ((basic Ty A R).sum (ltlFin Ty A R)) (ltlFin Ty A R) :=
  (Basic.toLtlFin Ty A R).copair (LogicMap.id _)

end Silmaril.Wasm.Spec
