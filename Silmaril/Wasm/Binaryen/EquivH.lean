module

public import Silmaril.Wasm.Binaryen.Equiv
public import Silmaril.Wasm.Binaryen.HostCode

@[expose] public section

/-! # Contextual refinement over a chosen class of hosts

`SeqRefines` quantifies over every `HostRespectsCode` host. That class contains
hosts which return ill-typed stores (`JoinableHostCex.corruptHost`), so a rewrite
that is only correct on well-typed configurations (a `local.get` operand, an `if`
on a global) is not a `SeqRefines` rewrite. Conversely the code-simulation tooling
(`Execution/Core/Sim`) works for every `Sim.HostParametric` host, a class that
contains every `HostRespectsCode` host (`HostRespectsCode.hostParametric`).

`SeqRefinesH Q` is `SeqRefines` with the host class `Q` as a parameter:

* `HostsRC`: `SeqRefinesH HostsRC = SeqRefines` (`seqRefinesH_rc_iff`);
* `HostsP` (code-parametric hosts): untyped rewrites (DCE, constant folding) are
  proved here; they give `SeqRefines` by `SeqRefinesH.toSeqRefines`;
* `HostsSafe` (typed and code-parametric hosts): typed rewrites (peephole,
  vacuum) are proved here; `closedHost` belongs to it at every `H`.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

/-- A class of hosts, at every host-state type. -/
abbrev HostClass : Type 1 := (H : Type) → HostSemantics H → Prop

/-- The hosts of `SeqRefines`. -/
abbrev HostsRC : HostClass := fun _ host => HostRespectsCode host

/-- Code-parametric hosts: the class of the code-simulation tooling. -/
abbrev HostsP : HostClass := fun _ host => Sim.HostParametric host

/-- Typed, code-parametric hosts (`HostCodeSafe`). -/
abbrev HostsSafe : HostClass := fun _ host => HostCodeSafe host

theorem hostsRC_le_hostsP {H : Type} {host : HostSemantics H} (h : HostsRC H host) :
    HostsP H host :=
  HostRespectsCode.hostParametric h

theorem hostsSafe_le_hostsP {H : Type} {host : HostSemantics H} (h : HostsSafe H host) :
    HostsP H host :=
  h.2

/-- **Contextual refinement of sequences over the host class `Q`.** As
`SeqRefines`, with `Q` in place of `HostRespectsCode`. -/
def SeqRefinesH (Q : HostClass) (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (C : Context) (it : InstrType) (es es' : List BExpr) : Prop :=
  SeqOk C es it ∧ SeqOk C es' it ∧
  ∀ {H : Type} (host : HostSemantics H) (m : BModule) (g : Nat) (K : BCtx),
    Q H host →
    (m.withBody g (K.plug es)).Ok → (m.withBody g (K.plug es')).Ok →
    ExportRefines R P host (m.withBody g (K.plug es)).lower (m.withBody g (K.plug es')).lower

/-- Contextual equivalence over the host class `Q`: refinement both ways. -/
def SeqEquivH (Q : HostClass) (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (C : Context) (it : InstrType) (es es' : List BExpr) : Prop :=
  SeqRefinesH Q R P C it es es' ∧ SeqRefinesH Q (fun b b' => R b' b) P C it es' es

theorem seqRefinesH_rc_iff {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    {C : Context} {it : InstrType} {es es' : List BExpr} :
    SeqRefinesH HostsRC R P C it es es' ↔ SeqRefines R P C it es es' :=
  Iff.rfl

namespace SeqRefinesH

variable {Q Q' : HostClass} {R R' : Behaviour Val → Behaviour Val → Prop} {P : Profile}
  {C : Context} {it : InstrType}

/-- Fewer hosts, weaker refinement. -/
theorem mono_host (hQ : ∀ (H : Type) (host : HostSemantics H), Q' H host → Q H host)
    {es es' : List BExpr} (h : SeqRefinesH Q R P C it es es') : SeqRefinesH Q' R P C it es es' :=
  ⟨h.1, h.2.1, fun host m g K hh h₁ h₂ => h.2.2 host m g K (hQ _ host hh) h₁ h₂⟩

/-- A refinement for every code-parametric host is a `SeqRefines`. -/
theorem toSeqRefines {es es' : List BExpr} (h : SeqRefinesH HostsP R P C it es es') :
    SeqRefines R P C it es es' :=
  (mono_host (fun _ _ hh => hostsRC_le_hostsP hh) h : SeqRefinesH HostsRC R P C it es es')

/-- A refinement for every code-parametric host holds for every typed one. -/
theorem toSafe {es es' : List BExpr} (h : SeqRefinesH HostsP R P C it es es') :
    SeqRefinesH HostsSafe R P C it es es' :=
  mono_host (fun _ _ hh => hostsSafe_le_hostsP hh) h

/-- **Congruence, by definition.** -/
theorem congr {es es' : List BExpr} (h : SeqRefinesH Q R P C it es es') (K : BCtx)
    {C' : Context} {it' : InstrType} (hK : SeqOk C' (K.plug es) it')
    (hK' : SeqOk C' (K.plug es') it') :
    SeqRefinesH Q R P C' it' (K.plug es) (K.plug es') := by
  refine ⟨hK, hK', fun host m g K' hh h₁ h₂ => ?_⟩
  have := h.2.2 host m g (K'.comp K) hh (by simpa using h₁) (by simpa using h₂)
  simpa using this

theorem refl (hR : ∀ b, R b b) {es : List BExpr} (h : SeqOk C es it) :
    SeqRefinesH Q R P C it es es :=
  ⟨h, h, fun _ _ _ _ _ _ _ => ExportRefines.refl hR _⟩

theorem trans (hR : ∀ x y z, R x y → R y z → R x z) {es es' es'' : List BExpr}
    (h : SeqRefinesH Q R P C it es es') (h' : SeqRefinesH Q R P C it es' es'')
    (hok : ∀ (m : BModule) (g : Nat) (K : BCtx), (m.withBody g (K.plug es)).Ok →
      (m.withBody g (K.plug es'')).Ok → (m.withBody g (K.plug es')).Ok) :
    SeqRefinesH Q R P C it es es'' :=
  ⟨h.1, h'.2.1, fun host m g K hh h₁ h₂ =>
    have h₃ := hok m g K h₁ h₂
    (h.2.2 host m g K hh h₁ h₃).trans hR (h'.2.2 host m g K hh h₃ h₂)⟩

theorem mono (hRR : ∀ x y, R x y → R' x y) {es es' : List BExpr}
    (h : SeqRefinesH Q R P C it es es') : SeqRefinesH Q R' P C it es es' :=
  ⟨h.1, h.2.1, fun host m g K hh h₁ h₂ => (h.2.2 host m g K hh h₁ h₂).mono hRR⟩

end SeqRefinesH

namespace SeqEquivH

variable {Q Q' : HostClass} {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
  {C : Context} {it : InstrType}

theorem mono_host (hQ : ∀ (H : Type) (host : HostSemantics H), Q' H host → Q H host)
    {es es' : List BExpr} (h : SeqEquivH Q R P C it es es') : SeqEquivH Q' R P C it es es' :=
  ⟨h.1.mono_host hQ, h.2.mono_host hQ⟩

theorem toSeqEquiv {es es' : List BExpr} (h : SeqEquivH HostsP R P C it es es') :
    SeqEquiv R P C it es es' :=
  ⟨h.1.toSeqRefines, h.2.toSeqRefines⟩

theorem toSafe {es es' : List BExpr} (h : SeqEquivH HostsP R P C it es es') :
    SeqEquivH HostsSafe R P C it es es' :=
  ⟨h.1.toSafe, h.2.toSafe⟩

theorem congr {es es' : List BExpr} (h : SeqEquivH Q R P C it es es') (K : BCtx)
    {C' : Context} {it' : InstrType} (hK : SeqOk C' (K.plug es) it')
    (hK' : SeqOk C' (K.plug es') it') :
    SeqEquivH Q R P C' it' (K.plug es) (K.plug es') :=
  ⟨h.1.congr K hK hK', h.2.congr K hK' hK⟩

end SeqEquivH

end Silmaril.Wasm.Binaryen
