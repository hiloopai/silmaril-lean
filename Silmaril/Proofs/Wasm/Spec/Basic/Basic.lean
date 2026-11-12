module

public import Silmaril.Wasm.Spec.Basic.Defs
public import Silmaril.Proofs.Wasm.Spec.Wasm.Ground

@[expose] public section

/-!
# The simple specification logics: proofs

The pending export of a history, prefix-closure of the simple properties, satisfaction on the
prefixes of one trace, and the closed-world reading of return postconditions for Wasm programs
(against every stateful environment, every profile). Summary in `Silmaril.Wasm.Spec.Basic.Thms`.
-/

namespace Silmaril.Wasm.Spec

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {Ty A R : Type}

/-- The pending export after one more event. -/
theorem activeExport_concat {X : Iface Ty} (h : List (Event A R X)) (e : Event A R X) :
    activeExport (h ++ [e]) = activeStep (activeExport h) e := by
  unfold activeExport
  rw [List.foldl_append]
  rfl

/-- The simple properties are inherited by prefixes. -/
theorem NeverCall.holds_of_prefix {X : Iface Ty} {i : X.Imp} {s t : List (Event A R X)}
    (ht : NeverCall.holds i t) (hs : s <+: t) : NeverCall.holds i s :=
  fun a ha => ht a (hs.subset ha)

theorem CallPre.holds_of_prefix {X : Iface Ty} {φ : CallPre.Fm A X} {s t : List (Event A R X)}
    (ht : CallPre.holds φ t) (hs : s <+: t) : CallPre.holds φ s :=
  fun a ha => ht a (hs.subset ha)

theorem NeverCallFrom.holds_of_prefix {X : Iface Ty} {φ : X.Imp × X.Exp}
    {s t : List (Event A R X)} (ht : NeverCallFrom.holds φ t) (hs : s <+: t) :
    NeverCallFrom.holds φ s :=
  EveryPos.of_prefix ht hs

theorem RetPost.holds_of_prefix {X : Iface Ty} {φ : RetPost.Fm R X} {s t : List (Event A R X)}
    (ht : RetPost.holds φ t) (hs : s <+: t) : RetPost.holds φ s :=
  fun r hr => ht r (hs.subset hr)

/-- On the prefixes of one trace, a prefix-closed per-trace property holds iff it holds of the
trace. -/
theorem ofTrace_sat_prefixesOf_iff {Fm : Iface Ty → Type}
    {holds : ∀ {X : Iface Ty}, Fm X → List (Event A R X) → Prop}
    (hpre : ∀ {X : Iface Ty} (φ : Fm X) (s t : List (Event A R X)), holds φ t → s <+: t → holds φ s)
    {X : Iface Ty} (l : List (Event A R X)) (φ : Fm X) :
    (Logic.ofTrace Fm holds).Sat (prefixesOf l) φ ↔ holds φ l :=
  ⟨fun h => h l (List.prefix_refl l), fun h s hs => hpre φ s l h hs⟩

theorem NeverCall.sat_prefixesOf_iff {X : Iface Ty} (l : List (Event A R X)) (i : X.Imp) :
    (neverCall Ty A R).Sat (prefixesOf l) i ↔ NeverCall.holds i l :=
  ⟨fun h => h l (List.prefix_refl l), fun h _ hs => NeverCall.holds_of_prefix h hs⟩

theorem CallPre.sat_prefixesOf_iff {X : Iface Ty} (l : List (Event A R X)) (φ : CallPre.Fm A X) :
    (callPre Ty A R).Sat (prefixesOf l) φ ↔ CallPre.holds φ l :=
  ⟨fun h => h l (List.prefix_refl l), fun h _ hs => CallPre.holds_of_prefix h hs⟩

theorem NeverCallFrom.sat_prefixesOf_iff {X : Iface Ty} (l : List (Event A R X))
    (φ : X.Imp × X.Exp) :
    (neverCallFrom Ty A R).Sat (prefixesOf l) φ ↔ NeverCallFrom.holds φ l :=
  ⟨fun h => h l (List.prefix_refl l), fun h _ hs => NeverCallFrom.holds_of_prefix h hs⟩

theorem RetPost.sat_prefixesOf_iff {X : Iface Ty} (l : List (Event A R X)) (φ : RetPost.Fm R X) :
    (retPost Ty A R).Sat (prefixesOf l) φ ↔ RetPost.holds φ l :=
  ⟨fun h => h l (List.prefix_refl l), fun h _ hs => RetPost.holds_of_prefix h hs⟩

theorem AssertNeverFalse.sat_prefixesOf_iff {X : Iface Ty}
    (l : List (Event (List Val) R X)) (i : X.Imp) :
    (assertNeverFalse Ty R).Sat (prefixesOf l) i ↔ AssertNeverFalse.holds i l :=
  ⟨fun h => h l (List.prefix_refl l),
    fun h _ hs => CallPre.holds_of_prefix (φ := ⟨i, assertOk⟩) h hs⟩

/-- **Return postconditions hold in the closed world** (every profile, every stateful
nondeterministic environment): if every trace of `p` satisfies the postcondition `Q` of export
`j`, every terminating behaviour of a call of `j` against the host machine `L` satisfies `Q`. -/
theorem retPost_closed_world {P : Profile} {X : WIface} (p : WasmProg X)
    (hw : p.inst.WellFormed p.store) {φ : RetPost.Fm (Behaviour Val) X}
    (hp : Models (retPost FnType (List Val) (Behaviour Val)) (wasmSem P) p φ)
    (L : SEnv (ifaceSig X.imports)) (hL : L.ThrowsBelow p.store.exns.length) (q : L.S)
    (a : Typed (X.exports.get φ.exp).params) {b : Behaviour Val} (hb : b ≠ .diverges)
    (h : b ∈ sbehavioursOf P L q (invoke p.store (p.inst.addr φ.exp) a.1)) : φ.post b := by
  have hsat : ∀ t ∈ (wasmSem P).traces p, RetPost.holds φ t :=
    (models_iff (retPost FnType (List Val) (Behaviour Val)) (wasmSem P) p φ).1 hp
  obtain ⟨t, ht, hex, -⟩ := exists_trace_of_sbehaviour p hw L hL q ⟨φ.exp, a⟩ hb h
  have hmem : (SideEv.ans φ.exp b : SideEv (List Val) (Behaviour Val) X.exports.length) ∈
      exportEvents t := by
    rw [hex]
    simp
  exact hsat t ht b (mem_exportEvents_iff.1 hmem)

/-- **Return postconditions against stateless hosts** (every profile): the Core behaviours of
an export call under the host induced by an environment `K`. -/
theorem retPost_behaviours {P : Profile} {X : WIface} (p : WasmProg X)
    (hw : p.inst.WellFormed p.store) {φ : RetPost.Fm (Behaviour Val) X}
    (hp : Models (retPost FnType (List Val) (Behaviour Val)) (wasmSem P) p φ)
    (K : Env (ifaceSig X.imports)) (hK : ThrowsBelow K p.store.exns.length)
    (a : Typed (X.exports.get φ.exp).params) {b : Behaviour Val} (hb : b ≠ .diverges)
    (h : b ∈ behaviours P (hostOf X.imports K) p.store (p.inst.addr φ.exp) a.1) : φ.post b := by
  have h' : b ∈ sbehavioursOf P (SEnv.ofEnv K) () (invoke p.store (p.inst.addr φ.exp) a.1) := by
    rw [SEnv.sbehavioursOf_ofEnv]
    exact h
  exact retPost_closed_world p hw hp (SEnv.ofEnv K) (SEnv.throwsBelow_ofEnv K _ |>.2 hK) () a hb h'

end Silmaril.Wasm.Spec
