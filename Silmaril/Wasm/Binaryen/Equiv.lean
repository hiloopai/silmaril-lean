module

public import Silmaril.Wasm.Binaryen.Behaviour
public import Silmaril.Wasm.Binaryen.CtxTyping

@[expose] public section

/-! # Equivalence notions for the IR

Two levels, both anchored on Core 3.0 behaviour of lowered code.

**(i) Module level: `ExportRefines R P host m m'`** (`m` implements `m'`). For every
valid store and import list: `m` instantiates whenever `m'` does, and every
observation of `m` (instantiation run, then any session of export invocations)
is `SessionRel R`-related to one of `m'`. Exports are observed **by name**, so
renumbering functions or globals (RemoveUnusedModuleElements, merge) costs
nothing at the interface. Pass soundness is `ExportRefines R (pass m).lower m.lower`
(the output implements the input); an equivalence is both directions with `Eq`.

**(ii) Expression level: `SeqRefines R P C it es es'`**, defined *contextually*:
plugging `es` into any one-hole context `K` in any function body of any module
gives a module that `ExportRefines` the one with `es'` plugged instead. So
`SeqRefines.congr` holds by definition (contexts compose: `BCtx.plug_comp`), and
the only hard lemma is the bridge from small-step joinability
(`Binaryen/Joinable.lean`).

Relation to the other equivalence notions in the repository:

* `Equiv.ModuleRefines` (`Silmaril/Wasm/Equiv/Module.lean`) is the fixed-store,
  single-invocation notion; `exportRefines_of_moduleRefines` is the same-address
  case.
* `Component.ObsEquiv.ModRefines` (core contexts) implies `ExportRefines Eq`:
  a separate cross-semantics bridge (not included in this package).
A general bridge from these operational relations to labeled transition-system or game-semantic certificates is a separate construction, not supplied here.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics Validation

variable {H : Type}

/-! ## Session relation -/

/-- Lifting a behaviour relation to sessions (implementation first). Pointwise,
except that once the specification exhibits a behaviour that `R` relates to
everything (a trap under `TrapsUB`), the rest of the implementation's session is
unconstrained. Under `Eq` the `ub` rule never fires.

The `ub` rule is deliberate: it is Binaryen's `trapsNeverHappen` contract lifted to
sessions. Once the specification's session reaches a trap, the implementation may do
*anything* from that point on: any later behaviours, and any number of them (fewer,
more, or none). The licence is only ever granted by the specification side, so it is
stable under composition (`SessionRel.trans`): if the middle program traps where the
implementation is licensed, the specification either traps there too or relates the
trap to its own behaviour, which by transitivity of `R` again relates to everything. -/
inductive SessionRel (R : Behaviour Val → Behaviour Val → Prop) :
    List (Behaviour Val) → List (Behaviour Val) → Prop where
  | nil : SessionRel R [] []
  | cons {b b' : Behaviour Val} {bs bs' : List (Behaviour Val)} (h : R b b')
      (t : SessionRel R bs bs') : SessionRel R (b :: bs) (b' :: bs')
  | ub {bs : List (Behaviour Val)} {b' : Behaviour Val} {bs' : List (Behaviour Val)}
      (h : ∀ b, R b b') : SessionRel R bs (b' :: bs')

namespace SessionRel

variable {R R' : Behaviour Val → Behaviour Val → Prop}

theorem refl (hR : ∀ b, R b b) : ∀ bs, SessionRel R bs bs
  | [] => .nil
  | b :: bs => .cons (hR b) (refl hR bs)

theorem mono (h : ∀ x y, R x y → R' x y) {bs bs' : List (Behaviour Val)}
    (hs : SessionRel R bs bs') : SessionRel R' bs bs' := by
  induction hs with
  | nil => exact .nil
  | cons hb _ ih => exact .cons (h _ _ hb) ih
  | ub hb => exact .ub (fun b => h _ _ (hb b))

theorem trans (hR : ∀ x y z, R x y → R y z → R x z) {as bs cs : List (Behaviour Val)}
    (h₁ : SessionRel R as bs) (h₂ : SessionRel R bs cs) : SessionRel R as cs := by
  induction h₁ generalizing cs with
  | nil => exact h₂
  | cons hab _ ih =>
    cases h₂ with
    | cons hbc t => exact .cons (hR _ _ _ hab hbc) (ih t)
    | ub hc => exact .ub hc
  | ub hb =>
    -- The middle session reached a behaviour `b` that `R` relates to everything (a
    -- trap under `TrapsUB`). If the spec then relates `b` to `c`, transitivity makes
    -- `c` relate to everything too, so the `ub` licence passes to the spec.
    cases h₂ with
    | cons hbc _ => exact .ub fun x => hR _ _ _ (hb x) hbc
    | ub hc => exact .ub hc

end SessionRel

/-! ## Module level -/

/-- **Export refinement.** `m` implements `m'`: on every valid store and import list,
`m` instantiates whenever `m'` does, and every observation of `m` is
`SessionRel R`-related to an observation of `m'`. -/
structure ExportRefines (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (host : HostSemantics H) (m m' : Module) : Prop where
  instantiates : ∀ (s : Store H) xas c', StoreOk s → Instantiate P host s m' xas c' →
    ∃ c, Instantiate P host s m xas c
  obs : ∀ (s : Store H) xas script, StoreOk s → ∀ bs ∈ moduleObs P host s xas m script,
    ∃ bs' ∈ moduleObs P host s xas m' script, SessionRel R bs bs'

/-- Two-sided export refinement. -/
def ExportEquiv (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (host : HostSemantics H) (m m' : Module) : Prop :=
  ExportRefines R P host m m' ∧ ExportRefines (fun b b' => R b' b) P host m' m

namespace ExportRefines

variable {R R' : Behaviour Val → Behaviour Val → Prop} {P : Profile} {host : HostSemantics H}

theorem refl (hR : ∀ b, R b b) (m : Module) : ExportRefines R P host m m :=
  ⟨fun _ _ c' _ h => ⟨c', h⟩, fun _ _ _ _ bs hbs => ⟨bs, hbs, SessionRel.refl hR bs⟩⟩

theorem mono (h : ∀ x y, R x y → R' x y) {m m' : Module} (hm : ExportRefines R P host m m') :
    ExportRefines R' P host m m' :=
  ⟨hm.instantiates, fun s xas script hs bs hbs =>
    let ⟨bs', hbs', hr⟩ := hm.obs s xas script hs bs hbs
    ⟨bs', hbs', hr.mono h⟩⟩

theorem trans (hR : ∀ x y z, R x y → R y z → R x z) {m m' m'' : Module}
    (h : ExportRefines R P host m m') (h' : ExportRefines R P host m' m'') :
    ExportRefines R P host m m'' :=
  ⟨fun s xas c'' hs hi =>
    let ⟨c', hc'⟩ := h'.instantiates s xas c'' hs hi
    h.instantiates s xas c' hs hc',
   fun s xas script hs bs hbs =>
    let ⟨bs', hbs', hr⟩ := h.obs s xas script hs bs hbs
    let ⟨bs'', hbs'', hr'⟩ := h'.obs s xas script hs bs' hbs'
    ⟨bs'', hbs'', hr.trans hR hr'⟩⟩

/-- Equal lowerings are equivalent: the free passes (`Pass/Free.lean`). -/
theorem of_lower_eq {m m' : BModule} (h : m.lower = m'.lower) :
    ExportRefines (· = ·) P host m.lower m'.lower := by
  rw [h]; exact refl (fun _ => rfl) _

/-- Under `Eq`, export refinement implies `TrapsUB` refinement. -/
theorem trapsUB_of_eq {m m' : Module} (h : ExportRefines (· = ·) P host m m') :
    ExportRefines TrapsUB P host m m' :=
  h.mono fun _ _ h => TrapsUB.of_eq h

end ExportRefines

/-- The session half of `exportRefines_of_moduleRefines`: a session from `s₁` is matched by
one from any `Inv`-related `s₁'`. -/
theorem session_of_moduleRefines {P : Profile} {host : HostSemantics H}
    {R : Behaviour Val → Behaviour Val → Prop} (Inv : Store H → Store H → Prop)
    (hR : ∀ b b', R b b' ↔ b = b')
    (hinv : ∀ s₁ s₁', Inv s₁ s₁' → Execution.Core.ModuleRefines R P host s₁ s₁')
    (hinvok : ∀ s₁ s₁' a vs, Inv s₁ s₁' → (InvokeOk s₁ a vs ↔ InvokeOk s₁' a vs))
    (hpres : ∀ s₁ s₁' a vs c, Inv s₁ s₁' → Steps P host (invoke s₁ a vs) c →
      ∀ c', Steps P host (invoke s₁' a vs) c' → c.code = c'.code → Inv c.store c'.store)
    {mi : ModuleInst} {s₁ : Store H} {script : List Call} {bs : List (Behaviour Val)}
    (hs : Session P host mi s₁ script bs) :
    ∀ s₁', Inv s₁ s₁' → ∃ bs', Session P host mi s₁' script bs' ∧ SessionRel R bs bs' := by
  induction hs with
  | nil => exact fun _ _ => ⟨[], .nil, .nil⟩
  | stop h =>
    intro s₁' hI
    exact ⟨[], .stop fun a ha hok => h a ha ((hinvok _ _ _ _ hI).2 hok), .nil⟩
  | @done s x vs rest a c r bs ha hok run hr _ ih =>
    intro s₁' hI
    have hb : r.toBehaviour ∈ behaviours P host s a vs := mem_behavioursOf run hr
    obtain ⟨b', hb', hRb⟩ :=
      Execution.Core.moduleRefines_iff.mp (hinv _ _ hI) a vs hok _ hb
    have heq := (hR _ _).mp hRb
    rcases hb' with ⟨c', r', run', hr', hbeq⟩ | ⟨hbeq, -⟩
    · have hrr : r = r' := Result.toBehaviour_injective (heq.trans hbeq)
      subst hrr
      have hI' := hpres _ _ _ _ _ hI run _ run' (hr.trans hr'.symm)
      obtain ⟨bs', htail, hrel⟩ := ih _ hI'
      exact ⟨_, .done ha ((hinvok _ _ _ _ hI).1 hok) run' hr' htail,
        .cons ((hR _ _).mpr rfl) hrel⟩
    · exact absurd (heq.trans hbeq) (Result.toBehaviour_ne_diverges r)
  | @diverge s x vs rest a ha hok hd =>
    intro s₁' hI
    have hb : Behaviour.diverges ∈ behaviours P host s a vs := Or.inr ⟨rfl, hd⟩
    obtain ⟨b', hb', hRb⟩ :=
      Execution.Core.moduleRefines_iff.mp (hinv _ _ hI) a vs hok _ hb
    have heq := (hR _ _).mp hRb
    rcases hb' with ⟨c', r', -, -, hbeq⟩ | ⟨-, hd'⟩
    · exact absurd (heq.trans hbeq).symm (Result.toBehaviour_ne_diverges r')
    · exact ⟨_, .diverge ha ((hinvok _ _ _ _ hI).1 hok) hd', .cons ((hR _ _).mpr rfl) .nil⟩

-- FLAG(statement-change): three hypotheses added; the original statement is refuted by
-- `exportRefines_of_moduleRefines_original_false` (separate equivalence counterexamples (not included in this package)): with
-- `Inv := False` and `R := False`, a module whose instantiation always traps (so `hready` is
-- vacuous) is not related to itself. The original hypotheses only constrain completed
-- instantiations, invocations both sides accept, and runs ending in the same code. Added:
-- `hR` (`R` is extensionally `Eq`: the head `returns []` of a session must be related to
-- itself, and `hpres` only continues the invariant when both runs end in the same code),
-- `hinit` (every instantiation outcome of `m` other than completing is one of `m'`), and
-- `hinvok` (`Inv`-related stores accept the same invocations, as the sessions' `stop` rule
-- needs). Use `ExportRefines.trapsUB_of_eq` for `TrapsUB`.
/-- **Same-address case.** If `m` and `m'` instantiate in lockstep to stores in
which every export of `m` refines (`Execution.Core.ModuleRefines`) the same
address of `m'`'s store, and that refinement is preserved by every invocation,
then `ExportRefines` holds. The side condition is the per-store invariant
`Inv`, the shape a separate reachable-store refinement development (not included in this package)'s `StepClosed` supplies. -/
theorem exportRefines_of_moduleRefines {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    {host : HostSemantics H} {m m' : Module} (Inv : Store H → Store H → Prop)
    (hR : ∀ b b', R b b' ↔ b = b')
    (hinst : ∀ s xas c', StoreOk s → Instantiate P host s m' xas c' →
      ∃ c, Instantiate P host s m xas c)
    (hinit : ∀ s xas, StoreOk s → ∀ b ∈ initBeh P host s m xas, b ≠ .returns [] →
      b ∈ initBeh P host s m' xas)
    (hready : ∀ s xas s₁ mi, Ready P host s m xas s₁ mi →
      ∃ s₁', Ready P host s m' xas s₁' mi ∧ Inv s₁ s₁')
    (hinv : ∀ s₁ s₁', Inv s₁ s₁' → Execution.Core.ModuleRefines R P host s₁ s₁')
    (hinvok : ∀ s₁ s₁' a vs, Inv s₁ s₁' → (InvokeOk s₁ a vs ↔ InvokeOk s₁' a vs))
    (hpres : ∀ s₁ s₁' a vs c, Inv s₁ s₁' → Steps P host (invoke s₁ a vs) c →
      ∀ c', Steps P host (invoke s₁' a vs) c' → c.code = c'.code → Inv c.store c'.store) :
    ExportRefines R P host m m' := by
  refine ⟨hinst, fun s xas script hs bs hbs => ?_⟩
  obtain ⟨c, hI, hcase⟩ := hbs
  rcases hcase with ⟨c', bs', hS, hcode, hsess, rfl⟩ | ⟨c', r, hS, hcode, hr, rfl⟩ | ⟨hd, rfl⟩
  · obtain ⟨s₁', ⟨d, d', hI', hS', hcode', hst, hmod⟩, hInv⟩ :=
      hready s xas c'.store c.frame.module ⟨c, c', hI, hS, hcode, rfl, rfl⟩
    obtain ⟨bs'', hsess', hrel⟩ :=
      session_of_moduleRefines Inv hR hinv hinvok hpres hsess s₁' hInv
    refine ⟨_, ⟨d, hI', Or.inl ⟨d', bs'', hS', hcode', ?_, rfl⟩⟩, .cons ((hR _ _).mpr rfl) hrel⟩
    rw [hst, hmod]
    exact hsess'
  · have hne : r.toBehaviour ≠ .returns [] := by
      intro h
      apply hr
      cases r <;> simp_all [Result.toBehaviour]
    obtain ⟨d, hI', hb'⟩ := hinit s xas hs _ ⟨c, hI, mem_behavioursOf hS hcode⟩ hne
    rcases hb' with ⟨d', r', hS', hcode', hbeq⟩ | ⟨hbeq, -⟩
    · have hrr : r' = r := Result.toBehaviour_injective hbeq.symm
      subst hrr
      exact ⟨_, ⟨d, hI', Or.inr (Or.inl ⟨d', r', hS', hcode', hr, rfl⟩)⟩,
        .cons ((hR _ _).mpr rfl) .nil⟩
    · exact absurd hbeq (Result.toBehaviour_ne_diverges r)
  · obtain ⟨d, hI', hb'⟩ := hinit s xas hs _ ⟨c, hI, Or.inr ⟨rfl, hd⟩⟩ (by simp)
    rcases hb' with ⟨d', r', -, -, hbeq⟩ | ⟨-, hd'⟩
    · exact absurd hbeq.symm (Result.toBehaviour_ne_diverges r')
    · exact ⟨_, ⟨d, hI', Or.inr (Or.inr ⟨hd', rfl⟩)⟩, .cons ((hR _ _).mpr rfl) .nil⟩

/-- The host never inspects function code: replacing Wasm code (keeping types)
in the store does not change what host calls may do. The Core analogue of
a separate reachable-store refinement development (not included in this package)'s `HostRespectsReplace`. `closedHost` satisfies it. -/
def HostRespectsCode (host : HostSemantics H) : Prop :=
  ∀ (h : H) (s s' : Store H) (vs : List Val) (o : HostOutcome H),
    (s.funcs.map (FuncInst.type (H := H)) = s'.funcs.map (FuncInst.type (H := H)) ∧
      ({ s with funcs := [] } : Store H) = ({ s' with funcs := [] } : Store H)) →
    host h s vs o → host h s' vs o

theorem closedHost_respectsCode : HostRespectsCode (closedHost (H := H)) :=
  fun _ _ _ _ _ _ h => False.elim h

/-- **Contextual refinement of sequences.** `es` implements `es'` at type `it` in
context `C`: both are typed there, and in every module, every function body and
every one-hole context, under every code-respecting host, the module with `es`
plugged `ExportRefines` the one with `es'` plugged. -/
def SeqRefines (R : Behaviour Val → Behaviour Val → Prop) (P : Profile) (C : Context)
    (it : InstrType) (es es' : List BExpr) : Prop :=
  SeqOk C es it ∧ SeqOk C es' it ∧
  ∀ {H : Type} (host : HostSemantics H) (m : BModule) (g : Nat) (K : BCtx),
    HostRespectsCode host →
    (m.withBody g (K.plug es)).Ok → (m.withBody g (K.plug es')).Ok →
    ExportRefines R P host (m.withBody g (K.plug es)).lower (m.withBody g (K.plug es')).lower

/-- Contextual equivalence: refinement both ways. -/
def SeqEquiv (R : Behaviour Val → Behaviour Val → Prop) (P : Profile) (C : Context)
    (it : InstrType) (es es' : List BExpr) : Prop :=
  SeqRefines R P C it es es' ∧ SeqRefines (fun b b' => R b' b) P C it es' es

namespace SeqRefines

variable {R R' : Behaviour Val → Behaviour Val → Prop} {P : Profile} {C : Context}
  {it : InstrType}

/-- **Congruence, by definition.** -/
theorem congr {es es' : List BExpr} (h : SeqRefines R P C it es es') (K : BCtx) {C' : Context}
    {it' : InstrType} (hK : SeqOk C' (K.plug es) it') (hK' : SeqOk C' (K.plug es') it') :
    SeqRefines R P C' it' (K.plug es) (K.plug es') := by
  refine ⟨hK, hK', fun host m g K' hh h₁ h₂ => ?_⟩
  have := h.2.2 host m g (K'.comp K) hh (by simpa using h₁) (by simpa using h₂)
  simpa using this

theorem refl (hR : ∀ b, R b b) {es : List BExpr} (h : SeqOk C es it) : SeqRefines R P C it es es :=
  ⟨h, h, fun _ _ _ _ _ _ _ => ExportRefines.refl hR _⟩

theorem trans (hR : ∀ x y z, R x y → R y z → R x z) {es es' es'' : List BExpr}
    (h : SeqRefines R P C it es es') (h' : SeqRefines R P C it es' es'')
    (hok : ∀ (m : BModule) (g : Nat) (K : BCtx), (m.withBody g (K.plug es)).Ok →
      (m.withBody g (K.plug es'')).Ok → (m.withBody g (K.plug es')).Ok) :
    SeqRefines R P C it es es'' :=
  ⟨h.1, h'.2.1, fun host m g K hh h₁ h₂ =>
    have h₃ := hok m g K h₁ h₂
    (h.2.2 host m g K hh h₁ h₃).trans hR (h'.2.2 host m g K hh h₃ h₂)⟩

theorem mono (hRR : ∀ x y, R x y → R' x y) {es es' : List BExpr} (h : SeqRefines R P C it es es') :
    SeqRefines R' P C it es es' :=
  ⟨h.1, h.2.1, fun host m g K hh h₁ h₂ => (h.2.2 host m g K hh h₁ h₂).mono hRR⟩

/-- Rewriting closure of a rule: zero or more rewrites, each in some context. -/
inductive Star (rule : List BExpr → List BExpr → Prop) : List BExpr → List BExpr → Prop where
  | refl (es : List BExpr) : Star rule es es
  | step {K : BCtx} {a b es : List BExpr} (h : rule a b) (t : Star rule (K.plug b) es) :
      Star rule (K.plug a) es

-- FLAG(statement-change): added `(hC : C.Wf)`. A rewrite inside a context needs a typing
-- of the hole, read off the typing of the plugged sequence by splitting it
-- (`InstrsOk.append_inv`), and splitting a typing derivation is only available in a
-- well-formed context (it uses transitivity of subtyping). Every context a function body
-- is typed in is well formed, so this costs nothing in use.
/-- **Rewriting everywhere.** A rule whose instances are refinements at their own
typing, and which preserves typing, may be applied any number of times anywhere. -/
theorem everywhere (hR : ∀ b, R b b) (hRt : ∀ x y z, R x y → R y z → R x z)
    {rule : List BExpr → List BExpr → Prop}
    (hrule : ∀ C it a b, rule a b → SeqOk C a it → SeqRefines R P C it b a)
    (hpres : ∀ C it a b, rule a b → SeqOk C a it → SeqOk C b it) (hC : C.Wf)
    {es es' : List BExpr} (h : Star rule es es') (hok : SeqOk C es it) :
    SeqRefines R P C it es' es := by
  induction h with
  | refl es => exact refl hR hok
  | @step K a b es₂ hab _ ih =>
    have hty : TyRepl (BExpr.lowerList a) (BExpr.lowerList b) :=
      fun C' it' _ h => hpres C' it' a b hab h
    have hKty := CtxTyping.tyRepl_plug K hty
    have hokb : SeqOk C (K.plug b) it := hKty C it hC hok
    obtain ⟨C', it', -, ha'⟩ := CtxTyping.plug_typing K a hC hok
    have hK := (hrule C' it' a b hab ha').congr K hokb hok
    exact (ih hokb).trans hRt hK fun m g K' _ h₂ =>
      CtxTyping.ok_transfer (CtxTyping.tyRepl_plug K' hKty) h₂

end SeqRefines

end Silmaril.Wasm.Binaryen
