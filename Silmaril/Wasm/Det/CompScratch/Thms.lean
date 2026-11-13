module

public import Silmaril.Wasm.Det.CompScratch.Defs
public import Silmaril.Wasm.Det.CompRef.Thms
public import Silmaril.Wasm.Det.CompRef.Litmus.Thms
import Silmaril.Proofs.Wasm.Det.CompScratch.Basic
import Silmaril.Proofs.Wasm.Det.CompScratch.Seq
import Silmaril.Proofs.Wasm.Det.CompScratch.Simple

/-!
# The scratch-buffer discipline on the reference machine: theorems

* `compStateless_of_obs` (**unwinding on the reference machine**): for an observable-state
  relation `Obs` on machine configurations that is symmetric and transitive, confinement
  (`RefConfined`) and observation (`RefObsDetermines`) give `CompStateless` of the component
  against the host `h`, at any component choice profile and any core engine;
* `compStateless_of_scratch`: the instance for the scratch relation `ScratchCfg m lo hi` over
  `core3P P` (every profile): a component whose calls only change the bytes `[lo, hi)` of core
  memory `m` (and the core store nowhere else, the rest of the configuration not at all, up to
  `eraseCore`) and whose outputs do not read the scratch contents is stateless;
* `scratchCfg_refl`, `scratchCfg_symm`, `scratchCfg_trans`, and the same for `ScratchEqH`.

`eraseCore` keeps the machine's call bookkeeping (`pending`, `results`, …), which every
top-level call changes, and `CompReach` allows reused call ids, under which `CompStateless`
fails for the adder (see `Silmaril.Wasm.Det.CompScratch.Defs`). The session versions fix both:

* `compStatelessSeq_of_obs`: unwinding over sessions (`SeqReach`: ids `0, 1, …`, admissible
  arguments, resolved calls), for any symmetric and transitive `Obs`;
* `compStatelessSeq_of_book`: the instance for `BookCfg m lo hi`, which ignores the call
  bookkeeping and compares the core stores outside the scratch bytes;
* `simple_compStatelessSeq`: every float-free simple component within the flat arities whose
  module is `ModStateless` is stateless over sessions with well-typed arguments (`SimpleAdm`);
  through `seq_refToSpec` and the IR's statelessness, not through an `Obs`;
* litmus `adder_compStatelessSeq`, `adder_refObsDeterminesSeq` (for every `BookCfg m lo hi`,
  in particular an empty scratch region).

Not done: `RefConfinedSeq` for `BookCfg` of the adder. It needs the configuration after a call
(`readyCfg`/`nextCfg` of `Silmaril.Proofs.Wasm.Component.Reference.MultiSeq.seq_inv`), which no
header of `Silmaril.Wasm.Component.Reference` exports.

Proofs: `Silmaril.Proofs.Wasm.Det.CompScratch.{Basic,Seq,Simple}`. New theorems.
-/

public section

namespace Silmaril.Wasm.Det.CompScratch

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Reference (Host initConfig Engine core3P)
open Silmaril.Wasm.Det.Core.Component

variable {E : Engine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]

/-- **Unwinding on the reference machine.** -/
theorem compStateless_of_obs {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {comp : Syntax.Component E.Module} {args : Instantiate.Exports E}
    {Obs : Config E σ → Config E σ → Prop} (hsy : ∀ {a b}, Obs a b → Obs b a)
    (htr : ∀ {a b c}, Obs a b → Obs b c → Obs a c) (hc : RefConfined prof h σ0 comp args Obs)
    (hd : RefObsDetermines prof h σ0 comp args Obs) : CompStateless prof h σ0 comp args :=
  Silmaril.Proofs.Wasm.Det.CompScratch.compStateless_of_obs (Obs := Obs) hsy htr hc hd

theorem scratchCfg_refl {P : Silmaril.Wasm.Numerics.Profile} {τ : Type} (m lo hi : Nat)
    (c : Config (core3P P) τ) : ScratchCfg m lo hi c c :=
  Silmaril.Proofs.Wasm.Det.CompScratch.scratchCfg_refl m lo hi c

theorem scratchCfg_symm {P : Silmaril.Wasm.Numerics.Profile} {τ : Type} {m lo hi : Nat}
    {c₁ c₂ : Config (core3P P) τ} (h : ScratchCfg m lo hi c₁ c₂) : ScratchCfg m lo hi c₂ c₁ :=
  Silmaril.Proofs.Wasm.Det.CompScratch.scratchCfg_symm h

theorem scratchCfg_trans {P : Silmaril.Wasm.Numerics.Profile} {τ : Type} {m lo hi : Nat}
    {c₁ c₂ c₃ : Config (core3P P) τ} (h₁ : ScratchCfg m lo hi c₁ c₂)
    (h₂ : ScratchCfg m lo hi c₂ c₃) : ScratchCfg m lo hi c₁ c₃ :=
  Silmaril.Proofs.Wasm.Det.CompScratch.scratchCfg_trans h₁ h₂

/-- **The scratch discipline on the reference machine gives statelessness** (every profile). -/
theorem compStateless_of_scratch {P : Silmaril.Wasm.Numerics.Profile} {τ : Type}
    [∀ a b, Decidable ((core3P P).ExternSub a b)] {prof : ProfileKind} {h : Host (core3P P) τ}
    {σ0 : τ} {comp : Syntax.Component (core3P P).Module} {args : Instantiate.Exports (core3P P)}
    {m lo hi : Nat} (hc : RefConfined prof h σ0 comp args (ScratchCfg m lo hi))
    (hd : RefObsDetermines prof h σ0 comp args (ScratchCfg m lo hi)) :
    CompStateless prof h σ0 comp args :=
  compStateless_of_obs (Obs := ScratchCfg m lo hi) scratchCfg_symm scratchCfg_trans hc hd

/-! ## Sessions -/

/-- **Unwinding over sessions.** -/
theorem compStatelessSeq_of_obs {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {comp : Syntax.Component E.Module} {args : Instantiate.Exports E}
    {Adm : String → List Value.Val → Prop} {Obs : Config E σ → Config E σ → Prop}
    (hsy : ∀ {a b}, Obs a b → Obs b a) (htr : ∀ {a b c}, Obs a b → Obs b c → Obs a c)
    (hc : RefConfinedSeq prof h σ0 comp args Adm Obs)
    (hd : RefObsDeterminesSeq prof h σ0 comp args Adm Obs) :
    CompStatelessSeq prof h σ0 comp args Adm :=
  Silmaril.Proofs.Wasm.Det.CompScratch.compStatelessSeq_of_obs (Obs := Obs) hsy htr hc hd

theorem refObsDeterminesSeq_of_stateless {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {comp : Syntax.Component E.Module} {args : Instantiate.Exports E}
    {Adm : String → List Value.Val → Prop} (Obs : Config E σ → Config E σ → Prop)
    (hs : CompStatelessSeq prof h σ0 comp args Adm) :
    RefObsDeterminesSeq prof h σ0 comp args Adm Obs :=
  Silmaril.Proofs.Wasm.Det.CompScratch.refObsDeterminesSeq_of_stateless Obs hs

theorem bookCfg_refl {P : Silmaril.Wasm.Numerics.Profile} {τ : Type} (m lo hi : Nat)
    (c : Config (core3P P) τ) : BookCfg m lo hi c c :=
  Silmaril.Proofs.Wasm.Det.CompScratch.bookCfg_refl m lo hi c

theorem bookCfg_symm {P : Silmaril.Wasm.Numerics.Profile} {τ : Type} {m lo hi : Nat}
    {c₁ c₂ : Config (core3P P) τ} (h : BookCfg m lo hi c₁ c₂) : BookCfg m lo hi c₂ c₁ :=
  Silmaril.Proofs.Wasm.Det.CompScratch.bookCfg_symm h

theorem bookCfg_trans {P : Silmaril.Wasm.Numerics.Profile} {τ : Type} {m lo hi : Nat}
    {c₁ c₂ c₃ : Config (core3P P) τ} (h₁ : BookCfg m lo hi c₁ c₂)
    (h₂ : BookCfg m lo hi c₂ c₃) : BookCfg m lo hi c₁ c₃ :=
  Silmaril.Proofs.Wasm.Det.CompScratch.bookCfg_trans h₁ h₂

/-- **The scratch discipline ignoring the call bookkeeping gives statelessness over sessions**
(every profile). -/
theorem compStatelessSeq_of_book {P : Silmaril.Wasm.Numerics.Profile} {τ : Type}
    [∀ a b, Decidable ((core3P P).ExternSub a b)] {prof : ProfileKind} {h : Host (core3P P) τ}
    {σ0 : τ} {comp : Syntax.Component (core3P P).Module} {args : Instantiate.Exports (core3P P)}
    {Adm : String → List Value.Val → Prop} {m lo hi : Nat}
    (hc : RefConfinedSeq prof h σ0 comp args Adm (BookCfg m lo hi))
    (hd : RefObsDeterminesSeq prof h σ0 comp args Adm (BookCfg m lo hi)) :
    CompStatelessSeq prof h σ0 comp args Adm :=
  compStatelessSeq_of_obs (Obs := BookCfg m lo hi) bookCfg_symm bookCfg_trans hc hd

open Silmaril.Wasm.Component.Reference in
/-- **Simple components with stateless modules are stateless over sessions** (every profile,
every component choice profile). -/
theorem simple_compStatelessSeq (P : Silmaril.Wasm.Numerics.Profile) (prof : ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (hD : Silmaril.Wasm.Det.CompRef.ModStateless P c.mod) :
    CompStatelessSeq prof (refHost P) () c.toRef [] (SimpleAdm c) :=
  Silmaril.Proofs.Wasm.Det.CompScratch.simple_compStatelessSeq P prof c hc hf hi ha hD

open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus in
/-- **Litmus: the adder is stateless over sessions on the reference machine.** -/
theorem adder_compStatelessSeq (P : Silmaril.Wasm.Numerics.Profile) (prof : ProfileKind) :
    CompStatelessSeq prof (refHost P) () adderS.toRef [] (SimpleAdm adderS) :=
  simple_compStatelessSeq P prof adderS adderS_good
    Silmaril.Proofs.Wasm.Det.CompScratch.adderS_floatFree' adderS_inst adderS_arity
    (Silmaril.Wasm.Det.CompRef.Litmus.adder_modStateless P)

open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus in
/-- **Litmus: observation for the bookkeeping-blind scratch relation**, any region (in
particular the empty one, `lo = hi`). -/
theorem adder_refObsDeterminesSeq (P : Silmaril.Wasm.Numerics.Profile) (prof : ProfileKind)
    (m lo hi : Nat) :
    RefObsDeterminesSeq prof (refHost P) () adderS.toRef [] (SimpleAdm adderS) (BookCfg m lo hi) :=
  refObsDeterminesSeq_of_stateless _ (adder_compStatelessSeq P prof)

end Silmaril.Wasm.Det.CompScratch
