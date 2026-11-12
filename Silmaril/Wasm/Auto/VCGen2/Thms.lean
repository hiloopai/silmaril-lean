module

public import Silmaril.Wasm.Auto.VCGen2.Defs
public import Silmaril.Wasm.Auto.VCGen.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Wasm.Logic.VC.Thms
public import Silmaril.Wasm.Examples.Common.Thms
import Silmaril.Proofs.Wasm.Auto.VCGen2.Func

/-!
# The VC generator with SSA names, memory and variants: results and tactics

Proofs in `Silmaril.Proofs.Wasm.Auto.VCGen2.{Basic,Step,Ren,Call,Sound,Func}`,
written once for both readings `c : Corr` of the every-run logic (`Wp .part = HWP`,
`Wp .total = TWP`):

* **`genFunc_sound`**: `AllValid F (genFunc S code fuel)` gives
  `FSpecValid P host a (fspec F S a fi)` (partial correctness and safety) for every profile `P` and
  host relation `host`, for the function instance `fi` at address `a` running `code`;
* **`genFunc_tsound`**: with `S.total = true` (the generator then asks, at every branch back to
  loop `j`, that the variant `S.var[j]` at the current locals be below its value at the head of
  the iteration), the same conditions give `TFSpecAt P host a (fspec F S a fi)`: every run of
  every call terminates (no trap, no exception) with results of the declared types and a final
  memory satisfying `S.post`. Callees must then be totally correct (`CalleesValid .total`);
* `gen_sound` (any code, labels and continuation, either reading), `step1_sound`, `sound_call`,
  `postOf_mono` (the postcondition is stable when the environment grows above the next fresh
  variable: what keeps the head values of a loop, and so its variant bound, fixed during an
  iteration).

## Tactics

* **`vcgen2_reduce`**: on a goal `AllValid F l` with `l` closed (typically
  `genFunc S code fuel`), computes the list of conditions by `Meta.reduce` and replaces `l` by
  it, through an auxiliary lemma checked by the kernel (as `Silmaril.Wasm.Auto.VCGen`'s `vcgen_reduce`);
* **`vcgen2`**: `vcgen2_reduce`, then unfold the denotation of the conditions with `simp only`,
  split them into one goal each and name the variables (`ρ.e32 i` is `vi`, `ρ.e64 i` is `wi`,
  memory variable `ρ.mem i` is `Mi`; `M0` is the memory at entry). Loads stay as
  `ldW w n sx M a` (`Silmaril.Wasm.Auto.VCGen2.ldW`), stores as `stW …`; user predicates and memory
  functions as the fields `F.pr`, `F.mf` of the specification functions.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.VCGen2

/-! ## Results proved in `Silmaril.Proofs.Wasm.Auto.VCGen2` -/

section

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation (Expand Ty)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (FSpecValid Wp Corr TFSpecAt)

/-- **A straight-line instruction**, every run. -/
theorem step1_sound {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {c : Corr}
    {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst} {i : Instr}
    {σ : SSt} {σ' : SSt} {side : List Fm} {ρ : Env} {s : Store H} {f : Frame} {rs : List Val}
    {rest : List Admin} {Q : Post H}
    (h : step1 S.mem i σ = some (σ', side)) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hs : ∀ φ ∈ side, φ.den F ρ ρ) (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain i :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.VCGen2.step1_sound (H := H) (P := P) (host := host) (F := F) (c := c)
    (S := S) (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (i := i) (σ := σ) (σ' := σ') (side := side)
    (ρ := ρ) (s := s) (f := f) (rs := rs) (rest := rest) (Q := Q) (h := h) (hR := hR) (hs := hs)
    (hk := hk)

/-- **A call**, every run: the callee's precondition holds at the call, and its every-run
specification gives the configurations after the call, related to the generator's state. -/
theorem sound_call {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {c : Corr}
    {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst} {σ : SSt} {ρ : Env}
    {s : Store H} {f : Frame} {rs : List Val}
    {x : FuncIdx} {σ₁ σ₂ : SSt} {pre : Fm} {rest : List Admin} {Q : Post H}
    (hS : S.wellScoped = true) (hC : CallsOK c P host F S s₀ m)
    (h : callStep S x.toNat σ = some (σ₁, pre, σ₂)) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hpre : Valid F (vc σ₁ pre)) (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ₂ rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.call x) :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.VCGen2.sound_call (H := H) (P := P) (host := host) (F := F) (c := c)
    (S := S) (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (σ := σ) (ρ := ρ) (s := s) (f := f)
    (rs := rs) (x := x) (σ₁ := σ₁) (σ₂ := σ₂) (pre := pre) (rest := rest) (Q := Q) (hS := hS)
    (hC := hC) (h := h) (hR := hR) (hpre := hpre) (hk := hk)

/-- **The postcondition is stable** under extending the environment above `N`. -/
theorem postOf_mono {H : Type} {c : Corr} {F : Fns} {S : FnSpec} {lt : List IntType} {ρ₀ : Env}
    {s₀ : Store H} {m : ModuleInst} {L : List Lbl} {kont : SSt → List Fm} {ρ ρ' : Env} {N N' : Nat}
    (hE : EqBelow N ρ ρ') (hN : N ≤ N') (hL : LblsOK S L N) {s : Store H} {f : Frame}
    {o : Outcome} (h : postOf F S lt ρ₀ s₀ m c ρ' N' L kont s f o) :
    postOf F S lt ρ₀ s₀ m c ρ N L kont s f o :=
  Silmaril.Proofs.Wasm.Auto.VCGen2.postOf_mono (H := H) (c := c) (F := F) (S := S) (lt := lt)
    (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (L := L) (kont := kont) (ρ := ρ) (ρ' := ρ') (N := N) (N' := N')
    (hE := hE) (hN := hN) (hL := hL) (s := s) (f := f) (o := o) (h := h)

/-- **Soundness of the generator**, at every `fuel`, in either reading (total correctness needs
the variant conditions, `S.total`). -/
theorem gen_sound {H : Type} {P : Profile} {host : HostSemantics H} {c : Corr} {F : Fns}
    {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst}
    (hS : S.wellScoped = true) (hT : c = .total → S.total = true)
    (hC : CallsOK c P host F S s₀ m) : ∀ fuel, IH F S lt ρ₀ s₀ m c P host fuel :=
  Silmaril.Proofs.Wasm.Auto.VCGen2.gen_sound (H := H) (P := P) (host := host) (c := c) (F := F)
    (S := S) (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (hS := hS) (hT := hT) (hC := hC)

/-- **Soundness of the generator for functions.** Valid conditions give the every-run
specification `fspec`: at every profile and for every host relation, a call with arguments and
memory satisfying the precondition returns results (of the declared types) and a final memory
satisfying the postcondition, without trapping; the store changes only in memory `0`'s bytes
(partial correctness). The callees' specifications are assumed (`CalleesValid .part`; for a
function without callees, `by simp`). -/
theorem genFunc_sound {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {fuel a : Nat} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hps : S.params.length = ps.length) (hrs : S.results.length = rs.length)
    (hvc : AllValid F (genFunc S code fuel)) (hC : CalleesValid .part P host F S) :
    FSpecValid P host a (fspec F S a fi) :=
  Silmaril.Proofs.Wasm.Auto.VCGen2.genFunc_sound (H := H) (P := P) (host := host) (F := F) (S := S)
    (fuel := fuel) (a := a) (fi := fi) (code := code) (ps := ps) (rs := rs) (hcode := hcode)
    (he := he) (hps := hps) (hrs := hrs) (hvc := hvc) (hC := hC)

/-- **Total correctness.** With the variant conditions (`S.total`), valid conditions give `fspec`
for total correctness: every run of the call terminates, with the outcome `genFunc_sound`
describes. The callees' specifications are assumed for total correctness
(`CalleesValid .total`). -/
theorem genFunc_tsound {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {fuel a : Nat} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)}
    (hT : S.total = true) (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hps : S.params.length = ps.length) (hrs : S.results.length = rs.length)
    (hvc : AllValid F (genFunc S code fuel)) (hC : CalleesValid .total P host F S) :
    TFSpecAt P host a (fspec F S a fi) :=
  Silmaril.Proofs.Wasm.Auto.VCGen2.genFunc_tsound (H := H) (P := P) (host := host) (F := F) (S := S)
    (fuel := fuel) (a := a) (fi := fi) (code := code) (ps := ps) (rs := rs) (hT := hT)
    (hcode := hcode) (he := he) (hps := hps) (hrs := hrs) (hvc := hvc) (hC := hC)

end

open Lean Elab Tactic Meta in
/-- Compute the conditions of a closed list `l` in a goal `AllValid F l` (see the module
docstring). -/
elab "vcgen2_reduce" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let some (fns, e) := tgt.app2? ``AllValid
      | throwError "vcgen2_reduce: the goal is not `AllValid F l`"
    if e.hasFVar || e.hasMVar then
      throwError "vcgen2_reduce: the list of conditions must be closed"
    let e' ← withTransparency .all <| reduce e (skipTypes := true) (skipProofs := true)
    let eqTy ← mkEq e e'
    let lvls := (collectLevelParams {} eqTy).params
    let lemmaLevels := (← Term.getLevelNames).reverse.filter lvls.contains
    let n ← withOptions (Elab.async.set · false) do mkAuxLemma lemmaLevels eqTy (← mkEqRefl e')
    let pf := mkConst n (lemmaLevels.map .param)
    let g' ← g.replaceTargetEq (mkApp2 (mkConst ``AllValid) fns e')
      (← mkCongrArg (mkApp (mkConst ``AllValid) fns) pf)
    replaceMainGoal [g']

/-- Unfold the denotation of computed conditions (see the module docstring). -/
macro "vcgen2_den" : tactic => `(tactic| (
  simp only [Silmaril.Wasm.Auto.VCGen2.AllValid, Silmaril.Wasm.Auto.VCGen2.Valid,
    Silmaril.Wasm.Auto.VCGen2.Fm.den, Silmaril.Wasm.Auto.VCGen2.Tm.den, Silmaril.Wasm.Auto.VCGen2.Env.get,
    Silmaril.Wasm.Auto.VCGen2.Fns.app1, Silmaril.Wasm.Auto.VCGen2.Fns.app2,
    Silmaril.Wasm.Auto.VCGen.litT, Silmaril.Wasm.Auto.VCGen.unT, Silmaril.Wasm.Auto.VCGen.binT,
    Silmaril.Wasm.Auto.VCGen.relP, Silmaril.Wasm.Auto.VCGen.unW, Silmaril.Wasm.Auto.VCGen.binW,
    Silmaril.Wasm.Auto.VCGen.relW, Silmaril.Wasm.Auto.VCGen.relV_ne_zero,
    Silmaril.Wasm.Auto.VCGen.eqzV_ne_zero, Silmaril.Wasm.Auto.VCGen.relV, Silmaril.Wasm.Auto.VCGen.eqzV,
    Silmaril.Wasm.Auto.VCGen.bool32_bne_zero, Silmaril.Wasm.Auto.VCGen.relB, Bool.cond_decide,
    Silmaril.Wasm.Auto.VCGen.nz32, Silmaril.Wasm.Auto.VCGen.iteT, Silmaril.Wasm.Auto.VCGen.wrapW, Silmaril.Wasm.Auto.VCGen.extSW,
    Silmaril.Wasm.Auto.VCGen.extUW, Silmaril.Wasm.Auto.VCGen2.MR.den, Silmaril.Wasm.Auto.VCGen2.ldT,
    Silmaril.Wasm.Auto.VCGen2.stT, Silmaril.Wasm.Auto.VCGen2.Tm.dens32,
    cond_eq_ite, bne_iff_ne, beq_iff_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    and_true, true_implies, true_and]
  try simp only [cond_eq_ite, beq_iff_eq, bne_iff_ne, Silmaril.Wasm.Numerics.bool32,
    Silmaril.Wasm.Auto.VCGen.ult_iff, Silmaril.Wasm.Auto.VCGen.ule_iff, Silmaril.Wasm.Auto.VCGen.slt_iff,
    Silmaril.Wasm.Auto.VCGen.sle_iff]))

open Lean Meta in
/-- The kind and index of an atom `ρ.e32 i` (`(0, i)`), `ρ.e64 i` (`(1, i)`) or `ρ.mem i`
(`(2, i)`). -/
meta def envAtom? (ρ : Lean.Expr) (e : Lean.Expr) : Option (Nat × Nat) :=
  let idx := fun (k : Nat) => (e.appArg!.rawNatLit? <|> e.appArg!.nat?).map ((k, ·))
  if e.isAppOfArity ``Env.e32 2 && e.appFn!.appArg! == ρ then idx 0
  else if e.isAppOfArity ``Env.e64 2 && e.appFn!.appArg! == ρ then idx 1
  else if e.isAppOfArity ``Env.mem 2 && e.appFn!.appArg! == ρ then idx 2
  else none

open Lean Meta in
/-- The atoms of an expression, one per index, with a representative. -/
meta partial def envAtoms (ρ : Lean.Expr) (e : Lean.Expr)
    (acc : Array ((Nat × Nat) × Lean.Expr)) :
    Array ((Nat × Nat) × Lean.Expr) :=
  match envAtom? ρ e with
  | some k => if acc.any (·.1 == k) then acc else acc.push (k, e)
  | none =>
    match e with
    | .app f a => envAtoms ρ a (envAtoms ρ f acc)
    | .lam _ t b _ | .forallE _ t b _ => envAtoms ρ b (envAtoms ρ t acc)
    | .letE _ t v b _ => envAtoms ρ b (envAtoms ρ v (envAtoms ρ t acc))
    | .mdata _ b => envAtoms ρ b acc
    | .proj _ _ b => envAtoms ρ b acc
    | _ => acc

open Lean Elab Tactic Meta in
/-- On a goal `∀ ρ : Env, P`, name each value `ρ.e32 i` as `vi`, `ρ.e64 i` as `wi` and `ρ.mem i` as `Mi`: the goal
becomes `∀ vi … wj, P'` with the values replaced syntactically (no unification), then the names
are introduced. -/
elab "vcgen2_vars" : tactic => do
  liftMetaTactic fun g => do
    let (ρ, g) ← g.intro `ρ
    g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      let atoms := envAtoms (.fvar ρ) tgt #[]
      let names := atoms.map fun ((b, i), _) =>
        Name.mkSimple (if b == 0 then s!"v{i}" else if b == 1 then s!"w{i}" else s!"M{i}")
      let decls := (atoms.zip names).map fun ((_, e), n) => (n, fun _ => inferType e)
      let tgt' ← withLocalDeclsD decls fun xs => do
        let body := tgt.replace fun e =>
          match envAtom? (.fvar ρ) e with
          | some k => (atoms.findIdx? (·.1 == k)).map (xs[·]!)
          | none => none
        mkForallFVars xs body
      let g' ← mkFreshExprSyntheticOpaqueMVar tgt' (← g.getTag)
      g.assign (mkAppN g' (atoms.map (·.2)))
      let (_, g'') ← g'.mvarId!.introN atoms.size names.toList
      let g'' ← g''.tryClear ρ
      return [g'']

/-- Compute the conditions and state each as a goal (see the module docstring). -/
macro "vcgen2" : tactic =>
  `(tactic| (vcgen2_reduce; vcgen2_den; (try and_intros); all_goals try vcgen2_vars))

end Silmaril.Wasm.Auto.VCGen2
