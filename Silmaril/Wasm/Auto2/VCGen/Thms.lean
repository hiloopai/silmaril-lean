module

public import Silmaril.Proofs.Wasm.Auto2.VCGen.Rec
public import Silmaril.Wasm.Auto.VCGen.Thms

/-!
# The VC generator (SSA names, memory, variants, entry facts): results and tactics

`Silmaril.Wasm.Auto2.VCGen` is `Silmaril.Wasm.Auto.VCGen3` (loop variants for total correctness) whose
loop heads keep the entry path condition (see `Silmaril.Wasm.Auto2.VCGen.Defs`). Proofs in `Silmaril.Proofs.Wasm.Auto2.VCGen.{Basic,Step,Ren,Call,Sound,Func}`,
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
* **`genFunc_tsound_rec`** (`Silmaril.Proofs.Wasm.Auto2.VCGen.Rec`): a function
  that calls itself, checked against a recursive callee contract under a family of specification
  functions `Fs N` (a bound), meets its specification under every `Fs N` (induction on `N`);
  callees are assumed for calls from a store with the same functions (`fspecIn`, `CallsOK`);
* callees with globals: a callee may use a prefix of the caller's globals; `callStep`
  binds its entry globals to the caller's current values and its final globals to fresh names;
  variants may name globals and read the memory at entry (`varOK`, `Tm.curFree`);
* `gen_sound` (any code, labels and continuation, either reading), `step1_sound`, `sound_call`,
  `postOf_mono` (the postcondition is stable when the environment grows above the next fresh
  variable: what keeps the head values of a loop, and so its variant bound, fixed during an
  iteration).

**Globals**: `FnSpec.globals` lists the module's integer globals
`0, …, k - 1` the function reads and writes; the generator keeps them as symbolic locals after the
declared ones (fresh names on `global.set`, havoc at loop heads like locals; callees may not use
globals), `fspec`'s precondition states their entry values (`GlobOk`: distinct addresses, values
the variables `params.length + g`) and its postcondition the final store
(`setGs (upd S s m B') m G`, the final values `G` after the results in the postcondition's
placeholders). Store lemmas in `Silmaril.Proofs.Wasm.Auto2.VCGen.Glob`, `global.get`/`global.set` in
`Step` (`sound_globalGet`, `sound_globalSet`).

## Tactics

* **`vcgen4_reduce`**: on a goal `AllValid F l` with `l` closed (typically
  `genFunc S code fuel`), computes the list of conditions by `Meta.reduce` and replaces `l` by
  it, through an auxiliary lemma checked by the kernel (as `vcgen_reduce` of `Silmaril.Wasm.Auto.VCGen`);
* **`vcgen4`**: `vcgen4_reduce`, then unfold the denotation of the conditions with `simp only`,
  split them into one goal each and name the variables (`ρ.e32 i` is `vi`, `ρ.e64 i` is `wi`,
  memory variable `ρ.mem i` is `Mi`; `M0` is the memory at entry), as `vcgen2`.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCGen

open Lean Elab Tactic Meta in
/-- Compute the conditions of a closed list `l` in a goal `AllValid F l` (see the module
docstring). -/
elab "vcgen4_reduce" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let some (fns, e) := tgt.app2? ``AllValid
      | throwError "vcgen4_reduce: the goal is not `AllValid F l`"
    if e.hasFVar || e.hasMVar then
      throwError "vcgen4_reduce: the list of conditions must be closed"
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
macro "vcgen4_den" : tactic => `(tactic| (
  simp only [Silmaril.Wasm.Auto2.VCGen.AllValid, Silmaril.Wasm.Auto2.VCGen.Valid,
    Silmaril.Wasm.Auto2.VCGen.Fm.den, Silmaril.Wasm.Auto2.VCGen.Tm.den, Silmaril.Wasm.Auto2.VCGen.Env.get,
    Silmaril.Wasm.Auto2.VCGen.Fns.app1, Silmaril.Wasm.Auto2.VCGen.Fns.app2,
    Silmaril.Wasm.Auto.VCGen.litT, Silmaril.Wasm.Auto.VCGen.unT, Silmaril.Wasm.Auto.VCGen.binT,
    Silmaril.Wasm.Auto.VCGen.relP, Silmaril.Wasm.Auto.VCGen.unW, Silmaril.Wasm.Auto.VCGen.binW,
    Silmaril.Wasm.Auto.VCGen.relW, Silmaril.Wasm.Auto.VCGen.relV_ne_zero,
    Silmaril.Wasm.Auto.VCGen.eqzV_ne_zero, Silmaril.Wasm.Auto.VCGen.relV, Silmaril.Wasm.Auto.VCGen.eqzV,
    Silmaril.Wasm.Auto.VCGen.bool32_bne_zero, Silmaril.Wasm.Auto.VCGen.relB, Bool.cond_decide,
    Silmaril.Wasm.Auto.VCGen.nz32, Silmaril.Wasm.Auto.VCGen.iteT, Silmaril.Wasm.Auto.VCGen.wrapW, Silmaril.Wasm.Auto.VCGen.extSW,
    Silmaril.Wasm.Auto.VCGen.extUW, Silmaril.Wasm.Auto2.VCGen.MR.den, Silmaril.Wasm.Auto2.VCGen.ldT,
    Silmaril.Wasm.Auto2.VCGen.stT, Silmaril.Wasm.Auto2.VCGen.Tm.dens32,
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
elab "vcgen4_vars" : tactic => do
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
macro "vcgen4" : tactic =>
  `(tactic| (vcgen4_reduce; vcgen4_den; (try and_intros); all_goals try vcgen4_vars))

end Silmaril.Wasm.Auto2.VCGen
