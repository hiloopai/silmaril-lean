module

public import Silmaril.Data.IncludeBytes.Types
public import Silmaril.Prelude.Bytes.Elab.Defs
public import Silmaril.Prelude.Bytes.Native.Defs
public meta import Lean.Elab.Tactic

/-! # Raw bytes and kernel bytes

`include_bytes` elaborates a file to `IncludeBytes.decode 4096 n [c₀, c₁, …]`, a `ByteArray`
whose bytes the kernel can only reach by decoding every chunk. `Silmaril.KBytes` holds the same
literals as a tree the kernel reads quickly. This module relates the two with no evaluation:

* `decode_eq_decodeChunks`: `IncludeBytes.decode` is `KBytes.decodeChunks` (same equations).
* `kbytes_def x of_include raw` builds the canonical tree from the literals in the definition of
  `raw` and proves `x.toByteArray_eq : x.toByteArray = raw`.
* `kbytes_rel` proves `K.toByteArray = raw` for a `kbytes_def` constant `K` and a term `raw`
  that unfolds to `decode` of the same literals. Its kernel check unfolds `ofChunks` on the
  literal list and compares literals; it decodes no byte. For any other closed `raw`, it falls
  back to `edge_decide` with `bytes.eqByteArray`, which runs natively when the policy allows
  and otherwise fails, since that procedure has no kernel fallback.
-/

@[expose] public section

namespace Silmaril.IncludeBytes

theorem bytesLE_eq_unpack : ∀ k n, bytesLE k n = KBytes.unpack k n
  | 0, _ => rfl
  | k + 1, n => by simp only [bytesLE, KBytes.unpack, bytesLE_eq_unpack k (n / 256)]

theorem bytesChunks_eq_chunksBytes (c : Nat) : ∀ n cs, bytesChunks c n cs = KBytes.chunksBytes c n cs
  | _, [] => rfl
  | n, x :: xs => by
    simp only [bytesChunks, KBytes.chunksBytes, bytesLE_eq_unpack, bytesChunks_eq_chunksBytes c _ xs]

/-- Raw chunk literals and kernel chunk literals hold the same bytes. -/
theorem decode_eq_decodeChunks (c n : Nat) (cs : List Nat) :
    decode c n cs = KBytes.decodeChunks c n cs := by
  simp only [decode, KBytes.decodeChunks, bytesChunks_eq_chunksBytes]

/-- The bridge: a tree equal to the canonical tree of a raw file's literals has its bytes. -/
theorem toByteArray_eq_decode {t : KBytes} {c n : Nat} {cs : List Nat}
    (h : t = KBytes.ofChunks c n cs) : t.toByteArray = decode c n cs := by
  rw [KBytes.toByteArray_eq_decodeChunks h, decode_eq_decodeChunks]

end Silmaril.IncludeBytes

public meta section

namespace Silmaril.IncludeBytes.Kernel

open Lean Elab Command Meta Tactic

/-- `decode c n cs` with literal `c`, `n` and list `cs`, found by unfolding constants. -/
def decodeArgs? (e : Expr) (fuel : Nat := 32) : MetaM (Option (Nat × Nat × Array Nat)) := do
  let mut e := e
  for _ in [0:fuel] do
    if e.isAppOfArity ``IncludeBytes.decode 3 || e.isAppOfArity ``KBytes.decodeChunks 3 then
      let args := e.getAppArgs
      let some c := (← instantiateMVars args[0]!).nat? <|> args[0]!.rawNatLit? | return none
      let some n := (← instantiateMVars args[1]!).nat? <|> args[1]!.rawNatLit? | return none
      let some cs ← listLits? args[2]! | return none
      return some (c, n, cs)
    match ← unfoldDefinition? e with
    | some e' => e := e'.headBeta
    | none => return none
  return none
where
  listLits? (e : Expr) : MetaM (Option (Array Nat)) := do
    let mut e := e
    for _ in [0:32] do
      if let some lits := KBytes.Elab.natLits? e then return some lits
      match ← unfoldDefinition? e with
      | some e' => e := e'
      | none => return none
    return none

/-- `kbytes_def x of_include raw [computable]`. -/
syntax (name := kbytesOfInclude) "kbytes_def " ident &" of_include " ident (&" computable")? :
  command

@[command_elab kbytesOfInclude] def elabOfInclude : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[1].getId
  let raw ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[3]
  let some (c, n, cs) ← liftTermElabM <| decodeArgs? (mkConst raw)
    | throwError "kbytes_def: {raw} does not unfold to `IncludeBytes.decode c n [literals]`"
  liftCoreM <| KBytes.Elab.defineKBytes name c n cs (!stx[4].isNone)
  let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``ByteArray)
    (mkApp (mkConst ``KBytes.toByteArray) (mkConst name)) (mkConst raw)
  let pf := mkApp4 (mkConst ``IncludeBytes.toByteArray_eq_decode) (mkConst name) (mkNatLit c)
    (mkNatLit n) (mkConst (name ++ `chunks)) |>.app (mkConst (name ++ `eq_ofChunks))
  liftCoreM <| KBytes.Elab.addThm (name ++ `toByteArray_eq) ty pf

/-- Prove `K.toByteArray = raw` (see the module docstring). -/
syntax (name := kbytesRel) "kbytes_rel" : tactic

@[tactic kbytesRel] def evalKBytesRel : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := ty.eq?
    | throwError "kbytes_rel: the goal must be `K.toByteArray = raw`"
  let structural : TacticM Bool := do
    unless lhs.isAppOfArity ``KBytes.toByteArray 1 do return false
    let some k := lhs.appArg!.constName? | return false
    let env ← getEnv
    unless env.contains (k ++ `eq_ofChunks) do return false
    let some (c, n, _) ← decodeArgs? rhs | return false
    let pf := mkApp4 (mkConst ``IncludeBytes.toByteArray_eq_decode) (mkConst k) (mkNatLit c)
      (mkNatLit n) (mkConst (k ++ `chunks)) |>.app (mkConst (k ++ `eq_ofChunks))
    -- The kernel checks that `raw` unfolds to `decode c n k.chunks`, comparing literals.
    try
      let lemma ← withOptions (Elab.async.set · false) do mkAuxLemma [] ty pf
      goal.assign (mkConst lemma)
      return true
    catch _ => return false
  if ← structural then replaceMainGoal []
  else
    evalTactic (← `(tactic| exact KBytes.toByteArray_eq_of_eqByteArray _ _ (by edge_decide)))

end Silmaril.IncludeBytes.Kernel
