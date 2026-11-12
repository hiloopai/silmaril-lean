module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.PrimsCall
public import Silmaril.Wasm.SpecTec.Sim.Memory.Thms

/-!
# Round 7, the export swap: `$with_tableinst` and `$with_meminst` at a real state (unrefined)

The two excluded definitions whose bodies update `$sof(z)[.TABLES[i] = ti]` (resp. `.MEMS`). Their
one clause is `$f(z, x, y) = ($sof(z)[.A[e] = y]; $fof(z))`: a case over a pair whose first
component is an update written only at the root (`rootOnly`). `tryClauses_root`: such a clause
commutes with erasure and keeps the swap set, whenever the root `$sof(z)` evaluates (in the
clause's scope) to no record with an `EXPORTS` field. The rest of the body is checked syntax.

`callDef_root` lifts it to the call, and `callDef_withTableinst_BI`, `callDef_withMeminst_BI` apply
it to the two definitions of the fixed script (`Sim.Memory.withInstDefs_simEnv` gives their one
clause) at round 6's primitives, with the `$sof` condition as the only hypothesis.
That condition holds at a real state, whose store has no `EXPORTS` field, and fails at a module
image (`Round7.Roots.not_allIn_QC_tables`); discharging it is left to `Step`'s call sites.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)

variable {Q : Value → Prop} {gr gd : String → Bool} {env : Env}

/-- The body of a root-update clause: `(e₁[p = e₂]; e₃)` under the mixop `op`. -/
def rootBody (op : MixopS) (e₁ : Exp) (p : Path) (e₂ e₃ : Exp) : Exp :=
  .caseE op (.tupE [.updE e₁ p e₂, e₃])

/-- **The body of a root-update clause commutes with erasure**, at every fuel. -/
theorem eval_rootBody (H : Hyps Q gr gd env) {ρ : VarEnv} {op : MixopS} {e₁ e₂ e₃ : Exp}
    {p : Path} (hρ : SG Q gd ρ) (h₁ : xExp gr gd e₁ = true) (hp : xPath gr gd p = true)
    (hr : rootOnly p = true) (h₂ : xExp gr gd e₂ = true) (h₃ : xExp gr gd e₃ = true)
    (hroot : ∀ k v₁, evalExp k env ρ e₁ = .ok v₁ → ∀ gs, v₁ = .struct gs → hasExp gs = false) :
    ∀ n, ER eraseV (AllIn Q) (evalExp n env ρ (rootBody op e₁ p e₂ e₃))
      (evalExp n env (eraseScope ρ) (rootBody op e₁ p e₂ e₃))
  | 0 => by simp only [rootBody, evalExp]; exact ER.error _
  | 1 => by simp only [rootBody, evalExp]; exact ER.map _ (fun _ _ => rfl) (fun _ h => h) (ER.error _)
  | m + 2 => by
    simp only [rootBody, evalExp]
    refine ER.map (Value.case op) (fun _ _ => rfl) (fun _ h => h) ?_
    refine ER.map Value.tuple (fun vs _ => (eraseV_tuple' vs).symm)
      (fun vs h => allIn_tuple_of h) ?_
    rcases m with _ | k
    · simp only [evalExps]; exact ER.error _
    · simp only [evalExps]
      refine ER.mapM' _ fun e he => ?_
      rcases List.mem_cons.1 he with rfl | he
      · rcases k with _ | k
        · simp only [evalExp]; exact ER.error _
        · exact step_updRoot (eraseAt H k) hρ h₁ hp hr h₂ (hroot k)
      · rw [List.mem_singleton.1 he]
        exact (eraseAt H k).exp ρ _ hρ h₃

/-- **A root-update clause commutes with erasure**: its argument patterns are checked, it has no
premises, and its root evaluates, in the scope its patterns bind, to no record with an `EXPORTS`
field. -/
theorem tryClauses_root (H : Hyps Q gr gd env) {qs : List Param} {pats : List Arg} {op : MixopS}
    {e₁ e₂ e₃ : Exp} {p : Path} {ws : List ArgV} (hpats : xArgs gr gd pats = true)
    (h₁ : xExp gr gd e₁ = true) (hp : xPath gr gd p = true) (hr : rootOnly p = true)
    (h₂ : xExp gr gd e₂ = true) (h₃ : xExp gr gd e₃ = true) (hws : ∀ w ∈ ws, ArgIn Q gd w)
    (hroot : ∀ k ρ₁, matchArgs k env VarEnv.empty pats ws = .ok ρ₁ →
      ∀ k' v₁, evalExp k' env ρ₁ e₁ = .ok v₁ → ∀ gs, v₁ = .struct gs → hasExp gs = false) :
    ∀ n, ER eraseV (AllIn Q) (tryClauses n env [.defD qs pats (rootBody op e₁ p e₂ e₃) []] ws)
      (tryClauses n env [.defD qs pats (rootBody op e₁ p e₂ e₃) []] (ws.map eraseA))
  | 0 => by simp only [tryClauses]; exact ER.error _
  | n + 1 => by
    simp only [tryClauses]
    have hm := (eraseAt H n).matchArgs VarEnv.empty pats ws sg_empty hpats hws
    rw [eraseScope_empty] at hm
    refine ER.elimUndef (ER.bind hm fun ρ₀ _ hρ₀ => (eraseAt H n).premsHold ρ₀ [] hρ₀ rfl)
      (fun ρ₁ hρ₁ hsg => ?_) fun _ => ?_
    · refine eval_rootBody H hsg h₁ hp hr h₂ h₃ (fun k v₁ hv₁ => ?_) n
      have hb : ∃ ρ₀, matchArgs n env VarEnv.empty pats ws = .ok ρ₀ ∧
          premsHold n env ρ₀ [] = .ok ρ₁ := by
        cases hma : matchArgs n env VarEnv.empty pats ws with
        | error e => rw [hma] at hρ₁; cases hρ₁
        | ok ρ₀ => rw [hma] at hρ₁; exact ⟨ρ₀, rfl, hρ₁⟩
      obtain ⟨ρ₀, hma, hph⟩ := hb
      have hρ : ρ₁ = ρ₀ := by
        rcases n with _ | n
        · simp [premsHold] at hph
        · simp only [premsHold, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hph
          exact hph.symm
      subst hρ
      exact hroot n ρ₁ hma k v₁ hv₁
    · rcases n with _ | n
      · simp only [tryClauses]; exact ER.error _
      · simp only [tryClauses]; exact ER.error _


/-- **A call of a root-update definition commutes with erasure**, given that its primitive fallback
does and that the root of its clause evaluates to no record with an `EXPORTS` field at every
argument list the call can produce. -/
theorem callDef_root (H : Hyps Q gr gd env) {x : IL.Id} {pats : List Arg} {op : MixopS}
    {e₁ e₂ e₃ : Exp} {p : Path} (hcl : State.HasClause1 env x pats (rootBody op e₁ p e₂ e₃))
    (hpats : xArgs gr gd pats = true) (h₁ : xExp gr gd e₁ = true) (hp : xPath gr gd p = true)
    (hr : rootOnly p = true) (h₂ : xExp gr gd e₂ = true) (h₃ : xExp gr gd e₃ = true)
    (hb : ∀ ws, (∀ w ∈ ws, ArgIn Q gd w) →
      env.builtins.call x (ws.map eraseA) = (env.builtins.call x ws).map eraseV ∧
        ∀ u, env.builtins.call x ws = some u → AllIn Q u)
    {ρ : VarEnv} {l : List Arg} (hρ : SG Q gd ρ) (hρx : ρ.findDef? x = none)
    (hl : xArgs gr gd l = true)
    (hroot : ∀ k ws, evalArgs k env ρ l = .ok ws → ∀ k' ρ₁,
      matchArgs k' env VarEnv.empty pats ws = .ok ρ₁ →
        ∀ k'' v₁, evalExp k'' env ρ₁ e₁ = .ok v₁ → ∀ gs, v₁ = .struct gs → hasExp gs = false) :
    ∀ n, ER eraseV (AllIn Q) (callDef n env ρ x l) (callDef n env (eraseScope ρ) x l)
  | 0 => by simp only [callDef]; exact ER.error _
  | n + 1 => by
    simp only [callDef, eraseScope_findDef, hρx, Option.getD_none]
    refine ER.bind ((eraseAt H n).args ρ l hρ hl) fun ws hws_eq hws => ?_
    obtain ⟨ps, t, q, hd⟩ := hcl
    simp only [hd, Res.ofOption_some, bind, Except.bind]
    refine ER.elimUndef (tryClauses_root H hpats h₁ hp hr h₂ h₃ hws (hroot n ws hws_eq) n)
      (fun v _ hv => ER.ok hv) fun _ => ?_
    obtain ⟨hb₁, hbA⟩ := hb ws hws
    exact ER.ofOption hb₁ hbA

/-- **The primitive fallback commutes with erasure** at round 6's primitives, away from
`$hostcall`, `$blocktype_`, `$sx` and `$utf8`. -/
theorem builtins_erase_BI {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {x : IL.Id} (h₁ : x ≠ "hostcall")
    (h₂ : x ≠ "blocktype_") (h₃ : x ≠ "sx") (h₄ : x ≠ "utf8") (ws : List ArgV) :
    (utf8Env (Round4Int.BI P hn host)).builtins.call x (ws.map eraseA) =
        ((utf8Env (Round4Int.BI P hn host)).builtins.call x ws).map eraseV ∧
      ∀ u, (utf8Env (Round4Int.BI P hn host)).builtins.call x ws = some u → AllIn Q u := by
  have hb : ∀ ws, (utf8Env (Round4Int.BI P hn host)).builtins.call x ws =
      Prims.call P hn host x ws := fun ws => by
    show (if x = "utf8" then Round6.MemSimd.utf8Call ws else Prims.call P hn host x ws) = _
    rw [ite_eq_right h₄]
  rw [hb, hb]
  exact erase_of_oks (oks_call P hn host h₁ h₂ h₃)

theorem hasClause1_utf8Env {B : Builtins} {x : IL.Id} {pats : List Arg} {body : Exp}
    (hx : x ≠ "utf8") (h : State.HasClause1 (simEnv B) x pats body) :
    State.HasClause1 (utf8Env B) x pats body := by
  obtain ⟨ps, t, q, h⟩ := h
  exact ⟨ps, t, q, by rw [findDef?_utf8Env_of_ne B hx, h]⟩

theorem gdE_sof : gdE "sof" = true := by decide +kernel
theorem gdE_fof : gdE "fof" = true := by decide +kernel

theorem xExp_withInstBody (F : AtomS) (y : IL.Id) (hF : F ≠ "EXPORTS") :
    xExp grE gdE (.callE "sof" [.expA (.varE "z")]) = true ∧
      xPath grE gdE (.idxP (.dotP .rootP F) (State.modAddr F)) = true ∧
      rootOnly (.idxP (.dotP .rootP F) (State.modAddr F)) = true ∧
      xExp grE gdE (.varE y) = true ∧ xExp grE gdE (.callE "fof" [.expA (.varE "z")]) = true := by
  simp [xExp, xArgs, xArg, xPath, rootOnly, State.modAddr, State.idxPayload, gdE_sof, gdE_fof, hF]

/-- **`$with_tableinst` at round 6's primitives** commutes with erasure, given the `$sof`
condition. -/
theorem callDef_withTableinst_BI {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) (HQ : Hyps Q grE gdE (utf8Env (Round4Int.BI P hn host)))
    {ρ : VarEnv} {l : List Arg} (hρ : SG Q gdE ρ) (hρx : ρ.findDef? "with_tableinst" = none)
    (hl : xArgs grE gdE l = true)
    (hroot : ∀ k ws, evalArgs k (utf8Env (Round4Int.BI P hn host)) ρ l = .ok ws → ∀ k' ρ₁,
      matchArgs k' (utf8Env (Round4Int.BI P hn host)) VarEnv.empty (Memory.zxyPat "ti") ws = .ok ρ₁ →
        ∀ k'' v₁, evalExp k'' (utf8Env (Round4Int.BI P hn host)) ρ₁
          (.callE "sof" [.expA (.varE "z")]) = .ok v₁ → ∀ gs, v₁ = .struct gs → hasExp gs = false) :
    ∀ n, ER eraseV (AllIn Q) (callDef n (utf8Env (Round4Int.BI P hn host)) ρ "with_tableinst" l)
      (callDef n (utf8Env (Round4Int.BI P hn host)) (eraseScope ρ) "with_tableinst" l) := by
  obtain ⟨h₁, hp, hr, h₂, h₃⟩ := xExp_withInstBody "TABLES" "ti" (by decide)
  exact callDef_root HQ
    (hasClause1_utf8Env (by decide) (Memory.withInstDefs_simEnv _).withTableinst)
    (by simp [xArgs, xArg, xExp]) h₁ hp hr h₂ h₃
    (fun ws _ => builtins_erase_BI P hn host (by decide) (by decide) (by decide) (by decide) ws)
    hρ hρx hl hroot

/-- **`$with_meminst` at round 6's primitives** commutes with erasure, given the `$sof`
condition. -/
theorem callDef_withMeminst_BI {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) (HQ : Hyps Q grE gdE (utf8Env (Round4Int.BI P hn host)))
    {ρ : VarEnv} {l : List Arg} (hρ : SG Q gdE ρ) (hρx : ρ.findDef? "with_meminst" = none)
    (hl : xArgs grE gdE l = true)
    (hroot : ∀ k ws, evalArgs k (utf8Env (Round4Int.BI P hn host)) ρ l = .ok ws → ∀ k' ρ₁,
      matchArgs k' (utf8Env (Round4Int.BI P hn host)) VarEnv.empty (Memory.zxyPat "mi") ws = .ok ρ₁ →
        ∀ k'' v₁, evalExp k'' (utf8Env (Round4Int.BI P hn host)) ρ₁
          (.callE "sof" [.expA (.varE "z")]) = .ok v₁ → ∀ gs, v₁ = .struct gs → hasExp gs = false) :
    ∀ n, ER eraseV (AllIn Q) (callDef n (utf8Env (Round4Int.BI P hn host)) ρ "with_meminst" l)
      (callDef n (utf8Env (Round4Int.BI P hn host)) (eraseScope ρ) "with_meminst" l) := by
  obtain ⟨h₁, hp, hr, h₂, h₃⟩ := xExp_withInstBody "MEMS" "mi" (by decide)
  exact callDef_root HQ
    (hasClause1_utf8Env (by decide) (Memory.withInstDefs_simEnv _).withMeminst)
    (by simp [xArgs, xArg, xExp]) h₁ hp hr h₂ h₃
    (fun ws _ => builtins_erase_BI P hn host (by decide) (by decide) (by decide) (by decide) ws)
    hρ hρx hl hroot


/-! ## The root condition at a real state -/

theorem findVal?_bindVal_ne {ρ : VarEnv} {x y : IL.Id} {v : Value} (h : x ≠ y) :
    (ρ.bindVal x v).findVal? y = ρ.findVal? y := by
  simp only [VarEnv.bindVal, VarEnv.findVal?, Map.bind]
  split
  · rfl
  · simp [Map.find?, h]

theorem findVal?_bindVal_self {ρ : VarEnv} {x : IL.Id} {v : Value} (h : x ≠ "_") :
    (ρ.bindVal x v).findVal? x = some v := by
  simp [VarEnv.bindVal, VarEnv.findVal?, Map.bind, h]

theorem matchArg_varE_ok {k : Nat} {ρ ρ' : VarEnv} {y : IL.Id} {v : Value}
    (h : matchArg k env ρ (.expA (.varE y)) (.val v) = .ok ρ') :
    (ρ.findVal? y = some v ∧ ρ' = ρ) ∨ (ρ.findVal? y = none ∧ ρ' = ρ.bindVal y v) := by
  rcases k with _ | k
  · simp [matchArg] at h
  simp only [matchArg] at h
  split at h
  · rcases k with _ | k
    · simp [matchExp] at h
    simp only [matchExp] at h
    split at h
    · rename_i w hw
      split at h
      · rename_i hwv
        cases h
        exact Or.inl ⟨hwv ▸ hw, rfl⟩
      · cases h
    · rename_i hw
      cases h
      exact Or.inr ⟨hw, rfl⟩
  · cases h

theorem matchArgs_cons_ok {k : Nat} {ρ ρ' : VarEnv} {a : Arg} {l : List Arg} {w : ArgV}
    {ws : List ArgV} (h : matchArgs k env ρ (a :: l) (w :: ws) = .ok ρ') :
    ∃ k' ρ'', matchArg k' env ρ a w = .ok ρ'' ∧ matchArgs k' env ρ'' l ws = .ok ρ' := by
  rcases k with _ | k
  · simp [matchArgs] at h
  simp only [matchArgs, Res.bind_eq_ok] at h
  obtain ⟨ρ'', h₁, h₂⟩ := h
  exact ⟨k, ρ'', h₁, h₂⟩

/-- Matching `z, x, y` binds `z` to the first argument and no definition variable. -/
theorem matchArgs_zxy {k : Nat} {y : IL.Id} {Z X Y : Value} {ρ₁ : VarEnv} (hy : y ≠ "z")
    (h : matchArgs k env VarEnv.empty (Memory.zxyPat y) [.val Z, .val X, .val Y] = .ok ρ₁) :
    ρ₁.findVal? "z" = some Z ∧ ρ₁.defs = [] := by
  obtain ⟨k₁, ρa, ha, h⟩ := matchArgs_cons_ok h
  obtain ⟨k₂, ρb, hb, h⟩ := matchArgs_cons_ok h
  obtain ⟨k₃, ρc, hc, h⟩ := matchArgs_cons_ok h
  have hd : ρ₁ = ρc := by
    rcases k₃ with _ | k₃
    · simp [matchArgs] at h
    · simp only [matchArgs, Except.ok.injEq] at h
      exact h.symm
  subst hd
  have h₁ : ρa.findVal? "z" = some Z ∧ ρa.defs = [] := by
    rcases matchArg_varE_ok ha with ⟨he, -⟩ | ⟨-, rfl⟩
    · simp [VarEnv.empty, VarEnv.findVal?, Map.empty] at he
    · exact ⟨findVal?_bindVal_self (by decide), rfl⟩
  have h₂ : ρb.findVal? "z" = some Z ∧ ρb.defs = [] := by
    rcases matchArg_varE_ok hb with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact h₁
    · exact ⟨(findVal?_bindVal_ne (by decide)).trans h₁.1, h₁.2⟩
  rcases matchArg_varE_ok hc with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact h₂
  · exact ⟨(findVal?_bindVal_ne (Ne.symm (Ne.symm hy))).trans h₂.1, h₂.2⟩

/-- **The root condition at a real state**: when the first argument is a state `(S; F)` whose
store `S` is no record with an `EXPORTS` field, `$sof(z)` evaluates, in the scope `z, x, y` binds,
to no such record. -/
theorem root_of_state (D : State.StateDefs env) {y : IL.Id} (hy : y ≠ "z") {S F X Y : Value}
    (hS : ∀ gs, S = .struct gs → hasExp gs = false) :
    ∀ k' ρ₁, matchArgs k' env VarEnv.empty (Memory.zxyPat y) [.val (stV S F), .val X, .val Y] =
        .ok ρ₁ → ∀ k'' v₁, evalExp k'' env ρ₁ (.callE "sof" [.expA (.varE "z")]) = .ok v₁ →
          ∀ gs, v₁ = .struct gs → hasExp gs = false := by
  intro k' ρ₁ hm k'' v₁ hv₁ gs hgs
  obtain ⟨hz, hdefs⟩ := matchArgs_zxy hy hm
  have hsof : ρ₁.findDef? "sof" = none := by
    simp [VarEnv.findDef?, hdefs]
  have he : EvalExp env ρ₁ (.callE "sof" [.expA (.varE "z")]) S :=
    State.evalExp_sof (S := S) (F := F) D hsof ⟨1, by simp [evalExp, hz]⟩
  have := EvalExp.unique ⟨k'', hv₁⟩ he
  subst this
  exact hS gs hgs


/-- The state accessors are definitions of `utf8Env B` too. -/
theorem stateDefs_utf8Env (B : Builtins) : State.StateDefs (utf8Env B) :=
  let D := State.stateDefs_simEnv B
  ⟨hasClause1_utf8Env (by decide) D.store, hasClause1_utf8Env (by decide) D.frame, hasClause1_utf8Env (by decide) D.sof, hasClause1_utf8Env (by decide) D.fof, hasClause1_utf8Env (by decide) D.local_, hasClause1_utf8Env (by decide) D.global, hasClause1_utf8Env (by decide) D.mem, hasClause1_utf8Env (by decide) D.table, hasClause1_utf8Env (by decide) D.data, hasClause1_utf8Env (by decide) D.elem, hasClause1_utf8Env (by decide) D.withLocal, hasClause1_utf8Env (by decide) D.withTable, hasClause1_utf8Env (by decide) D.withElem, hasClause1_utf8Env (by decide) D.withData, hasClause1_utf8Env (by decide) D.withGlobal⟩

/-- **`$with_tableinst` at a real state**, at round 6's primitives: when every argument list the
call produces is `(S; F), X, Y` with a store `S` that is no record with an `EXPORTS` field, the call
commutes with erasure and keeps the swap set. -/
theorem callDef_withTableinst_state {H : Type} (P : Silmaril.Wasm.Numerics.Profile)
    (hn : H → String) (host : Silmaril.Wasm.Execution.Core.HostSemantics H)
    (HQ : Hyps Q grE gdE (utf8Env (Round4Int.BI P hn host))) {ρ : VarEnv} {l : List Arg}
    (hρ : SG Q gdE ρ) (hρx : ρ.findDef? "with_tableinst" = none) (hl : xArgs grE gdE l = true)
    (hst : ∀ k ws, evalArgs k (utf8Env (Round4Int.BI P hn host)) ρ l = .ok ws →
      ∃ S F X Y, ws = [.val (stV S F), .val X, .val Y] ∧ ∀ gs, S = .struct gs → hasExp gs = false) :
    ∀ n, ER eraseV (AllIn Q) (callDef n (utf8Env (Round4Int.BI P hn host)) ρ "with_tableinst" l)
      (callDef n (utf8Env (Round4Int.BI P hn host)) (eraseScope ρ) "with_tableinst" l) :=
  callDef_withTableinst_BI P hn host HQ hρ hρx hl fun k ws hws => by
    obtain ⟨S, F, X, Y, rfl, hS⟩ := hst k ws hws
    exact root_of_state (stateDefs_utf8Env _) (by decide) hS

/-- **`$with_meminst` at a real state**, at round 6's primitives. -/
theorem callDef_withMeminst_state {H : Type} (P : Silmaril.Wasm.Numerics.Profile)
    (hn : H → String) (host : Silmaril.Wasm.Execution.Core.HostSemantics H)
    (HQ : Hyps Q grE gdE (utf8Env (Round4Int.BI P hn host))) {ρ : VarEnv} {l : List Arg}
    (hρ : SG Q gdE ρ) (hρx : ρ.findDef? "with_meminst" = none) (hl : xArgs grE gdE l = true)
    (hst : ∀ k ws, evalArgs k (utf8Env (Round4Int.BI P hn host)) ρ l = .ok ws →
      ∃ S F X Y, ws = [.val (stV S F), .val X, .val Y] ∧ ∀ gs, S = .struct gs → hasExp gs = false) :
    ∀ n, ER eraseV (AllIn Q) (callDef n (utf8Env (Round4Int.BI P hn host)) ρ "with_meminst" l)
      (callDef n (utf8Env (Round4Int.BI P hn host)) (eraseScope ρ) "with_meminst" l) :=
  callDef_withMeminst_BI P hn host HQ hρ hρx hl fun k ws hws => by
    obtain ⟨S, F, X, Y, rfl, hS⟩ := hst k ws hws
    exact root_of_state (stateDefs_utf8Env _) (by decide) hS

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
