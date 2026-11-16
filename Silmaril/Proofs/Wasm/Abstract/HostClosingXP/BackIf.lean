module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackBlock

/-!
# The logged backward simulation of conditionals and `try_table` (proofs)

`case_if`, `case_try`: see `BackCtl`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {host : HostSemantics H} {tags : List TagInst} {o : GrowOracle}

/-- The check of a block, from its parts. -/
theorem chk1_block_of {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {bt : BlockType} {body : List Binaryen.BExpr} {np nr : Nat}
    (ha : blockArity mi bt = some (np, nr)) (hp : np ≤ h)
    (hb : endsAt (chkE ext F mi nl ret (nr :: labels) (some np) body) nr = true) :
    chk1E ext F mi nl ret labels h (.block bt body) = some (some (h - np + nr)) := by
  simp [chk1E, ha, hp, hb]

/-- `if` steps, host-free, to the block of its chosen arm. -/
theorem steps_if_arm {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {cv : Val}
    {b : Bool} {t el : List Binaryen.BExpr} {rest : List Admin}
    (hb : Binaryen.truthy cv = some b) :
    Steps (profile o) NH ⟨s, f, vals (cv :: stk).reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest⟩
      ⟨s, f, vals stk.reverse ++
        .plain (.block bt (Binaryen.BExpr.lowerList (if b then t else el))) :: rest⟩ := by
  obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hb
  have e : vals (Val.i32 c₀ :: stk).reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest =
      vals stk.reverse ++ [constI32 c₀,
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el))] ++ rest := by
    simp [vals, constI32]
  rw [e]
  refine .single ?_
  by_cases h0 : c₀ = 0
  · subst h0
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := NH)
      (s := s) (f := f) stk.reverse rest
      (Step.ifFalse (bt := bt) (b₁ := Binaryen.BExpr.lowerList t) (b₂ := Binaryen.BExpr.lowerList el))
  · have h1 : (c₀ != 0) = true := by simpa using h0
    simp only [h1, ↓reduceIte]
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := NH)
      (s := s) (f := f) stk.reverse rest
      (Step.ifTrue (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
        (b₂ := Binaryen.BExpr.lowerList el) h0)

section Cases

variable {s : Store H} {f : Frame} {stk : List Val} {c : Config H}
  {cs : List (Call (wasmHostSig H))} {n : Nat}

/-- **Conditionals**: the condition, then the block of the chosen arm. -/
theorem case_if (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {bt : BlockType} {cnd t el es : List Binaryen.BExpr}
    (ihc : ∀ m ≤ n, BackG tags o host m cnd)
    (ihblk : ∀ b : Bool, ∀ m ≤ n, BackG tags o host m (.block bt (if b then t else el) :: es)) :
    BackG tags o host n (.if_ bt cnd t el :: es) := by
  intro s f stk c cs ht hrun hend hnd
  have hct := typedP_ctx ht
  obtain ⟨-, labels, ret, out, hS, hc, -, hTM, hts⟩ := id ht
  have hrun₀ := hrun
  have hcode := code_if stk bt cnd t el es
  change EvRunN _ _ _ ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList
    (.if_ bt cnd t el :: es))⟩ _ _ at hrun
  rw [hcode] at hrun
  obtain ⟨l, r, cs₁, cs₂, rfl, hd, hres, hr⟩ := seq_part (cond_typedP ht) ihc hrun hend hnd
  rcases hr with hn | ⟨s₁, f₁, stk₁', m, rfl, hq, hm, hk, hst⟩
  · exact mkOut'' hH hE ht hrun₀ hend (.ifAbort hd hn) hres
  have hst' : Steps (profile o) host ⟨s, f, tcode stk (.if_ bt cnd t el :: es)⟩
      ⟨s₁, f₁, vals stk₁'.reverse ++
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
          expression (Binaryen.BExpr.lowerList es)⟩ := by
    change Steps _ _ ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList
      (.if_ bt cnd t el :: es))⟩ _
    rw [hcode]; exact hst
  have hsite := ContextTyped.steps_typed hT hct hst'
  obtain ⟨cv, stk₁, b, rfl, hb⟩ := truthy_progressH hsite
  have hcons₁ : Cons host cs₁ := (cons_append.1 (evRun_consistent (evRunN_evRun hrun₀))).1
  obtain ⟨-, t₁, a₁, -⟩ := full_run (P := profile o) hH hE hd
    (substPre_mono (close_le_goodCX hH hE) hq) hcons₁ hts
  obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, hk1⟩ := chk1_ifE h1
  obtain ⟨hoc, inv1⟩ := (arityE_of_arityP a₁) hS hco
  obtain ⟨np, nr, ha, hpn, hbt, hbe, ho⟩ := hk1 _ hoc
  have har : Binaryen.arity f₁ bt = some (np, nr) := by
    rw [arity_eq, inv1.2.1]; exact ha
  have hif := steps_if_arm (o := o) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt) (t := t)
    (el := el) (rest := expression (Binaryen.BExpr.lowerList es)) hb
  have hcodeB : vals stk₁.reverse ++ .plain (.block bt
      (Binaryen.BExpr.lowerList (if b then t else el))) :: expression (Binaryen.BExpr.lowerList es) =
      tcode stk₁ (.block bt (if b then t else el) :: es) := (code_block stk₁ bt es).symm
  rw [hcodeB] at hif
  obtain ⟨m', hm', hk'⟩ := through hif hk hend
  have hlen : (cv :: stk₁).length = stk₁.length + 1 := rfl
  have hchk : chkE (ehExt tags) s₁.funcs f₁.module f₁.locals.length ret labels
      (some stk₁.length) (.block bt (if b then t else el) :: es) = some out := by
    refine chk_inv inv1 (chk_consE.mpr ⟨_, chk1_block_of ha (by omega) ?_, ?_⟩)
    · cases b
      · exact hbe
      · exact hbt
    · rw [ho] at h2
      rw [hlen] at h2
      simpa using h2
  have htk : TypedP tags s₁ f₁ stk₁ (.block bt (if b then t else el) :: es) :=
    typedP_of (storeChk_inv inv1 hS) hchk
      (ContextTyped.steps_typed hT hsite (steps_host (by rw [← hcodeB] at hif ⊢; exact hif)))
      (by rw [inv1.2.1]; exact hTM) t₁
  obtain ⟨l₂, r₂, hd₂, hres₂, -⟩ := ihblk b m' (by omega) s₁ f₁ stk₁ c cs₂ htk hk' hend hnd
  have hres' := resX_prepend hq hres₂
  cases hd₂ with
  | blockOk har' hbody hvs hk₂ =>
    exact mkOut hH hE ht hrun₀ hend (.ifOk hd hb har' hbody hvs hk₂)
      (by simpa [List.append_assoc] using hres')
  | blockBrk har' hbody => exact mkOut hH hE ht hrun₀ hend (.ifBrk hd hb har' hbody) hres'
  | blockEsc har' hbody hesc => exact mkOut hH hE ht hrun₀ hend (.ifEsc hd hb har' hbody hesc) hres'

/-- **`try_table`**: the body in its handler and label; a thrown exception caught or rethrown by
the clauses. -/
theorem case_try (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {bt : BlockType} {cl : List Catch} {body es : List Binaryen.BExpr}
    (ihB : ∀ m ≤ n, BackG tags o host m body) (ihk : ∀ m ≤ n, BackG tags o host m es) :
    BackG tags o host n (.tryTable bt cl body :: es) := by
  intro s f stk c cs ht hrun hend hnd
  have hct := typedP_ctx ht
  obtain ⟨-, labels, ret, out, hS, hc, -, hTM, hts⟩ := id ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨ns, np, nr, -, ha, -, -, -, -⟩ := chk1_tryTableE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  obtain ⟨-, -, -, hp, hb, h2⟩ := arity_try_pre har hc
  let B := Binaryen.BExpr.lowerList body
  let E := expression (Binaryen.BExpr.lowerList es)
  have henter : Steps (profile o) NH ⟨s, f, tcode stk (.tryTable bt cl body :: es)⟩
      ⟨s, f, vals (stk.drop np).reverse ++
        [.handler nr cl [.label nr [] (vals (stk.take np).reverse ++ expression B)]] ++ E⟩ := by
    change Steps _ _ ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList
      (.tryTable bt cl body :: es))⟩ _
    rw [code_tryTable]
    exact steps_try_enter har hp E
  obtain ⟨m₀, hm₀, hk₀⟩ := through henter hrun hend
  obtain ⟨cb, N₁, cs₁, cs₂, m, rfl, hN₁, h₁, hend₁, hm, hk, hx⟩ := evRunN_try_split hk₀ hend
  have hnd₁ := nd_try hx hnd
  have htb : TypedP tags s f (stk.take np) body := try_body_typedP har ht
  obtain ⟨l₁, ⟨s₁, f₁, ob⟩, hd₁, hres₁, hok₁⟩ :=
    ihB N₁ (by omega) s f (stk.take np) cb cs₁ htb h₁ hend₁ hnd₁
  cases ob with
  | tail a' args k => exact mkOut'' hH hE ht hrun hend (.tryEsc har hd₁ trivial trivial) hres₁
  | flow fl =>
    rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
    · have hne : fl ≠ .trap := ne_trap_of_blockVals' hvs
      have hq₁ := resX_nontrap hres₁ (by simpa using hne)
      have hcons₁ : Cons host cs₁ := (cons_append.1 (evRun_consistent (evRunN_evRun hrun))).1
      obtain ⟨-, t₁, a₁, -⟩ := full_run (P := profile o) hH hE hd₁
        (substPre_mono (close_le_goodCX hH hE) hq₁) hcons₁ hts
      obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS (arityE_of_arityP a₁) hb
        (take_length_of_le hp)
      have hnr := blockVals_length hok hob hvs
      have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
        rintro ws rfl; exact length_of_ends hok hob
      rcases hok₁ with ⟨oc, he, hm'⟩ | ⟨h, -⟩
      swap
      · exact absurd (by simpa using h) hne
      obtain ⟨hs₁, hf₁, hfm⟩ := match_of_matchP hne hm'
      obtain ⟨cst, cfr, ccd⟩ := cb
      simp only at hs₁ hf₁ he hk h₁
      subst hs₁ hf₁
      have hx₁ : Steps (profile o) NH ⟨cst, cfr, [.label nr [] ccd]⟩
          ⟨cst, cfr, vals (vs.take nr).reverse⟩ := by
        simpa using exit_blockVals (P := profile o) (host := NH) (s₁ := cst) (f₁ := cfr)
          (pre := []) (rest := []) he hfm hvs hnr hnorm
      have hout : Steps (profile o) NH ⟨cst, cfr, [.handler nr cl [.label nr [] ccd]]⟩
          ⟨cst, cfr, vals (vs.take nr).reverse⟩ :=
        (Steps.handler nr cl hx₁).tail Step.handlerVals
      have hex := Steps.ctx (P := profile o) (host := NH) (stk.drop np).reverse E hout
      have hcont : vals (stk.drop np).reverse ++ vals (vs.take nr).reverse ++ E =
          tcode (vs.take nr ++ stk.drop np) es := by simp [tcode, E]
      rw [hcont] at hex
      obtain ⟨m', hm'', hk'⟩ := through hex hk hend
      have hstT : Steps (profile o) host ⟨s, f, tcode stk (.tryTable bt cl body :: es)⟩
          ⟨cst, cfr, tcode (vs.take nr ++ stk.drop np) es⟩ :=
        (steps_host henter).trans ((Steps.ctx _ _ (Steps.handler nr cl
          (Steps.label nr [] (evRunN_steps h₁)))).trans (steps_host hex))
      have htk : TypedP tags cst cfr (vs.take nr ++ stk.drop np) es :=
        typedP_of (storeChk_inv inv1 hS) (chk_after inv1 hp hnr h2)
          (ContextTyped.steps_typed hT hct hstT) (by rw [inv1.2.1]; exact hTM) t₁
      obtain ⟨l₂, r₂, hd₂, hres₂, -⟩ := ihk m' (by omega) _ _ _ c cs₂ htk hk' hend hnd
      exact mkOut hH hE ht hrun hend (.tryOk har hd₁ hvs hd₂) (resX_prepend hq₁ hres₂)
    · exact mkOut'' hH hE ht hrun hend (.tryBrk har hd₁) (.inl (resX_nontrap hres₁ (by simp)))
    · rcases fl with _ | _ | vs | _ | a <;> simp only [Binaryen.Flow.Escapes] at hesc
      · exact mkOut'' hH hE ht hrun hend (.tryEsc har hd₁ hesc trivial) hres₁
      · exact mkOut'' hH hE ht hrun hend (.tryEsc har hd₁ hesc trivial) hres₁
      · obtain ⟨rr, hrr⟩ := Cfg.Region.catches_total s₁ f₁ a cl
        have hq₁ := resX_nontrap hres₁ (by simp)
        cases rr with
        | none => exact mkOut'' hH hE ht hrun hend (.tryRethrow har hd₁ hrr) (.inl hq₁)
        | some p =>
          obtain ⟨us, l'⟩ := p
          exact mkOut'' hH hE ht hrun hend (.tryCatch har hd₁ hrr) (.inl hq₁)

end Cases

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
