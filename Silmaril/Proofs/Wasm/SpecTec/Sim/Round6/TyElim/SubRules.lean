module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.TyElim.SubBase

/-!
# Round 6: each rule of `Heaptype_sub` and `Deftype_sub` in `{}`

One lemma per rule: in `{}`, on the concrete `B`, the rule establishes `HsRes` (resp. `DsRes`)
on its conclusion from its premises and the claim at its relational premises (`RS`).

* `refl`, `trans` (the middle type is an image by the claim at the premises, and coherent by
  `cohH_of_heaptypeOk`), the four abstract rules, `struct`/`array`/`func` (through `Expand`,
  `expand_inv`), `def` (through `Deftype_sub`), `none`/`nofunc`/`noexn`/`noextern` (their premise
  read from the right), `bot` (the typed `heaptype` is an image, `img_heap`);
* `typeidx-l`, `typeidx-r` and the four `rec-*` rules never fire in `{}` (`TYPES` and `RECS` are
  empty);
* `Deftype_sub/refl` never fires (`$clos_deftype` has no value), `Deftype_sub/super` reads
  `$unrolldt` (on images, Core's) and its `Heaptype_sub` premise.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.TyElim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj natV headV absV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Round6.Reading
open Round6.RefOkV (SubE CohH)

variable {prof : Silmaril.Wasm.Numerics.Profile} {H : Type} {hn : H → String}
  {host : Silmaril.Wasm.Execution.Core.HostSemantics H}

local notation "𝔼" => simEnv (Prims.builtins prof hn host)

/-! ## `refl`, `trans` -/

theorem rs_refl : RS 𝔼 HsRes hsRefl := by
  intro e' halt O els σ hq a b he hp ih
  obtain ⟨-, ha, hb⟩ := concl_C ((concl_eq halt rfl) ▸ he)
  have e : a = b := ha.unique hb
  exact e ▸ ⟨fun h₁ e₁ => ⟨h₁, e₁, .heapRefl⟩, fun h₂ e₂ => ⟨h₂, e₂, .heapRefl⟩⟩

/-- `trans`, from left to right. -/
theorem trans_fwd {a m b : Value} (h₁₂ : HsRes a m) (h₂₃ : HsRes m b)
    (hok : ∀ hm : CHeapType, m = tyV hm → CohH hm) {h₁ : CHeapType} (ha : a = tyV h₁) :
    ∃ h₂ : CHeapType, b = tyV h₂ ∧ SubE h₁ h₂ :=
  have ⟨hm, em, s₁⟩ := h₁₂.1 h₁ ha
  have ⟨h₂, eb, s₂⟩ := h₂₃.1 hm em
  ⟨h₂, eb, .heapTrans (hok hm em) s₁ s₂⟩

/-- `trans`, from right to left. -/
theorem trans_bwd {a m b : Value} (h₁₂ : HsRes a m) (h₂₃ : HsRes m b)
    (hok : ∀ hm : CHeapType, m = tyV hm → CohH hm) {h₂ : CHeapType} (hb : b = tyV h₂) :
    ∃ h₁ : CHeapType, a = tyV h₁ ∧ SubE h₁ h₂ :=
  have ⟨hm, em, s₂⟩ := h₂₃.2 h₂ hb
  have ⟨h₁, ea, s₁⟩ := h₁₂.2 hm em
  ⟨h₁, ea, .heapTrans (hok hm em) s₁ s₂⟩

theorem rs_trans : RS 𝔼 HsRes hsTrans := by
  intro e' halt O els σ hq a b he hp ih
  obtain ⟨hC, ha, hb⟩ := concl_C ((concl_eq halt rfl) ▸ he)
  obtain ⟨m, hM, -⟩ := hq "heaptype'" (.varT "heaptype" []) (by simp)
  have hA := evalExp_varE_iff.1 ha
  have hB := evalExp_varE_iff.1 hb
  have h₁₂ : HsRes a m := ih_hs (ih _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (evalExp_tup3 (evalExp_var hC) (evalExp_var hA) (evalExp_var hM))
  have h₂₃ : HsRes m b := ih_hs (ih _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..)))) (evalExp_tup3 (evalExp_var hC) (evalExp_var hM) (evalExp_var hB))
  have hok : ∀ hm : CHeapType, m = tyV hm → CohH hm := fun hm em =>
    cohH_of_heaptypeOk (em ▸ prem_rule2 hC hM (hp _ (List.mem_cons_self ..)))
  exact ⟨fun h₁ => trans_fwd h₁₂ h₂₃ hok, fun h₂ => trans_bwd h₁₂ h₂₃ hok⟩

/-! ## Between abstract heap types -/

/-- An abstract heap type, as a conclusion writes it, evaluates to its image. -/
theorem ev_abs {env : Env} {ρ : VarEnv} {x : AbsHeapType} {op : MixopS}
    (hx : absV x = .case op (.tuple [])) :
    EvalExp env ρ (.caseE op (.tupE [])) (tyV (Ty.abs x : CHeapType)) := by
  show EvalExp env ρ _ (absV x)
  rw [hx]
  exact evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)

/-- A rule `C ⊢ x <: y` between two abstract heap types. -/
theorem rs_absAbs {x y : AbsHeapType} {op₁ op₂ : MixopS} (hx : absV x = .case op₁ (.tuple []))
    (hy : absV y = .case op₂ (.tuple [])) (hs : SubE (Ty.abs x : CHeapType) (Ty.abs y))
    {nm : IL.Id} {qs : List Param} {prems : List Prem} :
    RS 𝔼 HsRes (.ruleD nm qs "%|-%<:%"
      (.tupE [.varE "C", .caseE op₁ (.tupE []), .caseE op₂ (.tupE [])]) prems) := by
  intro e' halt O els σ hq a b he hp ih
  obtain ⟨-, ha, hb⟩ := concl_C ((concl_eq halt rfl) ▸ he)
  have ea : a = tyV (Ty.abs x : CHeapType) := ha.unique (ev_abs hx)
  have eb : b = tyV (Ty.abs y : CHeapType) := hb.unique (ev_abs hy)
  refine ⟨fun h₁ e₁ => ⟨_, eb, ?_⟩, fun h₂ e₂ => ⟨_, ea, ?_⟩⟩
  · rwa [heap_of_abs (e₁.symm.trans ea)]
  · rwa [heap_of_abs (e₂.symm.trans eb)]

theorem rs_eqAny : RS 𝔼 HsRes hsEqAny := rs_absAbs (x := .eq) (y := .any) rfl rfl .eqAny
theorem rs_i31Eq : RS 𝔼 HsRes hsI31Eq := rs_absAbs (x := .i31) (y := .eq) rfl rfl .i31Eq
theorem rs_structEq : RS 𝔼 HsRes hsStructEq :=
  rs_absAbs (x := .struct) (y := .eq) rfl rfl .structEq
theorem rs_arrayEq : RS 𝔼 HsRes hsArrayEq := rs_absAbs (x := .array) (y := .eq) rfl rfl .arrayEq

/-! ## Defined types below their kind -/

/-- `C ⊢ dt <: x` through `Expand dt ct`, when the kind of `ct`'s head gives `SubE dt x`. -/
theorem rs_kind {x : AbsHeapType} {op : MixopS} (hx : absV x = .case op (.tuple [])) {E : Exp}
    (hk : ∀ (d : DefType) (ct : CCompType) (w : Value), Expand d ct → w = tyV ct →
      (∀ ρ, EvalExp 𝔼 ρ E w → SubE (Ty.use (.dt d) : CHeapType) (Ty.abs x)))
    {nm : IL.Id} {qs : List Param} (hq₀ : Param.expP "deftype" (.varT "deftype" []) ∈ qs) :
    RS 𝔼 HsRes (.ruleD nm qs "%|-%<:%" (.tupE [.varE "C", .subE (.varE "deftype")
      (.varT "deftype" []) (.varT "heaptype" []), .caseE op (.tupE [])])
      [.rulePr "Expand" [] "%~~%" (.tupE [.varE "deftype", E])]) := by
  intro e' halt O els σ hq a b he hp ih
  obtain ⟨-, ha, hb⟩ := concl_C ((concl_eq halt rfl) ▸ he)
  have hD := evalExp_varE_iff.1 (evalExp_subE_iff.1 ha)
  obtain ⟨d, rfl⟩ := quant_def hq hq₀ hD
  have eb : b = tyV (Ty.abs x : CHeapType) := hb.unique (ev_abs hx)
  obtain ⟨v, hv, hdv⟩ := prem_rule (hp _ (List.mem_singleton_self _))
  obtain ⟨v₁, w, rfl, h₁, h₂⟩ := RefOkV.evalExp_tup2_inv hv
  obtain rfl : v₁ = tyV d := h₁.unique (evalExp_var hD)
  obtain ⟨ct, hct, rfl⟩ := expand_inv hdv
  have hs := hk d ct _ hct rfl _ h₂
  refine ⟨fun h₁ e₁ => ⟨_, eb, ?_⟩, fun h₂ e₂ => ⟨Ty.use (.dt d), rfl, ?_⟩⟩
  · rwa [heap_of_def e₁.symm]
  · rwa [heap_of_abs (e₂.symm.trans eb)]

theorem rs_struct : RS 𝔼 HsRes hsStruct :=
  rs_kind (x := .struct) rfl (fun d ct w hct hw ρ hE => by
    obtain ⟨u, -, rfl⟩ := evalExp_caseE_iff.1 hE
    cases ct with
    | struct fs => exact .defStruct hct
    | _ => simp [tyV] at hw) (by simp)

theorem rs_array : RS 𝔼 HsRes hsArray :=
  rs_kind (x := .array) rfl (fun d ct w hct hw ρ hE => by
    obtain ⟨u, -, rfl⟩ := evalExp_caseE_iff.1 hE
    cases ct with
    | array f => exact .defArray hct
    | _ => simp [tyV] at hw) (by simp)

theorem rs_func : RS 𝔼 HsRes hsFunc :=
  rs_kind (x := .func) rfl (fun d ct w hct hw ρ hE => by
    obtain ⟨u, -, rfl⟩ := evalExp_caseE_iff.1 hE
    cases ct with
    | func ps rs => exact .defFunc hct
    | _ => simp [tyV] at hw) (by simp)

/-! ## `def` -/

theorem rs_def : RS 𝔼 HsRes hsDef := by
  intro e' halt O els σ hq a b he hp ih
  obtain ⟨hC, ha, hb⟩ := concl_C ((concl_eq halt rfl) ▸ he)
  have hA := evalExp_varE_iff.1 (evalExp_subE_iff.1 ha)
  have hB := evalExp_varE_iff.1 (evalExp_subE_iff.1 hb)
  obtain ⟨d₁, d₂, rfl, rfl, hs⟩ : DsRes a b := ih_ds (ih _ (List.mem_singleton_self _))
    (evalExp_tup3 (evalExp_var hC) (evalExp_var hA) (evalExp_var hB))
  refine ⟨fun h₁ e₁ => ⟨.use (.dt d₂), rfl, ?_⟩, fun h₂ e₂ => ⟨.use (.dt d₁), rfl, ?_⟩⟩
  · rw [heap_of_def e₁.symm]; exact .defDef hs
  · rw [heap_of_def e₂.symm]; exact .defDef hs

/-! ## Rules that never fire in `{}` -/

theorem rs_idxL : RS 𝔼 HsRes hsIdxL := by
  intro e' halt O els σ hq a b he hp ih
  obtain ⟨hC, -, -⟩ := concl_C ((concl_eq halt rfl) ▸ he)
  obtain ⟨v, hv, -⟩ := prem_rule (hp _ (List.mem_singleton_self _))
  obtain ⟨_, _, _, _, _, h₂, _⟩ := RefOkV.evalExp_tup3_ex hv
  exact absurd (evalExp_subE_iff.1 h₂) (not_evalExp_types0 hC)

theorem rs_idxR : RS 𝔼 HsRes hsIdxR := by
  intro e' halt O els σ hq a b he hp ih
  obtain ⟨hC, -, -⟩ := concl_C ((concl_eq halt rfl) ▸ he)
  obtain ⟨v, hv, -⟩ := prem_rule (hp _ (List.mem_singleton_self _))
  obtain ⟨_, _, _, _, _, _, h₃⟩ := RefOkV.evalExp_tup3_ex hv
  exact absurd (evalExp_subE_iff.1 h₃) (not_evalExp_types0 hC)

/-- A rule at `REC i` with one `if` premise on `C.RECS[i]`. -/
theorem rs_rec {nm : IL.Id} {qs : List Param} {e₂ e₃ E : Exp}
    (hno : hasOptNil (.tupE [.varE "C", e₂, e₃]) = false) :
    RS 𝔼 HsRes (.ruleD nm qs "%|-%<:%" (.tupE [.varE "C", e₂, e₃])
      [.ifPr (.cmpE .eqOp .boolT (.idxE (.dotE (.varE "C") "RECS") (.varE "i")) E)]) := by
  intro e' halt O els σ hq a b he hp ih
  obtain ⟨hC, -, -⟩ := concl_C ((concl_eq halt hno) ▸ he)
  exact absurd (hp _ (List.mem_singleton_self _)) (not_dpremB_recs0 hC)

theorem rs_recStruct : RS 𝔼 HsRes hsRecStruct := rs_rec rfl
theorem rs_recArray : RS 𝔼 HsRes hsRecArray := rs_rec rfl
theorem rs_recFunc : RS 𝔼 HsRes hsRecFunc := rs_rec rfl
theorem rs_recSub : RS 𝔼 HsRes hsRecSub := rs_rec rfl

/-! ## `none`, `nofunc`, `noexn`, `noextern` -/

/-- `heaptype =/= BOT`, inverted. -/
theorem ne_bot_of_prem {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {v : Value}
    (hv : ρ.findVal? "heaptype" = some v)
    (h : DPremB env O els ρ (.ifPr (.cmpE .neOp .boolT (.varE "heaptype")
      (.caseE "BOT" (.tupE []))))) : v ≠ .case "BOT" (.tuple []) := by
  cases h with
  | ifPr he =>
    obtain ⟨v₁, v₂, h₁, h₂, h₃⟩ := evalExp_cmpE_iff.1 he
    have e₁ : v₁ = v := Option.some.inj ((evalExp_varE_iff.1 h₁).symm.trans hv)
    have e₂ : v₂ = .case "BOT" (.tuple []) :=
      h₂.unique (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
    have hne : v₁ ≠ v₂ := by simpa [cmpValues] using h₃
    exact e₁ ▸ e₂ ▸ hne

/-- A heap type whose image is not `BOT` is not `BOT`. -/
theorem ne_bot {h : CHeapType} {v : Value} (e : v = tyV h) (hb : v ≠ .case "BOT" (.tuple [])) :
    h ≠ .bot := fun hh => hb (by rw [e, hh]; rfl)

/-- `C ⊢ x <: heaptype` from `heaptype <: top` and `heaptype ≠ BOT`. -/
theorem rs_bottom {x top : AbsHeapType} {opx optop : MixopS}
    (hx : absV x = .case opx (.tuple [])) (htop : absV top = .case optop (.tuple []))
    (hmk : ∀ h : CHeapType, SubE h (.abs top) → h ≠ .bot → SubE (.abs x) h)
    {nm : IL.Id} {qs : List Param} :
    RS 𝔼 HsRes (.ruleD nm qs "%|-%<:%" (.tupE [.varE "C", .caseE opx (.tupE []), .varE "heaptype"])
      [.rulePr "Heaptype_sub" [] "%|-%<:%" (.tupE [.varE "C", .varE "heaptype",
        .caseE optop (.tupE [])]), .ifPr (.cmpE .neOp .boolT (.varE "heaptype")
          (.caseE "BOT" (.tupE [])))]) := by
  intro e' halt O els σ hq a b he hp ih
  obtain ⟨hC, ha, hb⟩ := concl_C ((concl_eq halt rfl) ▸ he)
  have hB := evalExp_varE_iff.1 hb
  have ea : a = tyV (Ty.abs x : CHeapType) := ha.unique (ev_abs hx)
  have hR : HsRes b (tyV (Ty.abs top : CHeapType)) := ih_hs (ih _ (List.mem_cons_self ..))
    (evalExp_tup3 (evalExp_var hC) (evalExp_var hB) (ev_abs htop))
  have hnb := ne_bot_of_prem hB (hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine ⟨fun h₁ e₁ => ?_, fun h₂ e₂ => ⟨_, ea, ?_⟩⟩
  · obtain ⟨h, eb, hs⟩ := hR.2 (.abs top) rfl
    exact ⟨h, eb, heap_of_abs (e₁.symm.trans ea) ▸ hmk h hs (ne_bot eb hnb)⟩
  · obtain ⟨h', e', hs⟩ := hR.1 h₂ e₂
    exact hmk h₂ (heap_of_abs e'.symm ▸ hs) (ne_bot e₂ hnb)

theorem rs_none : RS 𝔼 HsRes hsNone :=
  rs_bottom (x := .none) (top := .any) rfl rfl fun _ hs hb => .none hs hb
theorem rs_nofunc : RS 𝔼 HsRes hsNofunc :=
  rs_bottom (x := .nofunc) (top := .func) rfl rfl fun _ hs hb => .nofunc hs hb
theorem rs_noexn : RS 𝔼 HsRes hsNoexn :=
  rs_bottom (x := .noexn) (top := .exn) rfl rfl fun _ hs hb => .noexn hs hb
theorem rs_noextern : RS 𝔼 HsRes hsNoextern :=
  rs_bottom (x := .noextern) (top := .extern) rfl rfl fun _ hs hb => .noextern hs hb

/-! ## `bot` -/

theorem rs_bot : RS 𝔼 HsRes hsBot := by
  intro e' halt O els σ hq a b he hp ih
  obtain ⟨-, ha, hb⟩ := concl_C ((concl_eq halt rfl) ▸ he)
  have ea : a = tyV (Ty.bot : CHeapType) :=
    ha.unique (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
  obtain ⟨h₂, rfl⟩ := quant_heap hq (x := "heaptype") (by simp) (evalExp_varE_iff.1 hb)
  refine ⟨fun h₁ e₁ => ⟨h₂, rfl, ?_⟩, fun h₂' e₂ => ⟨.bot, ea, .bot⟩⟩
  rw [show h₁ = .bot from tyV_inj _ _ (e₁.symm.trans ea)]
  exact .bot

end Silmaril.Wasm.SpecTec.Sim.Round6.TyElim
