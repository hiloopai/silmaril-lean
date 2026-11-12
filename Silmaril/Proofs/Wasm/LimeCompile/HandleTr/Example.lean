module

public import Silmaril.Proofs.Wasm.LimeCompile.HandleTr.Fwd
public import Silmaril.Wasm.LimeCompile.Agree.Thms
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# The `externref` identity: a witness, and the refutation of `Handle.HandleCorrectOn`

`idExtern` is `(func (export "id") (param externref) (result externref) local.get 0)`.

* `idExtern_valid`, `idExtern_tgt_valid`: it and its rewrite validate (silmaril-lean's
  validator, by `decide`);
* `compile_idExtern`: the compiler returns the Lime1 reading of `tgtM idExtern`
  (`(func (export "id") (param i32) (result i32) local.get 0)`), so `fwdFrag_idExtern`: the
  forwarder fragment is not empty, and the compiler is not the identity on it;
* `sessionRel_length`: behaviours related by `BehRel` (either direction) form sessions of equal
  length (the `ub` rule never applies);
* **`not_handleCorrectOn`**: `Handle.HandleCorrectOn` fails for the compiler on `idExtern`.
  Take the handle table `[ref.func 1]` and the empty store: the target accepts the handle `0`
  (an `i32`) and returns, while the source rejects `ref.func 1` (no function at address `1`), so
  its session stops; no target observation is related to the source's.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.HandleTr

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen (exportFunc? Session SessionRel moduleObs closedHost)
open Silmaril.Wasm.LimeCompile Silmaril.Wasm.LimeCompile.HandleTr
open Silmaril.Wasm.LimeCompile.Handle (BehRel)

/-- `externref`. -/
abbrev externrefT : ValType := .ref ⟨true, .abstract .extern⟩

/-- **The `externref` identity.** -/
def idExtern : Module where
  types := [⟨[⟨true, [], .func ⟨[externrefT], [externrefT]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨⟨0, by decide⟩⟩]⟩]
  exports := [⟨"id", .func ⟨0⟩⟩]

/-- Its 2.0 type. -/
def idTy : V2.FuncType := ⟨[.ref .externref], [.ref .externref]⟩

theorem idExtern_types : idExtern.types = [idTy].map V2.FuncType.toCoreRec := rfl

theorem idExtern_valid : ∃ mt, ModuleOk idExtern mt := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp
    (show (validate? idExtern).isSome = true by decide)
  exact ⟨mt, validate?_sound hmt⟩

theorem idExtern_tgt_valid : ∃ mt, ModuleOk (tgtM idExtern) mt := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp
    (show (validate? (tgtM idExtern)).isSome = true by decide)
  exact ⟨mt, validate?_sound hmt⟩

theorem idExtern_only : onlyFuncs idExtern = true := by decide

theorem idExtern_fwd : ∀ f ∈ idExtern.funcs, fwdFunc f = true := by decide

theorem limeView_idExtern : Preserve.limeView idExtern = none := by
  have : Lime1.Module.ofCore? idExtern = none := Option.isNone_iff_eq_none.mp (by decide)
  simp [Preserve.limeView, this]

theorem compile0_idExtern : compile0 idExtern = Lime1.Module.ofCore? (tgtM idExtern) := by
  simp only [compile0, show importsHandleFree idExtern = true by decide, ↓reduceIte,
    Direct.compile, lowerModule_hModule idExtern_only idExtern_fwd]
  simp only [show Direct.funcrefElemsB (tgtM idExtern) = true by decide, ↓reduceIte]

/-- **The compiler on `idExtern`** is the Lime1 reading of the rewrite. -/
theorem compile_idExtern : compile idExtern = Lime1.Module.ofCore? (tgtM idExtern) := by
  unfold compile Preserve.limePres
  rw [limeView_idExtern]
  exact compile0_idExtern

theorem compile_idExtern_some : ∃ l, compile idExtern = some l ∧ l.toCore = tgtM idExtern := by
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp
    (show (Lime1.Module.ofCore? (tgtM idExtern)).isSome = true by decide)
  refine ⟨l, compile_idExtern.trans hl, ?_⟩
  exact compile0_fwd idExtern_only idExtern_fwd (compile0_idExtern.trans hl)

/-- **The forwarder fragment is not empty.** -/
theorem fwdFrag_idExtern : FwdFrag idExtern := by
  refine ⟨idExtern_only, idExtern_fwd, ⟨[idTy], idExtern_types⟩, idExtern_valid, ?_⟩
  intro l hl
  obtain ⟨l', hl', ht⟩ := compile_idExtern_some
  rw [hl'] at hl
  cases hl
  rw [ht]
  exact idExtern_tgt_valid

/-! ## Sessions related by `BehRel` have equal length -/

theorem behRel_not_all {σ : List Val} {b : Behaviour Val} (h : ∀ x, BehRel σ b x) : False := by
  have h1 := h .traps
  have h2 := h .diverges
  rcases h1 with rfl | ⟨_, _, _, h1, _⟩
  · rcases h2 with h2 | ⟨_, _, h2, _, _⟩ <;> cases h2
  · cases h1

theorem sessionRel_length {σ : List Val} {bs' bs : List (Behaviour Val)}
    (h : SessionRel (fun b' b => BehRel σ b b') bs' bs) : bs'.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | ub h => exact (behRel_not_all h).elim

/-! ## The refutation -/

theorem storeOk_empty' {H : Type} : StoreOk ({} : Store H) := by
  constructor <;> intro x hx <;> cases hx

theorem refOk_func_lt {H : Type} {s : Store H} {b : Nat} {rt : CRefType}
    (h : RefOk s (.func b) rt) : b < s.funcs.length := by
  generalize hr : Ref.func b = r at h
  induction h with
  | func hf =>
    cases hr
    exact (List.getElem?_eq_some_iff.mp hf).1
  | sub _ _ _ ih => exact ih hr
  | _ => cases hr

/-- The allocation data of `idExtern` in the empty store. -/
theorem idExtern_setup :
    Setup ({} : Store Unit) idExtern [idTy] [idTy.toDefType] [(hV2FT idTy).toDefType]
      [⟨"id", .func 0⟩] :=
  ⟨idExtern_only, idExtern_fwd, idExtern_types, by decide, rfl, rfl⟩

theorem idExtern_export :
    exportFunc? (onlyInst ({} : Store Unit) idExtern [⟨"id", .func 0⟩]) "id" = some 0 := rfl

/-- The export instances of `idExtern`. -/
abbrev xiId : List ExportInst := [⟨"id", .func 0⟩]

theorem idExtern_paramsOf :
    Handle.paramsOf (Preserve.Module.exportApi idExtern) "id" = some [externrefT] := by decide

theorem idExtern_scriptRel : Handle.ScriptRel [.ref (.func 1)] (Preserve.Module.exportApi idExtern)
    [("id", [Val.i32 0])] [("id", [.ref (.func 1)])] := by
  refine .cons ⟨rfl, ?_⟩ .nil
  show match Handle.paramsOf (Preserve.Module.exportApi idExtern) "id" with
    | some ps => Handle.ArgsRel [.ref (.func 1)] ps [Val.i32 0] [.ref (.func 1)]
    | none => [Val.i32 0] = [.ref (.func 1)]
  rw [idExtern_paramsOf]
  exact .cons (.inr ⟨rfl, 0, .func 1, rfl, rfl, rfl⟩) .nil

theorem idExtern_src_func :
    (srcStore ({} : Store Unit) idExtern [idTy.toDefType] xiId).funcs[0]? =
      some ⟨idTy.toDefType, onlyInst ({} : Store Unit) idExtern xiId, .wasm ⟨⟨0⟩, [], [.localGet ⟨⟨0, by decide⟩⟩]⟩⟩ :=
  rfl

theorem idExtern_tgt_func :
    (tgtStore ({} : Store Unit) idExtern [(hV2FT idTy).toDefType] xiId).funcs[0]? =
      some ⟨(hV2FT idTy).toDefType, onlyInst ({} : Store Unit) (tgtM idExtern) xiId,
        .wasm ⟨⟨0⟩, [], [.localGet ⟨⟨0, by decide⟩⟩]⟩⟩ := rfl

/-- The source rejects the dangling function reference: its session stops. -/
theorem idExtern_src_obs : [Behaviour.returns []] ∈ moduleObs Profile.spec closedHost
    ({} : Store Unit) [] idExtern [("id", [.ref (.func 1)])] := by
  obtain ⟨⟨xtI, xtE⟩, hv⟩ := idExtern_valid
  have hv' : ModuleOk idExtern ⟨[], xtE⟩ := moduleOk_only idExtern_only hv ▸ hv
  have hstop : ∀ a, exportFunc? (onlyInst ({} : Store Unit) idExtern xiId) "id" = some a →
      ¬ InvokeOk (srcStore ({} : Store Unit) idExtern [idTy.toDefType] xiId) a [.ref (.func 1)] := by
    intro a ha hok
    have ha0 : a = 0 := Option.some.inj (ha.symm.trans idExtern_export)
    have hargs : List.Forall₂ (ValOk (srcStore ({} : Store Unit) idExtern [idTy.toDefType] xiId))
        [.ref (.func 1)] (idTy.params.map V2.ValType.toC) :=
      invokeOk_args (by rw [ha0]; exact idExtern_src_func) rfl hok
    obtain ⟨hv1, -⟩ := List.forall₂_cons.mp hargs
    cases hv1 with
    | ref hr =>
      have hlt : 1 < (srcStore ({} : Store Unit) idExtern [idTy.toDefType] xiId).funcs.length :=
        refOk_func_lt hr
      exact absurd hlt (by decide)
  exact (moduleObs_only idExtern_only).mpr ⟨_, inst_src_mk idExtern_only idExtern_types hv'
    idExtern_setup.fts idExtern_setup.xi, [], .stop hstop, rfl⟩

/-- The target accepts handle `0`: every observation has an invocation behaviour. -/
theorem idExtern_tgt_obs (bs : List (Behaviour Val))
    (hbs : bs ∈ moduleObs Profile.spec closedHost ({} : Store Unit) [] (tgtM idExtern)
      [("id", [Val.i32 0])]) : 2 ≤ bs.length := by
  obtain ⟨c', hc', bs₀, hss, hbs₀⟩ := (moduleObs_only (M := tgtM idExtern) idExtern_only).mp hbs
  obtain ⟨-, fts', xi, hf', hx, hceq⟩ := inst_tgt idExtern_only idExtern_types hc'
  have hxi : xi = xiId := Option.some.inj (hx.symm.trans idExtern_setup.xi)
  have hft : fts' = [(hV2FT idTy).toDefType] := Option.some.inj (hf'.symm.trans idExtern_setup.fts')
  have hss' : Session Profile.spec closedHost (onlyInst ({} : Store Unit) (tgtM idExtern) xiId)
      (tgtStore ({} : Store Unit) idExtern [(hV2FT idTy).toDefType] xiId) [("id", [Val.i32 0])]
      bs₀ := by
    rw [hceq, hxi, hft] at hss
    exact hss
  have hok : InvokeOk (tgtStore ({} : Store Unit) idExtern [(hV2FT idTy).toDefType] xiId) 0
      [Val.i32 0] :=
    invokeOk_of_args idExtern_tgt_func rfl (.cons (.num ⟨.int .i32, 0⟩) .nil)
  have hne : bs₀ ≠ [] := by
    cases hss' with
    | stop hstop => exact (hstop 0 idExtern_export hok).elim
    | done => simp
    | diverge => simp
  rw [hbs₀]
  obtain ⟨b, bs₁, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp

/-- **`Handle.HandleCorrectOn` (any handle table, untyped handles) fails for the compiler.** -/
theorem not_handleCorrectOn : ¬ Handle.HandleCorrectOn (· = idExtern) compile := by
  intro hc
  obtain ⟨l, hl, ht⟩ := compile_idExtern_some
  have he : Handle.EquivUpTo [.ref (.func 1)] Profile.spec closedHost l.toCore idExtern :=
    (hc idExtern l rfl hl).2 Unit [.ref (.func 1)] Profile.spec closedHost
      Agree.closedHost_parametric
  obtain ⟨bs, hbs, hrel⟩ : ∃ bs ∈ moduleObs Profile.spec closedHost ({} : Store Unit) []
      l.toCore [("id", [Val.i32 0])],
      SessionRel (fun b' b => BehRel [.ref (.func 1)] b b') [.returns []] bs :=
    he.2.obs {} [] _ _ storeOk_empty' idExtern_scriptRel _ idExtern_src_obs
  have hlen : [Behaviour.returns []].length = bs.length := sessionRel_length hrel
  have h2 : 2 ≤ bs.length := idExtern_tgt_obs bs (ht ▸ hbs)
  simp at hlen
  omega

end Silmaril.Proofs.Wasm.LimeCompile.HandleTr
