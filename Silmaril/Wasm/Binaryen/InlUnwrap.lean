module

public import Silmaril.Wasm.Binaryen.InlUnwrapRun
public import Silmaril.Wasm.Binaryen.CtxRefines
public import Silmaril.Wasm.Binaryen.InlSite

@[expose] public section

/-! # Unwrapping a branch-free block

`block bt region` and `region` are interchangeable in any function body when `region` is
inside the profile, has no free branch target and no `return`
(`block_unwrap_exportEquiv`): the two run in lockstep up to the block's label, which the
region never targets, and leave the same values; a trap or exception bubbles out of the
label (`Binaryen/InlUnwrapSim.lean`). The proof is a direct simulation, not through the
`Joinable` bridge, and holds for every code-respecting typed host. The module with the
bare region is valid at the same type (`block_unwrap_valid`): the label the block adds is
never targeted, so the region's typing does not depend on it (`InstrsOk.budRelabel`).

This is the step of `outline_sound` (`Binaryen/Inline.lean`) after inlining the outlined
function back: inlining produces `block (typeIdx ty) region`.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

namespace Unwrap

/-! ## Lowering -/

theorem UIL.append {R : List Instr} : ∀ {A A' B B' : List Instr}, UIL R A A' → UIL R B B' →
    UIL R (A ++ B) (A' ++ B')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h' => .cons h (UIL.append t h')
  | _, _, _, _, .site bt t, h' => by simpa using UIL.site bt (UIL.append t h')
  | _, _, _, _, .fold bt h₁ h₂ hT hE t, h' => by simpa using UIL.fold bt h₁ h₂ hT hE (UIL.append t h')

/-- The lowered bodies with the block and with the bare region are related. -/
theorem lower_plug (K : BCtx) (bt : BlockType) (region : List BExpr) :
    UIL (BExpr.lowerList region) (BExpr.lowerList (K.plug [.block bt region]))
      (BExpr.lowerList (K.plug region)) := by
  induction K with
  | hole =>
    simpa [BCtx.plug, BExpr.lower] using
      UIL.site (R := BExpr.lowerList region) bt (UIL.nil (R := BExpr.lowerList region))
  | seq pre k post ih =>
    simpa [BCtx.plug] using UIL.append (UIL.refl (BExpr.lowerList pre))
      (UIL.append ih (UIL.refl (BExpr.lowerList post)))
  | op i pre k post ih =>
    simpa [BCtx.plug] using UIL.append (UIL.refl (BExpr.lowerList pre))
      (UIL.append ih (UIL.refl (BExpr.lowerList post ++ [i])))
  | block bt' pre k post ih =>
    simpa [BCtx.plug, BExpr.lower] using
      (UIL.cons (UI.block (bt := bt') (UIL.append (UIL.refl (BExpr.lowerList pre))
        (UIL.append ih (UIL.refl (BExpr.lowerList post))))) UIL.nil :
        UIL (BExpr.lowerList region) [_] [_])
  | loop bt' pre k post ih =>
    simpa [BCtx.plug, BExpr.lower] using
      (UIL.cons (UI.loop (bt := bt') (UIL.append (UIL.refl (BExpr.lowerList pre))
        (UIL.append ih (UIL.refl (BExpr.lowerList post))))) UIL.nil :
        UIL (BExpr.lowerList region) [_] [_])
  | ifCond bt' pre k post t e ih =>
    simpa [BCtx.plug, BExpr.lower] using UIL.append (UIL.refl (BExpr.lowerList pre))
      (UIL.append ih (UIL.refl (BExpr.lowerList post ++
        [.if_ bt' (BExpr.lowerList t) (BExpr.lowerList e)])))
  | ifThen bt' c pre k post e ih =>
    simpa [BCtx.plug, BExpr.lower] using UIL.append (UIL.refl (BExpr.lowerList c))
      (UIL.cons (UI.if_ (bt := bt') (UIL.append (UIL.refl (BExpr.lowerList pre))
        (UIL.append ih (UIL.refl (BExpr.lowerList post)))) (UIL.refl (BExpr.lowerList e)))
        UIL.nil)
  | ifElse bt' c t pre k post ih =>
    simpa [BCtx.plug, BExpr.lower] using UIL.append (UIL.refl (BExpr.lowerList c))
      (UIL.cons (UI.if_ (bt := bt') (UIL.refl (BExpr.lowerList t))
        (UIL.append (UIL.refl (BExpr.lowerList pre))
          (UIL.append ih (UIL.refl (BExpr.lowerList post))))) UIL.nil)
  | tryTable bt' cs pre k post ih =>
    simpa [BCtx.plug, BExpr.lower] using
      (UIL.cons (UI.tryTable (bt := bt') (cs := cs) (UIL.append (UIL.refl (BExpr.lowerList pre))
        (UIL.append ih (UIL.refl (BExpr.lowerList post))))) UIL.nil :
        UIL (BExpr.lowerList region) [_] [_])

/-! ## Budgets of the region -/

theorem FlatB.restrict {b : Bud} {S T : Nat → Prop} {i : Instr} (h : FlatB b S i)
    (hl : ∀ n ∈ instrLabels i, T n) : FlatB b T i := by
  cases i <;> simp_all [FlatB]

theorem InstrB.restrict {b : Bud} {S : Nat → Prop} {i : Instr} (h : InstrB b S i) :
    ∀ {T : Nat → Prop}, (∀ n ∈ instrLabels i, T n) → InstrB b T i := by
  induction h with
  | flat h => exact fun hl => .flat (FlatB.restrict h hl)
  | @block S bt body _ ih =>
    intro T hl
    rw [instrLabels_block] at hl
    have hs := shiftP_of_unbind hl
    exact .block fun j hj => ih j hj fun n hn => hs n (mem_instrsLabels.mpr ⟨j, hj, hn⟩)
  | @loop S bt body hlo _ ih =>
    intro T hl
    rw [instrLabels_loop] at hl
    have hs := shiftP_of_unbind hl
    exact .loop hlo fun j hj => ih j hj fun n hn => hs n (mem_instrsLabels.mpr ⟨j, hj, hn⟩)
  | @if_ S bt t e _ _ iht ihe =>
    intro T hl
    rw [instrLabels_if] at hl
    have hs := shiftP_of_unbind hl
    exact .if_ (fun j hj => iht j hj fun n hn =>
        hs n (List.mem_append.mpr (.inl (mem_instrsLabels.mpr ⟨j, hj, hn⟩))))
      (fun j hj => ihe j hj fun n hn =>
        hs n (List.mem_append.mpr (.inr (mem_instrsLabels.mpr ⟨j, hj, hn⟩))))

/-- The lowered region stays inside `budU` with no free branch target. -/
theorem region_bud {region : List BExpr} (hfree : BExpr.labelsList region = [])
    (hany : (effectsList region).any = false) (hret : (effectsList region).branchesOut = false) :
    ∀ j ∈ BExpr.lowerList region, InstrB budU (fun _ => False) j := by
  have hE : EffLe (effectsList region) budU (· ∈ (effectsList region).breakTargets) :=
    ⟨hany, fun _ _ => by simp [budU], fun _ _ => by simp [budU], fun _ => by simp [budU],
      fun _ => by simp [budU], fun _ => by simp [budU], fun h => by simp [hret] at h,
      fun _ => by simp [budU], fun _ hl => hl⟩
  intro j hj
  refine InstrB.restrict (instrB_lowerList region hE j hj) fun n hn => ?_
  have : n ∈ instrsLabels (BExpr.lowerList region) := mem_instrsLabels.mpr ⟨j, hj, hn⟩
  have e : instrsLabels (BExpr.lowerList region) = [] := hfree
  rw [e] at this
  cases this

/-! ## Typing -/

/-- **The bare region may replace the block** in every well-formed context. -/
theorem tyRepl_unwrap {bt : BlockType} {R : List Instr}
    (hB : ∀ j ∈ R, InstrB budU (fun _ => False) j) : TyRepl [Instr.block bt R] R :=
  TyRepl.of_instr fun C it hC hi => by
    cases hi with
    | block hbt hb =>
      rename_i t₁ t₂ xs
      have h1 := InstrsOk.budRelabel (b := budU) (by simp [budU]) hb (S := fun _ => False)
        (lb := C.labels) C.return_ hB (fun _ hn => hn.elim)
      have e : (C.withLabel t₂).reshape (C.withLabel t₂).locals C.labels C.return_ = C := by
        cases C; rfl
      rw [e] at h1
      exact .sub h1 ⟨ResultSub.refl _ _, ResultSub.refl _ _, fun x hx _ => by simp at hx⟩
        (InstrsOk.regular hC (.instr (.block hbt hb)))
    | _ => rename_i h; cases h

/-- Validity transported along `TyRepl` of a function body, at the same type. -/
theorem ok_transfer_mt {m : BModule} {g : Nat} {B B' : List BExpr}
    (h : TyRepl (BExpr.lowerList B) (BExpr.lowerList B')) {mt : CModuleType}
    (hm : ModuleOk (m.withBody g B).lower mt) : ModuleOk (m.withBody g B').lower mt := by
  have := ModuleOk.replaceFuncs
    (fs := (modifyAt (fun f => { f with body := B' }) g m.funcs).map
      (Declaration.Func.mapBody BExpr.lowerList)) hm (fun C fdts hC hf =>
        forall₂_map_modifyAt (fun x d hx => by
          simpa [Declaration.Func.mapBody] using
            FuncOk.replaceBody hC (body' := BExpr.lowerList B') hx
              (by simpa [Declaration.Func.mapBody] using h)) g hf)
  exact this

/-! ## Instances -/

theorem modifyAt_eq_set {α : Type} (F : α → α) :
    ∀ (g : Nat) (l : List α) {x : α}, l[g]? = some x → modifyAt F g l = l.set g (F x)
  | _, [], _, h => by simp at h
  | 0, a :: l, x, h => by simp at h; subst h; rfl
  | g + 1, a :: l, x, h => by
    simp only [modifyAt, List.set_cons_succ]
    rw [modifyAt_eq_set F g l (by simpa using h)]

section det

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Profile.deterministic o

theorem sr_of_alloc {R : List Instr} {M : Module} {xas : List ExternAddr} {g n₀ : Nat}
    {cL cR : Func} {c c' : Config H} (hg : M.funcs[g]? = some cL)
    (hA : InlR.FuncAlloc M xas c n₀)
    (hst : c'.store = InlS.withFuncs c.store (InlR.setCode c.store.funcs (n₀ + g) cR)) :
    ∃ dg, SR ⟨R, c.frame.module, dg, n₀ + g, cL, cR⟩ c.store c'.store := by
  obtain ⟨dg, -, hcg⟩ := hA.code g cL hg
  refine ⟨dg, ⟨hcg, ?_⟩⟩
  rw [hst]
  congr 1
  unfold InlR.setCode
  rw [InlR.modify_eq_set_of _ hcg]
  rfl

/-- **The instantiations of a module and of the module with one function's code replaced
correspond**, when the codes are related by `UIL`. -/
theorem instCorr_of_set {host : HostSemantics H} {R : List Instr} {M : Module} {g : Nat}
    {cL cR : Func} (hg : M.funcs[g]? = some cL) (hty : cR.type = cL.type)
    (hval : ∀ mt, ModuleOk M mt ↔ ModuleOk { M with funcs := M.funcs.set g cR } mt)
    (hgood : ∀ mi dg ag, PrmOk ⟨R, mi, dg, ag, cL, cR⟩) :
    InstCorr (o := o) host M { M with funcs := M.funcs.set g cR } := by
  refine ⟨fun s xas c _ hi => ?_, fun s xas c' _ hi' => ?_⟩
  · obtain ⟨n₀, c', hi', hfr, hcode, hst, hA⟩ :=
      InlR.instantiate_set hg hty (fun mt h => (hval mt).mp h) hi
    obtain ⟨dg, hSR⟩ := sr_of_alloc (R := R) hg hA hst
    exact ⟨c', _, hgood _ _ _, hi', hfr, hcode, hSR⟩
  · have hlt := (List.getElem?_eq_some_iff.mp hg).1
    have hg' : (M.funcs.set g cR)[g]? = some cR := by simp [hlt]
    have hback : ({ ({ M with funcs := M.funcs.set g cR } : Module) with
        funcs := (M.funcs.set g cR).set g cL } : Module) = M := by
      have : (M.funcs.set g cR).set g cL = M.funcs := by
        rw [List.set_set]
        apply List.ext_getElem?
        intro j
        rw [List.getElem?_set]
        by_cases hj : g = j
        · subst hj; simp [hlt, (List.getElem?_eq_some_iff.mp hg).2]
        · simp [hj]
      cases M
      simp only at this ⊢
      rw [this]
    obtain ⟨n₀, c, hi, hfr, hcode, hst, hA'⟩ :=
      InlR.instantiate_set (M := { M with funcs := M.funcs.set g cR }) hg' hty.symm
        (fun mt h => by
          rw [hback]
          obtain ⟨mt₀, h₀⟩ : ∃ mt₀, ModuleOk M mt₀ := by
            obtain ⟨xtE, xtI, hmt, -⟩ := hi'.valid
            exact ⟨_, (hval _).mpr hmt⟩
          have h₀' := (hval mt₀).mp h₀
          rw [ModuleOk.unique h h₀']
          exact h₀) hi'
    rw [hback] at hi
    obtain ⟨hA, hst'⟩ := InlR.funcAlloc_back hg hty hA' hfr hst
    obtain ⟨dg, hSR⟩ := sr_of_alloc (R := R) hg hA hst'
    exact ⟨c, _, hgood _ _ _, hi, hfr.symm, hcode.symm, hSR⟩

end det

end Unwrap

open Unwrap

theorem withBody_eq_set {m : BModule} {g : Nat} {fg : BFunc} (hfg : m.funcs[g]? = some fg)
    (B : List BExpr) : (m.withBody g B).funcs = m.funcs.set g { fg with body := B } :=
  modifyAt_eq_set _ g m.funcs hfg

/-- **Unwrapping a branch-free block keeps validity**, at the same module type. -/
theorem block_unwrap_valid_mt {m : BModule} {g : Nat} {K : BCtx} {bt : BlockType}
    {region : List BExpr} (hfree : BExpr.labelsList region = [])
    (hany : (effectsList region).any = false) (hret : (effectsList region).branchesOut = false)
    {mt : CModuleType} (hok : ModuleOk (m.withBody g (K.plug [.block bt region])).lower mt) :
    ModuleOk (m.withBody g (K.plug region)).lower mt :=
  ok_transfer_mt (TyRepl.plug K (by
    simpa [BExpr.lower] using tyRepl_unwrap (bt := bt) (region_bud hfree hany hret))) hok

/-- **Unwrapping a branch-free block is an equivalence.** In any function body of any
module, `block bt region` may be replaced by `region` when `region` is inside the profile
(`any = false`), has no free branch target (`labelsList = []`) and no `return`
(`branchesOut = false`), under every code-respecting typed host. -/
theorem block_unwrap_exportEquiv {m : BModule} {g : Nat} {K : BCtx} {bt : BlockType}
    {region : List BExpr} (hg : g < m.funcs.length)
    (hok : (m.withBody g (K.plug [.block bt region])).Ok) (hfree : BExpr.labelsList region = [])
    (hany : (effectsList region).any = false) (hret : (effectsList region).branchesOut = false)
    (o : GrowKind → Nat → Nat → Nat → Bool) {H : Type} (host : HostSemantics H)
    (hhost : HostRespectsCode host) (hhostOk : HostOk host) :
    ExportEquiv (· = ·) (Profile.deterministic o) host (m.withBody g (K.plug region)).lower
      (m.withBody g (K.plug [.block bt region])).lower := by
  obtain ⟨fg, hfg⟩ : ∃ fg, m.funcs[g]? = some fg := ⟨_, List.getElem?_eq_getElem hg⟩
  obtain ⟨mt₀, hmt₀⟩ := hok
  have hbase : ∀ B, (m.withBody g B).base = m.base := fun _ => rfl
  have hL : (m.withBody g (K.plug [.block bt region])).lower.funcs[g]? =
      some (({ fg with body := K.plug [.block bt region] } : BFunc).mapBody BExpr.lowerList) := by
    simp only [BModule.lower, withBody_eq_set hfg, List.getElem?_map]
    rw [List.getElem?_set_self hg]
    rfl
  have hRm : (m.withBody g (K.plug region)).lower =
      { (m.withBody g (K.plug [.block bt region])).lower with
        funcs := (m.withBody g (K.plug [.block bt region])).lower.funcs.set g
          (({ fg with body := K.plug region } : BFunc).mapBody BExpr.lowerList) } := by
    simp only [BModule.lower, hbase, withBody_eq_set hfg, List.map_set, List.set_set]
  rw [hRm]
  refine exportEquiv_of_instCorr hhost hhostOk (instCorr_of_set hL rfl (fun mt => ?_)
    (fun mi dg ag => ⟨rfl, lower_plug K bt region, ⟨_, region_bud hfree hany hret⟩, hfree⟩))
  rw [← hRm]
  constructor
  · exact block_unwrap_valid_mt hfree hany hret
  · intro h'
    have h₀ := block_unwrap_valid_mt hfree hany hret hmt₀
    rw [ModuleOk.unique h' h₀]
    exact hmt₀

/-- Unwrapping a branch-free block keeps validity. -/
theorem block_unwrap_valid {m : BModule} {g : Nat} {K : BCtx} {bt : BlockType}
    {region : List BExpr} (hfree : BExpr.labelsList region = [])
    (hany : (effectsList region).any = false) (hret : (effectsList region).branchesOut = false)
    (hok : (m.withBody g (K.plug [.block bt region])).Ok) : (m.withBody g (K.plug region)).Ok :=
  let ⟨mt, h⟩ := hok
  ⟨mt, block_unwrap_valid_mt hfree hany hret h⟩

end Silmaril.Wasm.Binaryen
