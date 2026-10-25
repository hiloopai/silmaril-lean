module

public import Silmaril.Wasm.Binaryen.InlAssemble
public import Silmaril.Wasm.Binaryen.Equiv
public import Silmaril.Wasm.Binaryen.InlineDefs

@[expose] public section

/-! # The inlined site: from the module to the simulation parameters

Generic facts connecting `inlineSite` (`Binaryen/Inline.lean`) to the simulation:
the lowered site is related to the original call by `IRL` (`IRL_plug`), the lowered
parameter stores and re-zeroing have the shape `PrmC` expects (`sets_lower`,
`zeros_lower`), and the instantiations of a module and of the module with one
function's code replaced correspond (`instCorr_of_set`).
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-! ## The caller's code -/

theorem IRL_append {p : Prm} : ∀ {a a' b b' : List Instr}, IRL p a a' → IRL p b b' →
    IRL p (a ++ b) (a' ++ b')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hi t, h => .cons hi (IRL_append t h)

/-- The lowered caller with the call replaced by the inlined site is related to the
original lowered caller. -/
theorem IRL_plug {p : Prm} {args body : List BExpr} (hS : p.SBL = BExpr.lowerList body) :
    ∀ K : BCtx, IRL p (BExpr.lowerList (K.plug [.op (.call p.fx) args]))
      (BExpr.lowerList (K.plug (args ++ [.block (.typeIdx p.ty) body])))
  | .hole => by
    simp only [BCtx.plug, BExpr.lowerList_cons, BExpr.lowerList_nil,
      List.append_nil, BExpr.lowerList_append, BExpr.lower]
    exact IRL_append (IRL.refl p _) (.cons (hS ▸ .site) .nil)
  | .seq pre k post => by
    simp only [BCtx.plug, BExpr.lowerList_append]
    exact IRL_append (IRL_append (IRL.refl p _) (IRL_plug hS k)) (IRL.refl p _)
  | .op i pre k post => by
    simp only [BCtx.plug, BExpr.lowerList_cons, BExpr.lower_op, BExpr.lowerList_nil,
      List.append_nil, BExpr.lowerList_append]
    exact IRL_append (IRL_append (IRL_append (IRL.refl p _) (IRL_plug hS k)) (IRL.refl p _))
      (IRL.refl p _)
  | .block bt pre k post => by
    simp only [BCtx.plug, BExpr.lowerList_cons, BExpr.lowerList_nil, List.append_nil,
      BExpr.lower]
    exact .cons (.block (by
      simp only [BExpr.lowerList_append]
      exact IRL_append (IRL_append (IRL.refl p _) (IRL_plug hS k)) (IRL.refl p _))) .nil
  | .loop bt pre k post => by
    simp only [BCtx.plug, BExpr.lowerList_cons, BExpr.lowerList_nil, List.append_nil,
      BExpr.lower]
    exact .cons (.loop (by
      simp only [BExpr.lowerList_append]
      exact IRL_append (IRL_append (IRL.refl p _) (IRL_plug hS k)) (IRL.refl p _))) .nil
  | .tryTable bt cs pre k post => by
    simp only [BCtx.plug, BExpr.lowerList_cons, BExpr.lowerList_nil, List.append_nil,
      BExpr.lower]
    exact .cons (.tryTable (by
      simp only [BExpr.lowerList_append]
      exact IRL_append (IRL_append (IRL.refl p _) (IRL_plug hS k)) (IRL.refl p _))) .nil
  | .ifCond bt pre k post t e => by
    simp only [BCtx.plug, BExpr.lowerList_cons, BExpr.lowerList_nil, List.append_nil,
      BExpr.lower]
    simp only [BExpr.lowerList_append]
    exact IRL_append (IRL_append (IRL_append (IRL.refl p _) (IRL_plug hS k)) (IRL.refl p _))
      (IRL.refl p _)
  | .ifThen bt c pre k post e => by
    simp only [BCtx.plug, BExpr.lowerList_cons, BExpr.lowerList_nil, List.append_nil,
      BExpr.lower]
    exact IRL_append (IRL.refl p _) (.cons (.if_ (by
      simp only [BExpr.lowerList_append]
      exact IRL_append (IRL_append (IRL.refl p _) (IRL_plug hS k)) (IRL.refl p _))
      (IRL.refl p _)) .nil)
  | .ifElse bt c t pre k post => by
    simp only [BCtx.plug, BExpr.lowerList_cons, BExpr.lowerList_nil, List.append_nil,
      BExpr.lower]
    exact IRL_append (IRL.refl p _) (.cons (.if_ (IRL.refl p _) (by
      simp only [BExpr.lowerList_append]
      exact IRL_append (IRL_append (IRL.refl p _) (IRL_plug hS k)) (IRL.refl p _))) .nil)

/-! ## The parameter stores and the re-zeroing -/

theorem lidx_of_ofNat? {n : Nat} {x : LocalIdx} (h : Idx.ofNat? n = some x) : lidx n = x := by
  simp [lidx, h]

theorem sets_lower {base : Nat} : ∀ {js : List Nat} {sets : List BExpr},
    List.Forall₂ (fun j e => ∃ x : LocalIdx, Idx.ofNat? (base + j) = some x ∧
      e = .op (.localSet x) []) js sets →
    BExpr.lowerList sets = js.map fun j => .localSet (lidx (base + j))
  | [], [], .nil => rfl
  | j :: js, _ :: sets, .cons ⟨x, hx, he⟩ t => by
    subst he
    simp [sets_lower t, lidx_of_ofNat? hx]

theorem sets_lower_range {base n : Nat} {sets : List BExpr}
    (h : List.Forall₂ (fun j e => ∃ x : LocalIdx, Idx.ofNat? (base + j) = some x ∧
      e = .op (.localSet x) []) (List.range n).reverse sets) :
    BExpr.lowerList sets = ((List.range n).map fun j => lidx (base + j)).reverse.map .localSet := by
  rw [sets_lower h, List.map_reverse, List.map_reverse, List.map_map]
  rfl

theorem zeroInstr_val {t : ValType} {z : Instr} (h : zeroInstr t = some z) (σ : List CTypeUse) :
    ∃ v, (Admin.plain z).val? = some v ∧ defaultVal? ((liftVal t).substAll σ) = some v := by
  rcases t with (it | ft) | v | r
  · cases h; exact ⟨_, rfl, rfl⟩
  · cases h; exact ⟨_, rfl, rfl⟩
  · cases v; cases h; exact ⟨_, rfl, rfl⟩
  · cases h

theorem zeros_lower {base np : Nat} {ls : List ValType} (σ : List CTypeUse) :
    ∀ {js : List Nat} {zeros : List BExpr},
    List.Forall₂ (fun j e => ∃ (t : ValType) (z : Instr) (x : LocalIdx), ls[j]? = some t ∧
      zeroInstr t = some z ∧ Idx.ofNat? (base + np + j) = some x ∧
      e = .op (.localSet x) [.op z []]) js zeros →
    ∃ zs zvs, BExpr.lowerList zeros = zerosI zs (js.map fun j => lidx (base + np + j)) ∧
      zs.length = js.length ∧ List.Forall₂ (fun z v => (Admin.plain z).val? = some v) zs zvs ∧
      js.map (fun j => (ls[j]?).bind fun t => defaultVal? ((liftVal t).substAll σ)) =
        zvs.map some
  | [], [], .nil => ⟨[], [], rfl, rfl, .nil, rfl⟩
  | j :: js, _ :: zeros, .cons ⟨t, z, x, ht, hz, hx, he⟩ tl => by
    subst he
    obtain ⟨zs, zvs, h1, h2, h3, h4⟩ := zeros_lower σ tl
    obtain ⟨v, hv, hd⟩ := zeroInstr_val hz σ
    refine ⟨z :: zs, v :: zvs, ?_, by simp [h2], .cons hv h3, ?_⟩
    · simp [h1, zerosI, lidx_of_ofNat? hx]
    · simp [ht, hd, h4]

theorem map_range_getElem?_bind {α β : Type} (F : α → Option β) (l : List α) :
    (List.range l.length).map (fun j => (l[j]?).bind F) = l.map F := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [List.getElem?_eq_getElem h1]

/-! ## The instantiations -/

theorem instantiate_funcs_len {P : Numerics.Profile} {host : HostSemantics H} {s : Store H}
    {M : Module} {xas : List ExternAddr} {c : Config H} (h : Instantiate P host s M xas c) :
    (ExternAddr.funcs xas).length = M.importedFunctions.length := by
  obtain ⟨xtE, xtI, hmt, hxas⟩ := h.valid
  rw [(ExternAddrOk.forall₂_funcs hxas).length_eq]
  obtain ⟨-, hi, -⟩ := hmt
  exact InlineTy.importOk_funcs_length hi

theorem modify_eq_set_of {α : Type} {l : List α} {a : Nat} {x : α} (F : α → α)
    (h : l[a]? = some x) : l.modify a F = l.set a (F x) := by
  have ha := (List.getElem?_eq_some_iff.mp h).1
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_modify, List.getElem?_set]
  by_cases hj : a = j
  · subst hj; simp [ha, (List.getElem?_eq_some_iff.mp h).2]
  · simp [hj]

theorem setCode_getElem?_ne {fs : List (FuncInst H)} {a j : Nat} {c : Func} (h : a ≠ j) :
    (setCode fs a c)[j]? = fs[j]? := by
  simp [setCode, h]

theorem setCode_getElem?_self {fs : List (FuncInst H)} {a : Nat} {c : Func} {fi : FuncInst H}
    (h : fs[a]? = some fi) : (setCode fs a c)[a]? = some ⟨fi.type, fi.module, .wasm c⟩ := by
  simp [setCode, h]

theorem setCode_setCode {fs : List (FuncInst H)} {a : Nat} {c c' : Func} :
    setCode (setCode fs a c) a c' = setCode fs a c' := by
  simp only [setCode, List.modify_modify_eq]
  rfl

theorem setCode_self {fs : List (FuncInst H)} {a : Nat} {c : Func} {d : DefType} {mi : ModuleInst}
    (h : fs[a]? = some ⟨d, mi, .wasm c⟩) : setCode fs a c = fs := by
  unfold setCode
  rw [modify_eq_set_of _ h]
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set]
  by_cases hj : a = j
  · subst hj; simp [(List.getElem?_eq_some_iff.mp h).1, (List.getElem?_eq_some_iff.mp h).2]
  · simp [hj]

theorem withFuncs_withFuncs (s : Store H) (X Y : List (FuncInst H)) :
    withFuncs (withFuncs s X) Y = withFuncs s Y := rfl

theorem withFuncs_self (s : Store H) : withFuncs s s.funcs = s := rfl

/-- The function allocation of the module with one function's code replaced back. -/
theorem funcAlloc_back {M : Module} {xas : List ExternAddr} {g n₀ : Nat} {cg cg' : Func}
    {c c' : Config H} (hg : M.funcs[g]? = some cg) (hty : cg'.type = cg.type)
    (hA : FuncAlloc { M with funcs := M.funcs.set g cg' } xas c' n₀) (hfr : c.frame = c'.frame)
    (hst : c.store = withFuncs c'.store (setCode c'.store.funcs (n₀ + g) cg)) :
    FuncAlloc M xas c n₀ ∧ c'.store = withFuncs c.store (setCode c.store.funcs (n₀ + g) cg') := by
  have hlt := (List.getElem?_eq_some_iff.mp hg).1
  have hg' : (M.funcs.set g cg')[g]? = some cg' := by simp [hlt]
  obtain ⟨d, hd, hcode⟩ := hA.code g cg' hg'
  refine ⟨⟨?_, ?_, fun j f hj => ?_⟩, ?_⟩
  · rw [hfr, hA.funcs, List.length_set]
  · rw [hfr, hA.types]
  · rw [hst, hfr]
    simp only [withFuncs_funcs]
    by_cases hjg : j = g
    · subst hjg
      rw [hg] at hj
      cases hj
      refine ⟨d, by rw [← hty]; exact hd, ?_⟩
      rw [setCode_getElem?_self hcode]
    · have hj' : (M.funcs.set g cg')[j]? = some f := by
        rw [List.getElem?_set_ne (Ne.symm hjg)]; exact hj
      obtain ⟨d', hd', hc'⟩ := hA.code j f hj'
      exact ⟨d', hd', by rw [setCode_getElem?_ne (by omega)]; exact hc'⟩
  · rw [hst, withFuncs_withFuncs]
    simp only [withFuncs_funcs]
    rw [setCode_setCode, setCode_self hcode, withFuncs_self]

section det

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

/-- The statics of an inlining site, for one instance of the module. -/
def SiteGood (M : Module) (g jf : Nat) (cg cg' cf : Func) : Prop :=
  ∀ (mi : ModuleInst) (n₀ : Nat) (fa : List Nat) (dg df : DefType),
    fa.length = M.importedFunctions.length →
    mi.funcs = fa ++ (List.range M.funcs.length).map (n₀ + ·) →
    mi.types = allocTypes M.types →
    (allocTypes M.types)[cg.type.toNat]? = some dg →
    (allocTypes M.types)[cf.type.toNat]? = some df →
    ∃ p : Prm, Good p ∧ p.mi = mi ∧ p.ag = n₀ + g ∧ p.af = n₀ + jf ∧ p.dg = dg ∧ p.df = df ∧
      p.cg = cg ∧ p.cg' = cg' ∧ p.cf = cf

theorem good_sr {M : Module} {xas : List ExternAddr} {g jf n₀ : Nat} {cg cg' cf : Func}
    {c c' : Config H} (hg : M.funcs[g]? = some cg) (hf : M.funcs[jf]? = some cf)
    (hgood : SiteGood M g jf cg cg' cf) (hA : FuncAlloc M xas c n₀)
    (hlen : (ExternAddr.funcs xas).length = M.importedFunctions.length)
    (hst : c'.store = withFuncs c.store (setCode c.store.funcs (n₀ + g) cg')) :
    ∃ p, Good p ∧ SR p c.store c'.store := by
  obtain ⟨dg, hdg, hcg⟩ := hA.code g cg hg
  obtain ⟨df, hdf, hcf⟩ := hA.code jf cf hf
  obtain ⟨p, hG, hmi, hag, haf, hpdg, hpdf, hpcg, hpcg', hpcf⟩ :=
    hgood c.frame.module n₀ _ dg df hlen hA.funcs hA.types hdg hdf
  refine ⟨p, hG, ⟨?_, ?_, ?_⟩⟩
  · rw [hag, hcg]; simp [gO, hpdg, hmi, hpcg]
  · rw [haf, hcf]; simp [fO, hpdf, hmi, hpcf]
  · rw [hst]
    congr 1
    unfold setCode newFuncs
    rw [modify_eq_set_of _ hcg, hag]
    simp [gN, hpdg, hmi, hpcg']

/-- **The instantiations of a module and of the module with one function's code replaced
correspond.** -/
theorem instCorr_of_set {host : HostSemantics H} {M : Module} {g jf : Nat} {cg cg' cf : Func}
    (hg : M.funcs[g]? = some cg) (hf : M.funcs[jf]? = some cf) (hty : cg'.type = cg.type)
    (hval : ∀ mt, ModuleOk M mt ↔ ModuleOk { M with funcs := M.funcs.set g cg' } mt)
    (hgood : SiteGood M g jf cg cg' cf) :
    InstCorr (o := o) host M { M with funcs := M.funcs.set g cg' } := by
  refine ⟨fun s xas c _ hi => ?_, fun s xas c' _ hi' => ?_⟩
  · obtain ⟨n₀, c', hi', hfr, hcode, hst, hA⟩ :=
      instantiate_set hg hty (fun mt h => (hval mt).mp h) hi
    obtain ⟨p, hG, hSR⟩ := good_sr hg hf hgood hA (instantiate_funcs_len hi) hst
    exact ⟨c', p, hG, hi', hfr, hcode, hSR⟩
  · have hlt := (List.getElem?_eq_some_iff.mp hg).1
    have hg' : (M.funcs.set g cg')[g]? = some cg' := by simp [hlt]
    have hback : ({ ({ M with funcs := M.funcs.set g cg' } : Module) with
        funcs := (M.funcs.set g cg').set g cg } : Module) = M := by
      have : (M.funcs.set g cg').set g cg = M.funcs := by
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
      instantiate_set (M := { M with funcs := M.funcs.set g cg' }) hg' hty.symm
        (fun mt h => by
          rw [hback]
          obtain ⟨mt₀, h₀⟩ : ∃ mt₀, ModuleOk M mt₀ := by
            obtain ⟨xtE, xtI, hmt, -⟩ := hi'.valid
            exact ⟨_, (hval _).mpr hmt⟩
          have h₀' := (hval mt₀).mp h₀
          rw [ModuleOk.unique h h₀']
          exact h₀) hi'
    rw [hback] at hi
    obtain ⟨hA, hst'⟩ := funcAlloc_back hg hty hA' hfr hst
    obtain ⟨p, hG, hSR⟩ := good_sr hg hf hgood hA (instantiate_funcs_len hi) hst'
    exact ⟨c, p, hG, hi, hfr.symm, hcode.symm, hSR⟩

end det

end Silmaril.Wasm.Binaryen.InlR
