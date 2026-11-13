module

public import Silmaril.Wasm.Component.Env.Thms
public import Silmaril.Wasm.Component.Passes.Flatten.Defs

/-!
# Environments under the pairing laws: proofs

Consequences of `PairLaws` for environment strategies (`ext`), used by
flattening and dead instance elimination.

* `ext_sim`: if an environment `EA` is implemented over a flat environment
  `FB` by wiring programs `σ` (`EA = FB ≫ implsH σ`), extending `EA` by a core
  instance is extending `FB` by the same instance with substituted wiring,
  under the extended `σ` (`hdist`, `psum`).
* `starP`, `gl`: a stateless left component of a pairing that only uses the
  first functions of an environment commutes with environment extensions on
  the right (`gflat`, `hdist`, `psum`).
* `flattenNodes_sim`: the simulation invariant of `flattenNodes`.
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Laws

open Silmaril.Games
open Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

local notation "ofH" => Strategy.ofHandler

/-! ## Environment strategies -/

theorem go_eq_comp (C : CoreSem M) {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (M × List Impl)) (D : Strategy X sigU),
      Linked.denU.go C e ns D = D.comp (Linked.denU.go C e ns (Strategy.id sigU))
  | e, [], D => by simp only [Linked.denU.go, Strategy.comp_id]
  | e, n :: ns, D => by
    simp only [Linked.denU.go]
    rw [go_eq_comp C _ ns (ext e D _), go_eq_comp C _ ns (ext e (Strategy.id sigU) _)]
    simp only [ext, Strategy.id_comp, Strategy.comp_assoc]

theorem go_append (C : CoreSem M) {X : Sig.{0}} :
    ∀ (e : Nat) (ns₁ ns₂ : List (M × List Impl)) (D : Strategy X sigU),
      Linked.denU.go C e (ns₁ ++ ns₂) D =
        Linked.denU.go C (linkedEnv e ns₁) ns₂ (Linked.denU.go C e ns₁ D)
  | _, [], _, _ => by simp only [List.nil_append, Linked.denU.go, linkedEnv]
  | _, _ :: ns₁, ns₂, _ => by
    simp only [List.cons_append, Linked.denU.go, linkedEnv]
    exact go_append C _ ns₁ ns₂ _

theorem linkedEnv_append :
    ∀ (e : Nat) (ns₁ ns₂ : List (M × List Impl)),
      linkedEnv e (ns₁ ++ ns₂) = linkedEnv (linkedEnv e ns₁) ns₂
  | _, [], _ => rfl
  | _, _ :: ns₁, ns₂ => linkedEnv_append _ ns₁ ns₂

theorem le_linkedEnv : ∀ (e : Nat) (ns : List (M × List Impl)), e ≤ linkedEnv e ns
  | _, [] => le_rfl
  | _, _ :: ns => (Nat.le_add_right _ _).trans (le_linkedEnv _ ns)

/-! ## Handler identities -/

theorem ofHandler_id' : ofH (Handler.id sigU) = Strategy.id sigU := Strategy.ofHandler_id _

/-- `(ofH H₁).pair X = (id.pair X) ≫ ofH (sum H₁ id)`. -/
theorem pair_left_eq (L : PairLaws) (H₁ : Handler sigU sigU) (X : Strategy sigU sigU) :
    (ofH H₁).pair X =
      ((Strategy.id sigU).pair X).comp (ofH (Handler.sum H₁ (Handler.id sigU))) := by
  rw [L.psum, Strategy.id_comp, ofHandler_id', Strategy.comp_id]

theorem splitH_comp_implsH_scoped {eB d : Nat} {σ : List Impl} (hσ : ScopedList eB σ)
    (hd : eB ≤ d) :
    (splitH d).comp (implsH eB σ) =
      (Handler.ofHom (Sig.Hom.inl sigU sigU)).comp (implsH eB σ) := by
  funext q
  simp only [Handler.comp, implsH]
  cases h : σ[q.1]? with
  | none => rfl
  | some im => exact Impl.prog_interp_splitH (hσ im (List.mem_of_getElem? h)) hd q.2

/-! ## Extension by a core instance -/

theorem coreNode_subst (C : CoreSem M) (eB : Nat) (σ : List Impl) (m : M) (args : List Impl) :
    coreNode C eB m (args.map (Impl.subst σ)) =
      (ofH (implsH eB σ)).comp (coreNode C σ.length m args) := by
  simp only [coreNode]
  rw [← Strategy.comp_assoc (ofH (implsH eB σ)), ← Strategy.ofHandler_comp, implsN_comp_subst]

theorem coreNode_mask (C : CoreSem M) (e : Nat) (m : M) (args : List Impl) :
    (coreNode C e m args).comp (ofH (maskH (CoreModule.exports m).length)) =
      coreNode C e m args := by
  simp only [coreNode, Strategy.comp_assoc]
  rw [← Strategy.ofHandler_comp, widenH_comp_maskH]

/-- **Simulation step**: extending a simulated environment by a core
instance. -/
theorem ext_sim (L : PairLaws) (C : CoreSem M) {X : Sig.{0}} {EA FB : Strategy X sigU}
    {eB : Nat} {σ : List Impl} (hσ : ScopedList eB σ)
    (h : EA = FB.comp (ofH (implsH eB σ))) (m : M) (args : List Impl) :
    ext σ.length EA (coreNode C σ.length m args) =
      (ext eB FB (coreNode C eB m (args.map (Impl.subst σ)))).comp
        (ofH (implsH (eB + (CoreModule.exports m).length)
          (σ ++ (List.range (CoreModule.exports m).length).map fun i => Impl.fwd (eB + i)))) := by
  subst h
  set w := (CoreModule.exports m).length
  set N := coreNode C σ.length m args
  set N' := coreNode C eB m (args.map (Impl.subst σ))
  have hN : N' = (ofH (implsH eB σ)).comp N := coreNode_subst C eB σ m args
  have hT : N'.comp (ofH (maskH w)) = N' := coreNode_mask C eB m _
  simp only [ext, Strategy.comp_assoc]
  congr 1
  rw [← Strategy.comp_assoc (ofH (implsH eB σ)), L.hdist, Strategy.comp_id, ← hN,
    ← Strategy.ofHandler_comp (splitH eB), splitH_comp_implsH_append hσ, Strategy.ofHandler_comp,
    ← Strategy.comp_assoc ((Strategy.id sigU).pair N'), L.psum, Strategy.id_comp, hT]

/-! ## A stateless left component commutes with extensions on the right -/

/-- One extension. -/
theorem starP (L : PairLaws) {H₁ : Handler sigU sigU} {d : Nat}
    (hH : (splitH d).comp H₁ = (Handler.ofHom (Sig.Hom.inl sigU sigU)).comp H₁)
    (N T : Strategy sigU sigU) (eA : Nat) :
    ((ofH H₁).pair ((((Strategy.id sigU).pair N).comp (ofH (splitH d))).comp T)).comp
        (ofH (splitH eA)) =
      (((Strategy.id sigU).pair N).comp (ofH (splitH d))).comp
        (((ofH H₁).pair T).comp (ofH (splitH eA))) := by
  have hg := L.gflat (Handler.id sigU) N ((ofH (splitH d)).comp T)
  rw [ofHandler_id'] at hg
  rw [pair_left_eq L, Strategy.comp_assoc ((Strategy.id sigU).pair N), ← hg,
    Strategy.comp_assoc ((Strategy.id sigU).pair N), L.psum, ← Strategy.ofHandler_comp,
    ofHandler_id', Strategy.comp_id]
  rw [Strategy.comp_assoc ((Strategy.id sigU).pair N), Strategy.comp_assoc,
    ← Strategy.comp_assoc (ofH (splitH d)), L.hdist, ← Strategy.ofHandler_comp, hH]

/-- Any number of extensions. -/
theorem gl (L : PairLaws) (C : CoreSem M) {H₁ : Handler sigU sigU} {eB₀ : Nat}
    (hH : ∀ d, eB₀ ≤ d →
      (splitH d).comp H₁ = (Handler.ofHom (Sig.Hom.inl sigU sigU)).comp H₁) (eA : Nat) :
    ∀ (e : Nat) (nn : List (M × List Impl)) (T : Strategy sigU sigU), eB₀ ≤ e →
      ((ofH H₁).pair ((Linked.denU.go C e nn (Strategy.id sigU)).comp T)).comp
          (ofH (splitH eA)) =
        (Linked.denU.go C e nn (Strategy.id sigU)).comp
          (((ofH H₁).pair T).comp (ofH (splitH eA)))
  | e, [], T, _ => by simp only [Linked.denU.go, Strategy.id_comp]
  | e, n :: nn, T, he => by
    simp only [Linked.denU.go]
    rw [go_eq_comp C _ nn]
    simp only [ext, Strategy.id_comp]
    rw [Strategy.comp_assoc, starP L (hH e he), gl L C hH eA _ nn T
      (he.trans (Nat.le_add_right _ _))]
    simp only [Strategy.comp_assoc]

/-! ## Flattening -/

theorem implsH_comp_maskH_subst (eB : Nat) (σ args : List Impl) (n : Nat) :
    ((implsH eB σ).comp (implsH σ.length args)).comp (maskH n) =
      implsH eB ((List.range n).map fun i => (args[i]?.getD Impl.trap).subst σ) := by
  rw [implsH_comp_subst, implsH_comp_maskH]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [List.getElem?_map]
  cases args[i]? <;> rfl

theorem case_comp_splitH {eB eB' : Nat} {σ : List Impl} (hσ : ScopedList eB σ) (he : eB ≤ eB')
    (ys : List Impl) :
    (Handler.case (implsH eB σ) (implsH eB' ys)).comp (splitH σ.length) =
      implsH eB' (σ ++ ys) := by
  funext q
  obtain ⟨r, x⟩ := q
  simp only [Handler.comp]
  by_cases h₁ : r < σ.length
  · show (splitH σ.length (r, x)).interp (Handler.case (implsH eB σ) (implsH eB' ys)) =
      implsH eB' (σ ++ ys) (r, x)
    have hR : (splitH σ.length (r, x)) = .call (.inl (r, x)) fun n => .pure n := by
      simp only [splitH, h₁, ↓reduceIte]
    rw [hR]
    show ((Handler.case (implsH eB σ) (implsH eB' ys) (.inl (r, x))).bind fun n => Prog.pure n)
      = _
    rw [Prog.bind_pure]
    simp only [Handler.case, implsH, List.getElem?_append_left h₁,
      List.getElem?_eq_getElem h₁]
    rw [Impl.prog_mono (hσ _ (List.getElem_mem h₁)) he]
  · have hR : (splitH σ.length (r, x)) = .call (.inr (r - σ.length, x)) fun n => .pure n := by
      simp only [splitH, h₁, ↓reduceIte]
    rw [hR]
    show ((Handler.case (implsH eB σ) (implsH eB' ys) (.inr (r - σ.length, x))).bind
      fun n => Prog.pure n) = _
    rw [Prog.bind_pure]
    simp only [Handler.case, implsH, List.getElem?_append_right (Nat.le_of_not_lt h₁)]
    rfl

theorem scoped_fwds (eB w : Nat) :
    ScopedList (eB + w) ((List.range w).map fun i => Impl.fwd (eB + i)) := by
  intro im him
  simp only [List.mem_map, List.mem_range] at him
  obtain ⟨i, hi, rfl⟩ := him
  show eB + i < eB + w
  omega

theorem ScopedList.mono {e e' : Nat} {σ : List Impl} (h : ScopedList e σ) (he : e ≤ e') :
    ScopedList e' σ := fun im him => (h im him).mono he

theorem ScopedList.append {e : Nat} {σ τ : List Impl} (h₁ : ScopedList e σ)
    (h₂ : ScopedList e τ) : ScopedList e (σ ++ τ) := by
  intro im him
  rcases List.mem_append.1 him with h | h
  · exact h₁ im h
  · exact h₂ im h

theorem scoped_map_subst {e : Nat} {σ : List Impl} (hσ : ScopedList e σ) {α : Type}
    (l : List α) (f : α → Impl) : ScopedList e (l.map fun a => (f a).subst σ) := by
  intro im him
  simp only [List.mem_map] at him
  obtain ⟨a, _, rfl⟩ := him
  exact Impl.subst_scoped hσ _

/-- The simulation invariant of `flattenNodes`. -/
theorem flattenNodes_sim (L : PairLaws) (C : CoreSem M) :
    ∀ (σ : List Impl) (eB : Nat) (ns : List (Node M)), ScopedList eB σ →
      ScopedList (flattenNodes σ eB ns).2.1 (flattenNodes σ eB ns).1 ∧
      (flattenNodes σ eB ns).1.length = envAfter σ.length ns ∧
      (flattenNodes σ eB ns).2.1 = linkedEnv eB (flattenNodes σ eB ns).2.2 ∧
      ∀ {X : Sig.{0}} (EA FB : Strategy X sigU), EA = FB.comp (ofH (implsH eB σ)) →
        denNodes C σ.length ns EA =
          (Linked.denU.go C eB (flattenNodes σ eB ns).2.2 FB).comp
            (ofH (implsH (flattenNodes σ eB ns).2.1 (flattenNodes σ eB ns).1))
  | σ, eB, [], hσ => by
    simp only [flattenNodes]
    refine ⟨hσ, rfl, rfl, fun EA FB h => ?_⟩
    simp only [denNodes, Linked.denU.go, h]
  | σ, eB, .core m args :: ns, hσ => by
    set w := (CoreModule.exports m).length
    have hσ₁ : ScopedList (eB + w) (σ ++ (List.range w).map fun i => Impl.fwd (eB + i)) :=
      ScopedList.append (ScopedList.mono hσ (Nat.le_add_right _ _)) (scoped_fwds eB w)
    obtain ⟨h₁, h₂, h₃, h₄⟩ := flattenNodes_sim L C _ _ ns hσ₁
    have hlen : (σ ++ (List.range w).map fun i => Impl.fwd (eB + i)).length = σ.length + w := by
      simp
    rw [hlen] at h₂ h₄
    simp only [flattenNodes]
    refine ⟨h₁, by simpa [envAfter, Node.width] using h₂, by simpa [linkedEnv] using h₃,
      fun EA FB h => ?_⟩
    simp only [denNodes, Node.den, Node.width, Linked.denU.go]
    exact h₄ _ _ (ext_sim L C hσ h m args)
  | σ, eB, .inst (.mk I ns' xs') args :: ns, hσ => by
    rw [flattenNodes]
    set σc := (List.range I.length).map fun i => (args[i]?.getD Impl.trap).subst σ
    have hσc : ScopedList eB σc := scoped_map_subst hσ _ _
    obtain ⟨c₁, c₂, c₃, c₄⟩ := flattenNodes_sim L C σc eB ns' hσc
    set rc := flattenNodes σc eB ns'
    have hle : eB ≤ rc.2.1 := c₃ ▸ le_linkedEnv eB _
    set ys := xs'.map fun x => x.impl.subst rc.1
    have hσ₂ : ScopedList rc.2.1 (σ ++ ys) := ScopedList.append (ScopedList.mono hσ hle) (scoped_map_subst c₁ _ _)
    obtain ⟨h₁, h₂, h₃, h₄⟩ := flattenNodes_sim L C (σ ++ ys) rc.2.1 ns hσ₂
    have hlen : (σ ++ ys).length = σ.length + xs'.length := by simp [ys]
    rw [hlen] at h₂ h₄
    have hσclen : σc.length = I.length := by simp [σc]
    rw [hσclen] at c₂ c₄
    refine ⟨h₁, by simpa [envAfter, Node.width] using h₂, ?_, fun EA FB h => ?_⟩
    · simp only [linkedEnv_append]
      convert h₃ using 2
      exact c₃.symm
    simp only [denNodes, Node.den, Node.width, Comp.exports_mk]
    rw [go_append, ← c₃]
    apply h₄
    -- the nested instance
    subst h
    simp only [ext, Comp.denU]
    set S := implsH eB σ
    rw [Strategy.comp_assoc FB, ← Strategy.comp_assoc (ofH S), L.hdist, Strategy.comp_id,
      ← Strategy.comp_assoc (ofH S), ← Strategy.ofHandler_comp,
      ← Strategy.comp_assoc (ofH (S.comp _)), denNodes_comp, ← Strategy.ofHandler_comp,
      implsH_comp_maskH_subst]
    have hc := c₄ (ofH (implsH eB σc)) (Strategy.id sigU) (Strategy.id_comp _).symm
    rw [hc, Strategy.comp_assoc, ← Strategy.ofHandler_comp, ← c₂, implsH_comp_exportsH,
      gl L C (H₁ := S) (eB₀ := eB) (fun d hd => splitH_comp_implsH_scoped hσ hd) σ.length eB _ _
        le_rfl, L.cp, ← Strategy.ofHandler_comp]
    simp only [exportsH, List.map_map]
    rw [case_comp_splitH hσ hle, ← Strategy.comp_assoc, ← go_eq_comp]
    rfl

theorem scoped_range_fwd (n : Nat) : ScopedList n ((List.range n).map Impl.fwd) := by
  simpa using scoped_fwds 0 n

/-- **Flattening preserves the denotation**, under the pairing laws. -/
theorem denU_flatten (L : PairLaws) (C : CoreSem M) (c : Comp M) :
    (flatten c).denU C = c.denU C := by
  obtain ⟨I, ns, xs⟩ := c
  have hσ := scoped_range_fwd I.length
  obtain ⟨-, h₂, h₃, h₄⟩ := flattenNodes_sim L C _ I.length ns hσ
  have hlen : ((List.range I.length).map Impl.fwd).length = I.length := by simp
  rw [hlen] at h₂ h₄
  have hbase : Strategy.ofHandler (maskH I.length) =
      (Strategy.ofHandler (maskH I.length)).comp
        (Strategy.ofHandler (implsH I.length ((List.range I.length).map Impl.fwd))) := by
    rw [implsH_fwd, ← Strategy.ofHandler_comp, maskH_comp_maskH]
  simp only [flatten, Linked.denU, Comp.denU]
  rw [h₄ _ _ hbase, Strategy.comp_assoc, ← Strategy.ofHandler_comp, ← h₂,
    implsH_comp_exportsH, ← h₃]

/-- A scoped wiring list below the mask of its scope is unchanged. -/
private theorem maskH_comp_implsH {e : Nat} {σ₀ : List Impl} (hσ : ScopedList e σ₀) :
    (maskH e).comp (implsH e σ₀) = implsH e σ₀ := by
  funext q
  simp only [Handler.comp, implsH]
  cases h : σ₀[q.1]? with
  | none => rfl
  | some im =>
    show (im.prog e q.2).interp (maskH e) = im.prog e q.2
    have hs : im.Scoped e := hσ im (List.mem_of_getElem? h)
    obtain ⟨c, t⟩ := im
    simp only [Impl.prog, runChain_interp]
    congr 1
    funext y
    cases t with
    | const _ => rfl
    | call r =>
      have hr : r < e := hs
      simp [Target.prog, hr, Prog.interp_call, maskH, Prog.bind_pure]

/-- **Specialisation composes the known handler in statically** (assuming
`PairLaws`). -/
theorem denU_specialise (L : PairLaws) (C : CoreSem M) (J : Iface) {σ₀ : List Impl}
    (hσ : ScopedList J.length σ₀) (c : Comp M) (hlen : σ₀.length = c.imports.length) :
    (specialise J σ₀ c).denU C = (ofH (implsH J.length σ₀)).comp (c.denU C) := by
  obtain ⟨I, ns, xs⟩ := c
  have hlen' : σ₀.length = I.length := hlen
  obtain ⟨-, h₂, h₃, h₄⟩ := flattenNodes_sim L C σ₀ J.length ns hσ
  have h₂' : (flattenNodes σ₀ J.length ns).1.length = envAfter I.length ns := by
    rw [← hlen']; exact h₂
  have h₄' : ∀ {X : Sig.{0}} (EA FB : Strategy X sigU),
      EA = FB.comp (ofH (implsH J.length σ₀)) →
      denNodes C I.length ns EA =
        (Linked.denU.go C J.length (flattenNodes σ₀ J.length ns).2.2 FB).comp
          (ofH (implsH (flattenNodes σ₀ J.length ns).2.1 (flattenNodes σ₀ J.length ns).1)) := by
    rw [← hlen']; exact h₄
  have hmask : (maskH J.length).comp (implsH J.length σ₀) = implsH J.length σ₀ :=
    maskH_comp_implsH hσ
  have hbase : (ofH (implsH J.length σ₀)).comp (ofH (maskH I.length)) =
      (ofH (maskH J.length)).comp (ofH (implsH J.length σ₀)) := by
    have hl : (List.range σ₀.length).map (fun i => σ₀[i]?.getD Impl.trap) = σ₀ := by
      apply List.ext_getElem (by simp)
      intro i h₁ h₂
      simp [List.getElem?_eq_getElem h₂]
    rw [← Strategy.ofHandler_comp, ← Strategy.ofHandler_comp, hmask, implsH_comp_maskH, ← hlen',
      hl]
  simp only [specialise, Linked.denU, Comp.denU]
  rw [← Strategy.comp_assoc, denNodes_comp, h₄' _ _ hbase, Strategy.comp_assoc,
    ← Strategy.ofHandler_comp, ← h₂', implsH_comp_exportsH, ← h₃]

end Silmaril.Proofs.Wasm.Component.Laws
