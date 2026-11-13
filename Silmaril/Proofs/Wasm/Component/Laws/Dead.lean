module

public import Silmaril.Proofs.Wasm.Component.Laws.Env
public import Silmaril.Wasm.Component.Passes.DeadInstance.Defs

/-!
# Dead instance elimination: proofs

Under `PairLaws`: removing a dead core instance preserves the denotation of a
flat component (`denU_removeNode`). The environment without the instance is
simulated by the environment with it, through the renaming `shiftσ` that skips
the functions of the removed instance (`ext_sim`); at the removed instance the
simulation starts by projection (`PairLaws.pproj`) and the fact that environments
trap beyond their size (`go_traps`).
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Laws

open Silmaril.Games
open Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

local notation "ofH" => Strategy.ofHandler

/-! ## Environments trap beyond their size -/

theorem splitH_comp_maskH (e w : Nat) :
    (splitH e).comp (maskH (e + w)) = (Handler.sum (maskH e) (maskH w)).comp (splitH e) := by
  funext q
  obtain ⟨r, x⟩ := q
  simp only [Handler.comp]
  by_cases h₁ : r < e
  · have hR : (splitH e (r, x)) = .call (.inl (r, x)) fun n => .pure n := by
      simp only [splitH, h₁, ↓reduceIte]
    rw [hR]
    show _ = ((Handler.sum (maskH e) (maskH w) (.inl (r, x))).bind fun n => Prog.pure n)
    rw [Prog.bind_pure]
    simp only [maskH, Target.prog, h₁, Nat.lt_of_lt_of_le h₁ (Nat.le_add_right e w), Handler.sum,
      Prog.interp_call, splitH, ↓reduceIte]
    rfl
  · show ((maskH (e + w)) (r, x)).interp (splitH e) =
      (splitH e (r, x)).interp (Handler.sum (maskH e) (maskH w))
    have hR : (splitH e (r, x)) = .call (.inr (r - e, x)) fun n => .pure n := by
      simp only [splitH, h₁, ↓reduceIte]
    rw [hR]
    show _ = ((Handler.sum (maskH e) (maskH w) (.inr (r - e, x))).bind fun n => Prog.pure n)
    rw [Prog.bind_pure]
    by_cases h₂ : r < e + w
    · have h₃ : r - e < w := by omega
      simp only [maskH, Target.prog, h₁, h₂, h₃, Handler.sum, Prog.interp_call,
        splitH, ↓reduceIte]
      rfl
    · have h₃ : ¬ r - e < w := by omega
      simp only [maskH, Target.prog, h₂, h₃, Handler.sum, ↓reduceIte]
      rfl

theorem ext_traps (L : PairLaws) {X : Sig.{0}} {D : Strategy X sigU} {e w : Nat}
    (hD : D.comp (ofH (maskH e)) = D) {N : Strategy sigU sigU}
    (hN : N.comp (ofH (maskH w)) = N) :
    (ext e D N).comp (ofH (maskH (e + w))) = ext e D N := by
  simp only [ext, Strategy.comp_assoc]
  rw [← Strategy.ofHandler_comp, splitH_comp_maskH, Strategy.ofHandler_comp,
    ← Strategy.comp_assoc ((Strategy.id sigU).pair N), L.psum, Strategy.id_comp, hN]
  conv => rhs; rw [← hD]
  conv => lhs; rw [← hD]
  simp only [Strategy.comp_assoc]
  rw [← Strategy.comp_assoc (ofH (maskH e)), ← Strategy.comp_assoc (ofH (maskH e)), L.hdist,
    L.hdist, Strategy.comp_id, ← Strategy.ofHandler_comp, maskH_comp_maskH]

theorem go_traps (L : PairLaws) (C : CoreSem M) {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (M × List Impl)) (D : Strategy X sigU),
      D.comp (ofH (maskH e)) = D →
      (Linked.denU.go C e ns D).comp (ofH (maskH (linkedEnv e ns))) = Linked.denU.go C e ns D
  | e, [], D, hD => by simpa only [Linked.denU.go, linkedEnv] using hD
  | e, n :: ns, D, hD => by
    simp only [Linked.denU.go, linkedEnv]
    exact go_traps L C _ ns _ (ext_traps L hD (coreNode_mask C e n.1 n.2))

/-- Restricting an extended environment to its old functions. -/
theorem ext_mask_left (L : PairLaws) {X : Sig.{0}} {D : Strategy X sigU} {e : Nat}
    (hD : D.comp (ofH (maskH e)) = D) (N : Strategy sigU sigU) :
    (ext e D N).comp (ofH (maskH e)) = D := by
  have hh : (splitH e).comp (maskH e) =
      (Handler.ofHom (Sig.Hom.inl sigU sigU)).comp (maskH e) := by
    funext q
    obtain ⟨r, x⟩ := q
    by_cases h₁ : r < e
    · simp [Handler.comp, maskH, Target.prog, h₁, Prog.interp_call, Prog.bind_pure, splitH]
      rfl
    · simp [Handler.comp, maskH, Target.prog, h₁]
  have hp := L.pproj (Strategy.id sigU) N
  simp only [Strategy.restrict] at hp
  simp only [ext, Strategy.comp_assoc]
  rw [← Strategy.ofHandler_comp, hh, Strategy.ofHandler_comp,
    ← Strategy.comp_assoc ((Strategy.id sigU).pair N), hp, Strategy.id_comp, hD]

/-! ## The renaming that skips a removed instance -/

/-- Function `r` of the environment without the removed functions `[e, e + w)`
is function `r` (below `e`) or `r + w` of the environment with them. -/
def shiftσ (e w n : Nat) : List Impl :=
  (List.range n).map fun r => Impl.fwd (if r < e then r else r + w)

theorem shiftσ_length (e w n : Nat) : (shiftσ e w n).length = n := by simp [shiftσ]

theorem shiftσ_getElem? {e w n r : Nat} (h : r < n) :
    (shiftσ e w n)[r]? = some (Impl.fwd (if r < e then r else r + w)) := by
  simp [shiftσ, List.getElem?_range h]

theorem shiftσ_scoped {e w n : Nat} (_he : e ≤ n) : ScopedList (n + w) (shiftσ e w n) := by
  intro im him
  simp only [shiftσ, List.mem_map, List.mem_range] at him
  obtain ⟨r, hr, rfl⟩ := him
  show (if r < e then r else r + w) < n + w
  split <;> omega

theorem shiftσ_append {e w n : Nat} (he : e ≤ n) (w' : Nat) :
    shiftσ e w n ++ (List.range w').map (fun i => Impl.fwd (n + w + i)) =
      shiftσ e w (n + w') := by
  simp only [shiftσ, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, show ¬ n + i < e by omega, ↓reduceIte]
  congr 1
  omega

theorem implsH_shiftσ_base (e w : Nat) : implsH (e + w) (shiftσ e w e) = maskH e := by
  funext q
  obtain ⟨r, x⟩ := q
  by_cases h : r < e
  · simp [implsH, shiftσ_getElem? h, h, maskH, Target.prog, Impl.prog, runChain,
      Nat.lt_of_lt_of_le h (Nat.le_add_right e w)]
  · rw [show implsH (e + w) (shiftσ e w e) (r, x) = .pure none by
      simp only [implsH]
      rw [List.getElem?_eq_none (by simp [shiftσ_length]; omega)]]
    simp [maskH, Target.prog, h]

theorem unshift_subst_prog {e w n : Nat} (he : e ≤ n) {im : Impl}
    (h : im.avoids e w = true) :
    ((im.unshift e w).subst (shiftσ e w n)).prog (n + w) = im.prog (n + w) := by
  obtain ⟨c, t⟩ := im
  cases t with
  | const _ => rfl
  | call r =>
    simp only [Impl.avoids, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
      not_le, not_lt] at h
    by_cases h₁ : r < e
    · simp only [Impl.unshift, h₁, ↓reduceIte, Impl.subst,
        shiftσ_getElem? (Nat.lt_of_lt_of_le h₁ he), List.append_nil]
    · have h₂ : e + w ≤ r := by omega
      simp only [Impl.unshift, h₁, ↓reduceIte, Impl.subst]
      by_cases h₃ : r - w < n
      · simp only [shiftσ_getElem? h₃, show ¬ r - w < e by omega, ↓reduceIte,
          show r - w + w = r by omega, List.append_nil]
      · rw [List.getElem?_eq_none (by simp [shiftσ_length]; omega)]
        simp only [Impl.prog]
        congr 1
        funext y
        simp [Target.prog, show ¬ r < n + w by omega]

theorem implsN_unshift {e w n : Nat} (he : e ≤ n) {args : List Impl}
    (h : args.all (Impl.avoids e w) = true) (t : Nat) :
    implsN (n + w) ((args.map (Impl.unshift e w)).map (Impl.subst (shiftσ e w n))) t =
      implsN (n + w) args t := by
  funext q
  simp only [implsN, implsH, List.map_map, List.getElem?_map]
  cases hq : args[q.1.val]? with
  | none => rfl
  | some im =>
    simp only [Option.map_some, Function.comp]
    exact congrFun (unshift_subst_prog he
      ((List.all_eq_true.1 h) im (List.mem_of_getElem? hq))) q.2

theorem linkedEnv_add :
    ∀ (a b : Nat) (ns : List (M × List Impl)), linkedEnv (a + b) ns = linkedEnv a ns + b
  | _, _, [] => rfl
  | a, b, n :: ns => by
    simp only [linkedEnv]
    rw [show a + b + (CoreModule.exports n.1).length = a + (CoreModule.exports n.1).length + b
      by omega]
    exact linkedEnv_add _ b ns

theorem linkedEnv_map {f : List Impl → List Impl} :
    ∀ (a : Nat) (ns : List (M × List Impl)),
      linkedEnv a (ns.map fun n => (n.1, f n.2)) = linkedEnv a ns
  | _, [] => rfl
  | _, _ :: ns => linkedEnv_map _ ns

/-- The simulation of the instances after a removed one. -/
theorem die_go (L : PairLaws) (C : CoreSem M) (e w : Nat) :
    ∀ (post : List (M × List Impl)) (n : Nat) {X : Sig.{0}} (EA FB : Strategy X sigU),
      e ≤ n → post.all (fun nd => nd.2.all (Impl.avoids e w)) = true →
      EA = FB.comp (ofH (implsH (n + w) (shiftσ e w n))) →
      Linked.denU.go C n (post.map fun nd => (nd.1, nd.2.map (Impl.unshift e w))) EA =
        (Linked.denU.go C (n + w) post FB).comp
          (ofH (implsH (linkedEnv n post + w) (shiftσ e w (linkedEnv n post))))
  | [], n, _, EA, FB, _, _, h => by simpa only [List.map_nil, Linked.denU.go, linkedEnv] using h
  | nd :: post, n, _, EA, FB, he, hav, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hav
    obtain ⟨hnd, hpost⟩ := hav
    simp only [List.map_cons, Linked.denU.go, linkedEnv]
    set wm := (CoreModule.exports nd.1).length
    have hs := ext_sim L C (shiftσ_scoped (w := w) he) h nd.1 (nd.2.map (Impl.unshift e w))
    rw [shiftσ_length] at hs
    have hc : coreNode C (n + w) nd.1 ((nd.2.map (Impl.unshift e w)).map
        (Impl.subst (shiftσ e w n))) = coreNode C (n + w) nd.1 nd.2 := by
      simp only [coreNode, implsN_unshift he hnd]
    rw [hc, shiftσ_append he wm] at hs
    have := die_go L C e w post (n + wm)
      (ext n EA (coreNode C n nd.1 (nd.2.map (Impl.unshift e w))))
      (ext (n + w) FB (coreNode C (n + w) nd.1 nd.2)) (he.trans (Nat.le_add_right _ _)) hpost
      (by rw [hs, Nat.add_right_comm n w])
    rw [this, Nat.add_right_comm n wm w]

/-- Exports that avoid the removed functions, unshifted and then renamed by
`shiftσ`, run as before. -/
private theorem exportsH_unshift_subst {e w n : Nat} (he : e ≤ n) {xs : List Export}
    (hxs : xs.all (fun x => x.impl.avoids e w) = true) :
    exportsH (n + w) ((xs.map fun x => { x with impl := x.impl.unshift e w }).map
      fun x => { x with impl := x.impl.subst (shiftσ e w n) }) = exportsH (n + w) xs := by
  simp only [exportsH, List.map_map]
  funext q
  simp only [implsH, List.getElem?_map]
  cases hq : xs[q.1]? with
  | none => rfl
  | some x =>
    simp only [Option.map_some, Function.comp]
    exact congrFun (unshift_subst_prog he
      ((List.all_eq_true.1 hxs) x (List.mem_of_getElem? hq))) q.2

/-- The surviving case of `denU_removeNode`: the node `nd` between `pre` and
`post` is dead, so dropping it and unshifting what follows keeps the
denotation. -/
private theorem denU_removeNode_split (L : PairLaws) (C : CoreSem M) (I : Iface)
    (pre post : List (M × List Impl)) (nd : M × List Impl) (xs : List Export)
    (hpost : post.all (fun n => n.2.all (Impl.avoids (linkedEnv I.length pre)
      (CoreModule.exports nd.1).length)) = true)
    (hxs : xs.all (fun x => x.impl.avoids (linkedEnv I.length pre)
      (CoreModule.exports nd.1).length) = true) :
    Linked.denU C ⟨I, pre ++ post.map (fun n => (n.1, n.2.map
        (Impl.unshift (linkedEnv I.length pre) (CoreModule.exports nd.1).length))),
      xs.map fun x => { x with impl := (x.impl.unshift (linkedEnv I.length pre)
        (CoreModule.exports nd.1).length) }⟩ =
      Linked.denU C ⟨I, pre ++ nd :: post, xs⟩ := by
  set e := linkedEnv I.length pre
  set w := (CoreModule.exports nd.1).length
  set D := Linked.denU.go C I.length pre (ofH (maskH I.length))
  set xs' := xs.map fun x => { x with impl := x.impl.unshift e w }
  have hD : D.comp (ofH (maskH e)) = D :=
    go_traps L C _ pre _ (by rw [← Strategy.ofHandler_comp, maskH_comp_maskH])
  have hbase : D = (ext e D (coreNode C e nd.1 nd.2)).comp
      (ofH (implsH (e + w) (shiftσ e w e))) := by
    rw [implsH_shiftσ_base, ext_mask_left L hD]
  have hgo : Linked.denU.go C e (post.map fun nd => (nd.1, nd.2.map (Impl.unshift e w))) D =
      (Linked.denU.go C (e + w) post (ext e D (coreNode C e nd.1 nd.2))).comp
        (ofH (implsH (linkedEnv e post + w) (shiftσ e w (linkedEnv e post)))) :=
    die_go L C e w post e D _ le_rfl hpost hbase
  have key : (implsH (linkedEnv e post + w) (shiftσ e w (linkedEnv e post))).comp
      (exportsH (linkedEnv e post) xs') = exportsH (linkedEnv e post + w)
        (xs'.map fun x => { x with impl := x.impl.subst (shiftσ e w (linkedEnv e post)) }) := by
    simpa only [shiftσ_length] using
      implsH_comp_exportsH (linkedEnv e post + w) (shiftσ e w (linkedEnv e post)) xs'
  have hexp := exportsH_unshift_subst (le_linkedEnv e post) hxs
  simp only [Linked.denU]
  rw [go_append, go_append, hgo, Linked.denU.go]
  simp only [linkedEnv_append, linkedEnv, linkedEnv_map]
  rw [Strategy.comp_assoc, ← Strategy.ofHandler_comp, key, linkedEnv_add, hexp]

/-- **Dead instance elimination preserves the denotation** (assuming
`PairLaws`). -/
theorem denU_removeNode (L : PairLaws) (C : CoreSem M) {l l' : Linked M} {k : Nat}
    (h : removeNode l k = some l') : l'.denU C = l.denU C := by
  obtain ⟨I, ns, xs⟩ := l
  cases hk : ns[k]? with
  | none =>
    have hnone : removeNode ⟨I, ns, xs⟩ k = none := by simp only [removeNode, hk]
    exact nomatch hnone.symm.trans h
  | some nd =>
    show l'.denU C = Linked.denU C ⟨I, ns, xs⟩
    obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.1 hk
    have hns : ns = ns.take k ++ nd :: ns.drop (k + 1) := by
      rw [← hkeq, List.getElem_cons_drop, List.take_append_drop]
    by_cases hav : ((ns.drop (k + 1)).all (fun n => n.2.all
        (Impl.avoids (linkedEnv I.length (ns.take k)) (CoreModule.exports nd.1).length)) &&
        xs.all (fun x => x.impl.avoids (linkedEnv I.length (ns.take k))
          (CoreModule.exports nd.1).length)) = true
    · show l'.denU C = Linked.denU C ⟨I, ns, xs⟩
      obtain ⟨hpost, hxs⟩ := Bool.and_eq_true_iff.1 hav
      have hsome : removeNode ⟨I, ns, xs⟩ k = some ⟨I, ns.take k ++ (ns.drop (k + 1)).map
          (fun n => (n.1, n.2.map (Impl.unshift (linkedEnv I.length (ns.take k))
            (CoreModule.exports nd.1).length))), xs.map fun x => { x with impl :=
              (x.impl.unshift (linkedEnv I.length (ns.take k))
                (CoreModule.exports nd.1).length) }⟩ := by
        simp only [removeNode, hk, hav, ↓reduceIte]
      rw [← Option.some.inj (hsome.symm.trans h)]
      conv => rhs; rw [hns]
      exact denU_removeNode_split L C I _ _ nd xs hpost hxs
    · have hnone : removeNode ⟨I, ns, xs⟩ k = none := by
        simp only [removeNode, hk, hav, Bool.false_eq_true, ↓reduceIte]
      exact nomatch hnone.symm.trans h

end Silmaril.Proofs.Wasm.Component.Laws
