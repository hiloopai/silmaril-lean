module

public import Silmaril.Wasm.Component.Algebra.Kahn.Defs
public import Silmaril.Games.Answer.Thms
public import Silmaril.Wasm.Component.Adapter.Defs

/-!
# Kahn strategies: proofs

* `denotes_kahn`: the Kahn machine follows the legality automaton and is receptive, so it
  denotes its strategy.
* `compSim`, `compSim'`: for monotone `F` and `G`, the parallel composition of the Kahn machines
  of `F` and `G` and the Kahn machine of `G ∘ F` simulate each other. The relation `CRel`
  records that the downstream machine has received exactly the first `kT` answers the upstream
  one produced (`Inv`); the composite machine processes eagerly what the pair processes lazily,
  and `drain` runs the hidden pulls of the pair until the downstream machine can answer or the
  upstream one has delivered everything.
* `idSim`, `idSim'`: the Kahn machine of the identity and the transition system of `maskH 1`
  simulate each other.
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Algebra.Kahn

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra.Kahn

/-! ## The Kahn machine denotes its strategy -/

theorem kpos_step {F : List Ans → List Ans} {x y : KState} {l : Option (Move sigU sigU)}
    (h : KStep F x l y) : Path (kpos x) l.toList (kpos y) := by
  cases h with
  | ask h k q => exact Path.single (Step.ask (E := sigU) (F := sigU) q)
  | trap h k q _ => exact Path.single (Step.ret (E := sigU) (F := sigU) q none)
  | out h k q a _ _ => exact Path.single (Step.ret (E := sigU) (F := sigU) q a)
  | pull h k q _ _ =>
    exact Path.single (Step.call (E := sigU) (F := sigU) q ((0 : Nat), q.2))
  | recv h k q a =>
    exact Path.single (Step.reply (E := sigU) (F := sigU) q ((0 : Nat), q.2) a)

theorem kpos_recv {F : List Ans → List Ans} {x : KState} {o : Move sigU sigU}
    {p' : Pos sigU sigU} (h : Step (kpos x) o p') (ho : o.IsO) :
    ∃ y, (kahnL F).Run x [o] y := by
  rcases x with ⟨hs, k⟩ | ⟨hs, k, q⟩ | ⟨hs, k, q⟩
  · cases h with
    | ask q => exact ⟨_, .vis (KStep.ask hs k q) (.nil _)⟩
  · cases h with
    | call => exact ho.elim
    | ret => exact ho.elim
  · cases h with
    | reply _ _ n => exact ⟨_, .vis (KStep.recv hs k q n) (.nil _)⟩

/-- **The Kahn machine denotes its strategy.** -/
theorem denotes_kahn (F : List Ans → List Ans) : (kahnL F).Denotes (kahn F) :=
  LTS.denotes_of_pos kpos rfl kpos_step kpos_recv

/-! ## Lists -/

theorem getElem?_of_prefix {l l' : List Ans} (h : l <+: l') {k : Nat} {a : Ans}
    (hk : l[k]? = some a) : l'[k]? = some a := by
  obtain ⟨t, rfl⟩ := h
  have hk' : k < l.length := (List.getElem?_eq_some_iff.1 hk).1
  rw [List.getElem?_append_left hk', hk]

theorem mono_of_prefix {G : List Ans → List Ans} (hG : Mono G) {l l' : List Ans}
    (h : l <+: l') : G l <+: G l' := by
  obtain ⟨t, rfl⟩ := h
  exact hG l t

/-! ## Composition -/

section Comp

variable {F G : List Ans → List Ans}

/-- The downstream machine has received the first `kT` answers of the upstream one. -/
def Inv (F : List Ans → List Ans) (h : List Ans) (kT : Nat) (hU : List Ans) : Prop :=
  kT ≤ (F h).length ∧ hU = (F h).take kT

theorem Inv.prefix {h hU : List Ans} {kT : Nat} (hi : Inv F h kT hU) : hU <+: F h :=
  hi.2 ▸ List.take_prefix _ _

theorem Inv.next {h hU : List Ans} {kT : Nat} {a : Ans} (hi : Inv F h kT hU)
    (ha : (F h)[kT]? = some a) : Inv F h (kT + 1) (hU ++ [a]) := by
  have hlt : kT < (F h).length := (List.getElem?_eq_some_iff.1 ha).1
  refine ⟨hlt, ?_⟩
  rw [List.take_add_one, ha, hi.2]
  rfl

theorem Inv.full {h hU : List Ans} {kT : Nat} (hi : Inv F h kT hU)
    (hn : (F h)[kT]? = none) : hU = F h := by
  rw [hi.2]
  exact List.take_of_length_le (List.getElem?_eq_none_iff.1 hn)

theorem Inv.full' {h hU : List Ans} {kT : Nat} (hi : Inv F h kT hU)
    (hn : kT = (F h).length) : hU = F h := by
  rw [hi.2, hn]
  exact List.take_length

theorem Inv.append (hF : Mono F) {h hU : List Ans} {kT : Nat} (hi : Inv F h kT hU) (a : Ans) :
    Inv F (h ++ [a]) kT hU := by
  obtain ⟨t, ht⟩ := hF h [a]
  refine ⟨?_, ?_⟩
  · rw [← ht, List.length_append]
    exact Nat.le_add_right_of_le hi.1
  · rw [← ht, List.take_append_of_le_length hi.1]
    exact hi.2

theorem inv_nil : Inv F [] 0 [] := ⟨Nat.zero_le _, rfl⟩

/-- Relation of the pair of machines to the machine of the composite. -/
inductive CRel (F G : List Ans → List Ans) :
    (kahnL F).State × (kahnL G).State → (kahnL fun h => G (F h)).State → Prop
  | idle {h hU : List Ans} {kT k : Nat} : Inv F h kT hU →
      CRel F G (.idle h kT, .idle hU k) (.idle h k)
  | run {h hU : List Ans} {kT k : Nat} {q : sigU.Op} : Inv F h kT hU →
      CRel F G (.idle h kT, .run hU k q) (.run h k q)
  | up {h hU : List Ans} {kT k : Nat} {q : sigU.Op} : Inv F h kT hU → q.1 = 0 →
      (G hU)[k]? = none → CRel F G (.run h kT (0, q.2), .wait hU k q) (.run h k q)
  | wait {h hU : List Ans} {kT k : Nat} {q : sigU.Op} : Inv F h kT hU → q.1 = 0 →
      (G hU)[k]? = none → CRel F G (.wait h kT (0, q.2), .wait hU k q) (.wait h k q)

/-- The composite of the two Kahn machines. -/
abbrev pairL (F G : List Ans → List Ans) : LTS sigU sigU := (kahnL F).comp (kahnL G)

/-- The pair is simulated by the machine of the composite. -/
def compSim (hF : Mono F) (hG : Mono G) : LTS.Simulation (pairL F G) (kahnL fun h => G (F h)) where
  R := CRel F G
  init := .idle inv_nil
  step := by
    intro x x' z l hr hs
    change LTS.CompStep (kahnL F) (kahnL G) x l x' at hs
    cases hr with
    | idle hi =>
      cases hs with
      | tau₁ hs => cases hs
      | tau₂ hs => cases hs
      | left e hs => cases hs
      | right g ht =>
        cases ht with
        | ask _ _ q => exact ⟨_, .vis (KStep.ask _ _ q) (.nil _), .run hi⟩
      | sync f hs ht => cases ht
    | @run h hU kT k q hi =>
      cases hs with
      | tau₁ hs => cases hs
      | tau₂ hs => cases hs
      | left e hs => cases hs
      | right g ht =>
        cases ht with
        | trap _ _ _ hq => exact ⟨_, .vis (KStep.trap _ _ _ hq) (.nil _), .idle hi⟩
        | out _ _ _ a hq ha =>
          have ha' : (G (F h))[k]? = some a := getElem?_of_prefix (mono_of_prefix hG hi.prefix) ha
          exact ⟨_, .vis (KStep.out _ _ _ a hq ha') (.nil _), .idle hi⟩
      | sync f hs ht =>
        cases ht with
        | pull _ _ _ hq hn =>
          cases hs with
          | ask => exact ⟨_, .nil _, .up hi hq hn⟩
    | @up h hU kT k q hi hq hn =>
      cases hs with
      | tau₁ hs => cases hs
      | tau₂ hs => cases hs
      | left e hs =>
        cases hs with
        | pull _ _ _ _ hF =>
          have hn' : (G (F h))[k]? = none := hi.full hF ▸ hn
          exact ⟨_, .vis (KStep.pull _ _ _ hq hn') (.nil _), .wait hi hq hn⟩
      | right g ht => cases ht
      | sync f hs ht =>
        cases ht with
        | recv _ _ _ a =>
          cases hs with
          | trap _ _ _ h0 => exact absurd rfl h0
          | out _ _ _ _ _ ha => exact ⟨_, .nil _, .run (hi.next ha)⟩
    | @wait h hU kT k q hi hq hn =>
      cases hs with
      | tau₁ hs => cases hs
      | tau₂ hs => cases hs
      | left e hs =>
        cases hs with
        | recv _ _ _ a => exact ⟨_, .vis (KStep.recv _ _ _ a) (.nil _), .up (hi.append hF a) hq hn⟩
      | right g ht => cases ht
      | sync f hs ht =>
        cases ht with
        | recv _ _ _ a => cases hs

/-- **Draining**: the pair runs hidden pulls until the downstream machine can answer its
`k`-th answer or the upstream machine has delivered everything it produced. -/
theorem drain {h : List Ans} {k : Nat} {q : sigU.Op} (hq : q.1 = 0) :
    ∀ (n kT : Nat) (hU : List Ans), (F h).length - kT = n → Inv F h kT hU →
      ∃ kT' hU', Inv F h kT' hU' ∧
        (pairL F G).Run (.idle h kT, .run hU k q) [] (.idle h kT', .run hU' k q) ∧
        ((G hU')[k]?.isSome ∨ kT' = (F h).length) := by
  intro n
  induction n with
  | zero =>
    intro kT hU hn hi
    exact ⟨kT, hU, hi, .nil _, .inr (by have := hi.1; omega)⟩
  | succ n ih =>
    intro kT hU hn hi
    by_cases hs : ((G hU)[k]?).isSome
    · exact ⟨kT, hU, hi, .nil _, .inl hs⟩
    · have hnone : (G hU)[k]? = none := Option.not_isSome_iff_eq_none.1 hs
      have hlt : kT < (F h).length := by omega
      have ha : (F h)[kT]? = some (F h)[kT] := List.getElem?_eq_getElem hlt
      obtain ⟨kT', hU', hi', hr, hd⟩ := ih (kT + 1) (hU ++ [(F h)[kT]]) (by omega) (hi.next ha)
      refine ⟨kT', hU', hi', ?_, hd⟩
      refine .tau (LTS.CompStep.sync (.ask ((0 : Nat), q.2)) (KStep.ask h kT _)
        (KStep.pull hU k q hq hnone)) ?_
      exact .tau (LTS.CompStep.sync (.ans ((0 : Nat), q.2) (F h)[kT])
        (KStep.out h kT ((0 : Nat), q.2) _ rfl ha) (KStep.recv hU k q _)) hr

/-- After draining, the downstream machine's `k`-th answer is the composite's. -/
theorem get_of_drain (hG : Mono G) {h hU' : List Ans} {kT' k : Nat} (hi' : Inv F h kT' hU')
    (hd : ((G hU')[k]?).isSome ∨ kT' = (F h).length) : (G hU')[k]? = (G (F h))[k]? := by
  rcases hd with hd | hd
  · obtain ⟨b, hb⟩ : ∃ b, (G hU')[k]? = some b := Option.isSome_iff_exists.1 hd
    have hb' : (G (F h))[k]? = some b := getElem?_of_prefix (mono_of_prefix hG hi'.prefix) hb
    rw [hb, hb']
  · rw [hi'.full' hd]

theorem full_of_drain {h hU' : List Ans} {kT' k : Nat}
    (hd : ((G hU')[k]?).isSome ∨ kT' = (F h).length) (hn : (G hU')[k]? = none) :
    kT' = (F h).length := by
  rcases hd with hd | hd
  · simp [hn] at hd
  · exact hd

/-- Drain, then answer or pull as the composite machine does. -/
theorem stepRun (hG : Mono G) {h hU : List Ans} {kT k : Nat} {q : sigU.Op}
    {l : Option (Move sigU sigU)} {z' : KState} (hi : Inv F h kT hU)
    (hs : KStep (fun h => G (F h)) (.run h k q) l z') :
    ∃ x', (pairL F G).Run (.idle h kT, .run hU k q) l.toList x' ∧ CRel F G x' z' := by
  cases hs with
  | trap _ _ _ hq => exact ⟨_, .vis (LTS.CompStep.right _ (KStep.trap _ _ _ hq)) (.nil _), .idle hi⟩
  | out _ _ _ a hq ha =>
    show ∃ x', (pairL F G).Run _ [.inr (.ans q a)] x' ∧ CRel F G x' (.idle h (k + 1))
    obtain ⟨kT', hU', hi', hr, hd⟩ := drain (G := G) hq _ kT hU rfl hi
    have ha' : (G hU')[k]? = some a := (get_of_drain hG hi' hd).trans ha
    exact ⟨_, hr.append (.vis (LTS.CompStep.right _ (KStep.out _ _ _ a hq ha')) (.nil _)),
      .idle hi'⟩
  | pull _ _ _ hq hn =>
    show ∃ x', (pairL F G).Run _ [.inl (.ask (0, q.2))] x' ∧ CRel F G x' (.wait h k q)
    obtain ⟨kT', hU', hi', hr, hd⟩ := drain (G := G) hq _ kT hU rfl hi
    have hn' : (G hU')[k]? = none := (get_of_drain hG hi' hd).trans hn
    have hfull : kT' = (F h).length := full_of_drain hd hn'
    have hF : (F h)[kT']? = none := List.getElem?_eq_none_iff.2 (by omega)
    refine ⟨_, hr.append (.tau (LTS.CompStep.sync (.ask ((0 : Nat), q.2)) (KStep.ask h kT' _)
      (KStep.pull hU' k q hq hn')) (.vis (LTS.CompStep.left _
        (KStep.pull h kT' ((0 : Nat), q.2) rfl hF)) (.nil _))), .wait hi' hq hn'⟩

/-- The machine of the composite is simulated by the pair. -/
def compSim' (hF : Mono F) (hG : Mono G) :
    LTS.Simulation (kahnL fun h => G (F h)) (pairL F G) where
  R z x := CRel F G x z
  init := .idle inv_nil
  step := by
    intro z z' x l hr hs
    change KStep (fun h => G (F h)) z l z' at hs
    cases hr with
    | idle hi =>
      cases hs with
      | ask _ _ q => exact ⟨_, .vis (LTS.CompStep.right _ (KStep.ask _ _ q)) (.nil _), .run hi⟩
    | run hi => exact stepRun hG hi hs
    | @up h hU kT k q hi hq hn =>
      by_cases hfull : kT = (F h).length
      · have hU'eq : hU = F h := hi.full' hfull
        have hF : (F h)[kT]? = none := List.getElem?_eq_none_iff.2 (by omega)
        cases hs with
        | trap _ _ _ hq' => exact absurd hq hq'
        | out _ _ _ a _ ha =>
          rw [← hU'eq, hn] at ha
          exact absurd ha (by simp)
        | pull _ _ _ _ _ =>
          exact ⟨_, .vis (LTS.CompStep.left _ (KStep.pull h kT ((0 : Nat), q.2) rfl hF))
            (.nil _), .wait hi hq hn⟩
      · have hlt : kT < (F h).length := by have := hi.1; omega
        have ha : (F h)[kT]? = some (F h)[kT] := List.getElem?_eq_getElem hlt
        obtain ⟨x', hr', hx'⟩ := stepRun hG (hi.next ha) hs
        exact ⟨x', .tau (LTS.CompStep.sync (.ans ((0 : Nat), q.2) (F h)[kT])
          (KStep.out h kT ((0 : Nat), q.2) _ rfl ha) (KStep.recv hU k q _)) hr', hx'⟩
    | @wait h hU kT k q hi hq hn =>
      cases hs with
      | recv _ _ _ a =>
        exact ⟨_, .vis (LTS.CompStep.left _ (KStep.recv h kT ((0 : Nat), q.2) a)) (.nil _),
          .up (hi.append hF a) hq hn⟩

end Comp

/-! ## The identity -/

/-- The forwarding handler of the stream interface. -/
abbrev idL : LTS sigU sigU := (maskH 1).toReduction.toLTS

/-- Relation of the Kahn machine of the identity to the transition system of `maskH 1`. -/
inductive IRel : (kahnL id).State → idL.State → Prop
  | idle {h : List Ans} : IRel (.idle h h.length) .idle
  | run {h : List Ans} {q : sigU.Op} : IRel (.run h h.length q) (.run q (maskH 1 q))
  | wait {h : List Ans} {p : Payload} :
      IRel (.wait h h.length (0, p)) (.wait (0, p) (0, p) fun n => .pure n)
  | ret {h : List Ans} {p : Payload} {a : Ans} :
      IRel (.run (h ++ [a]) h.length (0, p)) (.run (0, p) (.pure a))

theorem maskH_zero (p : Payload) : maskH 1 (0, p) = .call (0, p) fun n => .pure n := rfl

theorem maskH_ne {q : sigU.Op} (hq : q.1 ≠ 0) : maskH 1 q = .pure none := by
  have : ¬ q.1 < 1 := by omega
  simp only [maskH, Target.prog, this, ↓reduceIte]

theorem getElem?_length (h : List Ans) : h[h.length]? = none :=
  List.getElem?_eq_none_iff.2 (Nat.le_refl _)

theorem getElem?_snoc (h : List Ans) (a : Ans) : (h ++ [a])[h.length]? = some a := by
  simp

theorem idle_snoc (h : List Ans) (a : Ans) :
    IRel (.idle (h ++ [a]) (h.length + 1)) .idle := by
  have : (h ++ [a]).length = h.length + 1 := by simp
  rw [← this]
  exact .idle

/-- The Kahn machine of the identity is simulated by the forwarding handler. -/
def idSim : LTS.Simulation (kahnL id) idL where
  R := IRel
  init := .idle
  step := by
    intro x x' y l hr hs
    change KStep id x l x' at hs
    cases hr with
    | idle =>
      cases hs with
      | ask _ _ q => exact ⟨_, .vis (Reduction.Step.ask q) (.nil _), .run⟩
    | @run h q =>
      cases hs with
      | trap _ _ _ hq =>
        exact ⟨_, .vis (Reduction.Step.ret (maskH_ne hq)) (.nil _), .idle⟩
      | out _ _ _ a _ ha =>
        rw [show (id h)[h.length]? = none from getElem?_length h] at ha
        exact absurd ha (by simp)
      | pull _ _ _ hq _ =>
        obtain ⟨i, p⟩ := q
        simp only at hq
        subst hq
        exact ⟨_, .vis (Reduction.Step.call (maskH_zero p)) (.nil _), .wait⟩
    | @wait h p =>
      cases hs with
      | recv _ _ _ a =>
        exact ⟨_, .vis (Reduction.Step.resume (R := (maskH 1).toReduction) ((0 : Nat), p)
          ((0 : Nat), p) (fun n => .pure n) a) (.nil _), .ret⟩
    | @ret h p a =>
      cases hs with
      | trap _ _ _ hq => exact absurd rfl hq
      | out _ _ _ b _ hb =>
        rw [show (id (h ++ [a]))[h.length]? = some a from getElem?_snoc h a] at hb
        cases hb
        exact ⟨_, .vis (Reduction.Step.ret rfl) (.nil _), idle_snoc h a⟩
      | pull _ _ _ _ hn =>
        rw [show (id (h ++ [a]))[h.length]? = some a from getElem?_snoc h a] at hn
        exact absurd hn (by simp)

/-- The forwarding handler is simulated by the Kahn machine of the identity. -/
def idSim' : LTS.Simulation idL (kahnL id) where
  R y x := IRel x y
  init := .idle
  step := by
    intro y y' x l hr hs
    cases hr with
    | idle =>
      cases hs with
      | ask q => exact ⟨_, .vis (KStep.ask _ _ q) (.nil _), .run⟩
    | @run h q =>
      cases hs with
      | tau hc => exact (hc : False).elim
      | call hc =>
        by_cases hq : q.1 = 0
        · obtain ⟨i, p⟩ := q
          simp only at hq
          subst hq
          rw [maskH_zero] at hc
          cases hc
          exact ⟨_, .vis (KStep.pull _ _ _ rfl (getElem?_length h)) (.nil _), .wait⟩
        · rw [maskH_ne hq] at hc
          cases hc
      | ret hd =>
        by_cases hq : q.1 = 0
        · obtain ⟨i, p⟩ := q
          simp only at hq
          subst hq
          rw [maskH_zero] at hd
          cases hd
        · rw [maskH_ne hq] at hd
          cases hd
          exact ⟨_, .vis (KStep.trap _ _ _ hq) (.nil _), .idle⟩
    | @wait h p =>
      cases hs with
      | resume _ _ _ n => exact ⟨_, .vis (KStep.recv _ _ _ n) (.nil _), .ret⟩
    | @ret h p a =>
      cases hs with
      | tau hc => exact (hc : False).elim
      | call hc => cases hc
      | ret hd =>
        cases hd
        exact ⟨_, .vis (KStep.out _ _ _ a rfl (getElem?_snoc h a)) (.nil _), idle_snoc h a⟩

end Silmaril.Proofs.Wasm.Component.Algebra.Kahn
