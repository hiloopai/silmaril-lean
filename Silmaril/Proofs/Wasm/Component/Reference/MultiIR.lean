module

public import Silmaril.Proofs.Wasm.Component.Reference.MultiSeq
public import Silmaril.Proofs.Wasm.Component.Reference.MultiGames

/-!
# The IR side for sequences of calls

`seqSpecToIR : SeqSpecToIR`: a chain of returned calls of the canonical-ABI specification
threading the instance's Core store (`SeqSpec`), followed by a terminating outcome of the last
call at the store reached (`specAt`), is a multi-question play of `c.toComp.den (modSem P)`.

The play is built as rounds (`MultiGames`), layer by layer as in `SpecToIR`:

* the instance: the returned calls are complete activations of the instance's strategy, from
  store to store (`retAt_rounds`), and the last call is a two-move play at the store reached
  (`last_rounds`); `ScalarInstance.append_mem_of` puts them together;
* `core3Sem`'s export handler (`exportH_round`), `modSem` (`sem_rounds`);
* the core node, the pairing and `splitH` (`envS_rounds`);
* the export handler with the lift adapter, which answers an ill-typed call at once and every
  other call by one core call (`exportsH_trap`, `exportsH_call`);
* `atSizes` (`den_rounds`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-! ## Rounds at the untyped interface -/

/-- A round of an interface of `n` functions, at the untyped interface. -/
def Round.forget {n : Nat} (x : Round (sigN n)) : Round sigU := ⟨(x.1.1.val, x.1.2), x.2⟩

theorem hrounds_narrowH (k : Nat) :
    ∀ l : List (Round (sigN k)), HRounds (narrowH k) l (l.map Round.forget)
  | [] => .nil
  | ⟨q, a⟩ :: l => by
    show HRounds (narrowH k) (⟨q, a⟩ :: l) (⟨(q.1.val, q.2), a⟩ :: l.map Round.forget)
    exact .call (h := narrowH k) (q' := (q.1.val, q.2)) (k := fun r => .pure r) rfl rfl
      (hrounds_narrowH k l)

theorem hrounds_widenH (n : Nat) (l : List (Round (sigN n))) :
    HRounds (widenH n) (l.map Round.forget) l :=
  hrounds_map Round.forget l fun x _ => ⟨fun r => .pure r, dite_eq_left x.1.1.isLt, rfl⟩

theorem hrounds_splitH :
    ∀ l : List (Round sigU), HRounds (splitH 0) l (l.map (Round.inr (F₁ := sigU)))
  | [] => .nil
  | ⟨q, a⟩ :: l => by
    show HRounds (splitH 0) (⟨q, a⟩ :: l) (⟨Sum.inr q, a⟩ :: l.map (Round.inr (F₁ := sigU)))
    exact .call (h := splitH 0) (q' := Sum.inr q) (k := fun n => .pure n)
      (ite_eq_right (Nat.not_lt_zero _)) rfl
      (hrounds_splitH l)

/-- **The `atSizes` layer**, for several rounds. -/
theorem den_rounds {M : Type} [CoreModule M] (C : CoreSem M) (c : Comp M)
    {l : List (Round (sigN c.exports.length))}
    (h : twos (l.map Round.forget) ∈ c.denU C) : twos l ∈ c.den C := by
  unfold Comp.den atSizes
  exact twos_comp_ofHandler (hrounds_narrowH _ l) (twos_comp_upper h)

/-! ## The environment and the core layer -/

/-- **The core node, the pairing and `splitH`**, for several rounds. -/
theorem envS_rounds (C : CoreSem NumModule) (c : Simple)
    {lc : List (Round (CoreIface.sig (CoreModule.exports c.mod)))}
    (h : twos lc ∈ C.sem c.mod) : twos (lc.map Round.forget) ∈ envS C c := by
  have hN : twos (lc.map Round.forget) ∈ coreNode C 0 c.mod [] :=
    twos_comp_upper (twos_comp_ofHandler (hrounds_widenH _ lc) h)
  have hP : twos ((lc.map Round.forget).map (Round.inr (F₁ := sigU))) ∈
      (Strategy.id sigU).pair (coreNode C 0 c.mod []) := twos_pair_inr hN
  unfold envS ext
  exact twos_comp_upper (twos_comp_ofHandler (hrounds_splitH _) hP)

/-- The numeric instance of a module with its instance. -/
abbrev instNum {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) : NumInstance :=
  { inst := I, imports := [], exports := m.exports, imports_eq := hI.2.1, exports_eq := hI.2.2 }

/-- `core3Sem`'s export handler on a typed call of core export `k`. -/
theorem exportH_round {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I)
    {k : Nat} (hk : k < m.exports.length) {xs : List Flat}
    (hxs : xs.map (·.type) = m.exports[k].2.params) :
    exportH (instNum hI) (⟨k, hk⟩, .flat xs) =
      .call (opAt hI hk hxs) fun a => .pure (answerPayload a) := by
  have htyped : typed? (I.exports.get (opAt hI hk hxs).1).params (xs.map ofFlat) =
      some (opAt hI hk hxs).2 := by
    unfold typed?
    exact dite_eq_left (opAt hI hk hxs).2.2
  unfold exportH
  dsimp only
  erw [htyped]
  rfl

/-- **`modSem` on a module with an instance**, for several rounds. -/
theorem sem_rounds {P : Profile} {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) {lc : List (Round (CoreIface.sig (CoreModule.exports m)))}
    {li : List (Round I.F)} (H : HRounds (exportH (instNum hI)) lc li)
    (h : twos li ∈ I.strategy P I.store) : twos lc ∈ (modSem P).sem m := by
  rw [modSem_sem hI]
  exact twos_comp_upper (twos_comp_ofHandler H h)

/-! ## The export layer -/

theorem exportsH_trap (c : Simple) {j : Nat} (hj : j < c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (hcore : c.exports[j].core < c.mod.exports.length)
    (hl : checkLower c.exports[j].ty.params vs = none) :
    HRounds (exportsH c.mod.exports.length c.toComp.exports) [⟨(j, .vals vs), none⟩] [] :=
  .pure (h := exportsH c.mod.exports.length c.toComp.exports)
    (by rw [exportsH_toComp c hj vs hcore, hl]) .nil

theorem exportsH_call (c : Simple) {j : Nat} (hj : j < c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (hcore : c.exports[j].core < c.mod.exports.length)
    {xs : List Flat} (hl : checkLower c.exports[j].ty.params vs = some xs) (R A : Option Payload)
    (hA : R.bind (Adapter.up (.lift c.exports[j].ty)) = A) :
    HRounds (exportsH c.mod.exports.length c.toComp.exports) [⟨(j, .vals vs), A⟩]
      [⟨(c.exports[j].core, .flat xs), R⟩] :=
  .call (h := exportsH c.mod.exports.length c.toComp.exports) (q' := (c.exports[j].core, .flat xs))
    (k := fun (n : Option Payload) => .pure (n.bind (Adapter.up (.lift c.exports[j].ty))))
    (by rw [exportsH_toComp c hj vs hcore, hl]) (by rw [hA]) .nil

/-! ## Activations -/

theorem path_append {I : Silmaril.Wasm.Game.ScalarInstance} {P : Profile}
    {q₁ q₂ q₃ : I.HState} {c c' : List (Move I.E I.F)} (h : I.Path P q₁ c q₂)
    (h' : I.Path P q₂ c' q₃) : I.Path P q₁ (c ++ c') q₃ := by
  induction h with
  | nil => exact h'
  | cons ht _ ih => exact .cons ht (ih h')

/-- The checked lowering of typed values. -/
theorem checkLower_of_check {ts : List ValTy} {vs : List Silmaril.Wasm.Component.Val}
    (h : ValTy.checkList ts vs = true) : checkLower ts vs = some (lowerArgs ts vs) := by
  unfold checkLower
  rw [ite_eq_left h]

/-- A returned call is one complete activation of the instance and one round through the
export handlers. -/
theorem retAt_rounds {P : Profile} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hc : c.Good) (hI : c.mod.IsInst I) {j : Fin c.exports.length}
    {vs ws : List Silmaril.Wasm.Component.Val} {s s' : Store Nat} (hw : I.WellFormed s)
    (h : RetAt P c I c.exports[j] vs s ws s') :
    ∃ (li : List (Round I.F)) (lc : List (Round (CoreIface.sig (CoreModule.exports c.mod)))),
      I.Activation P s (twos li) s' ∧ HRounds (exportH (instNum hI)) lc li ∧
      HRounds (exportsH c.mod.exports.length c.toComp.exports)
        [⟨(j.val, .vals vs), some (.vals ws)⟩] (lc.map Round.forget) := by
  obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem j.isLt)
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  have hxs : (lowerArgs c.exports[j].ty.params vs).map (·.type) =
      c.mod.exports[c.exports[j].core].2.params := by
    rw [show c.mod.exports[c.exports[j].core] = (nm, c.exports[j].ty.flat) from hget]
    exact lowerList_types _ _ h.typed
  obtain ⟨t', cvs, ys, run, final, hys, hws⟩ := h.run
  have steps : Steps P Det.noHost (invoke s (I.addrs.getD c.exports[j].core 0)
      ((lowerArgs c.exports[j].ty.params vs).map ofFlat)) (t'.config s') :=
    internalP_steps (H := Nat) run
  obtain ⟨w, hw'⟩ := answer_at hI hw hk hxs steps (r := .values cvs) final
  have hpath : I.Activation P s (twos [⟨opAt hI hk hxs, w⟩]) s' :=
    .cons (.call s _) (.cons (.oret run final hw') (.nil _))
  have hpay : answerPayload w = some (.flat ys) := by
    rw [answerPayload_of_ofResult? hw']
    simp only [hys, Option.map_some]
  have hup : (some (Payload.flat ys)).bind (Adapter.up (.lift c.exports[j].ty)) =
      some (.vals ws) := by
    simp only [Option.bind_some, Adapter.up, hws, Option.map_some]
  refine ⟨[⟨opAt hI hk hxs, w⟩],
    [⟨(⟨c.exports[j].core, hk⟩, .flat (lowerArgs c.exports[j].ty.params vs)), some (.flat ys)⟩],
    hpath, .call (h := exportH (instNum hI)) (exportH_round hI hk hxs) (by rw [hpay]) .nil, ?_⟩
  exact exportsH_call c j.isLt vs hk (checkLower_of_check h.typed) _ _ hup

/-- What the IR answer `A` must be for a terminating reference outcome `b`. -/
def ObsAns : Outcome → Option Payload → Prop
  | .returns (some rs), A => ∃ ws, rs = ws.map toRefVal ∧ A = some (.vals ws)
  | .traps, A => A = none
  | _, _ => False

theorem obsAns_liftOutcome (ft : FuncTy) :
    ∀ r : Option (List Flat),
      ObsAns (liftOutcome ft r) ((r.map Payload.flat).bind (Adapter.up (.lift ft)))
  | none => rfl
  | some ys => by
    cases hl : liftArgs ft.results ys with
    | none =>
      show ObsAns (liftOutcome ft (some ys)) ((liftArgs ft.results ys).map Payload.vals)
      simp only [liftOutcome, hl, ObsAns, Option.map_none]
    | some ws =>
      show ObsAns (liftOutcome ft (some ys)) ((liftArgs ft.results ys).map Payload.vals)
      simp only [liftOutcome, hl, ObsAns, Option.map_some]
      exact ⟨ws, rfl, rfl⟩

/-- The rounds of a last call reaching the core. -/
theorem last_rounds_core {P : Profile} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hc : c.Good) (hI : c.mod.IsInst I) {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {s : Store Nat} (hw : I.WellFormed s) {xs : List Flat}
    (hl : checkLower c.exports[j].ty.params vs = some xs) {r : Option (List Flat)}
    (hr : r ∈ coreAt P I c.exports[j].core xs s) :
    ∃ (A : Option Payload) (li : List (Round I.F))
      (lc : List (Round (CoreIface.sig (CoreModule.exports c.mod)))),
      ObsAns (liftOutcome c.exports[j].ty r) A ∧ twos li ∈ I.strategy P s ∧
      HRounds (exportH (instNum hI)) lc li ∧
      HRounds (exportsH c.mod.exports.length c.toComp.exports)
        [⟨(j.val, .vals vs), A⟩] (lc.map Round.forget) := by
  obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem j.isLt)
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  obtain ⟨c', res, run, final, hres⟩ := hr
  have hxs : xs.map (·.type) = c.mod.exports[c.exports[j].core].2.params := by
    have hck : ValTy.checkList c.exports[j].ty.params vs = true ∧
        xs = ValTy.lowerList c.exports[j].ty.params vs := checkLower_eq hl
    rw [show c.mod.exports[c.exports[j].core] = (nm, c.exports[j].ty.flat) from hget, hck.2]
    exact lowerList_types _ _ hck.1
  obtain ⟨w, hw'⟩ := answer_at hI hw hk hxs run final
  have h2 : two (opAt hI hk hxs) w ∈ I.strategy P s :=
    Silmaril.Wasm.Game.ScalarInstance.ask_ans_iff.mpr ⟨c', res, run, final, hw'⟩
  have hA : ObsAns (liftOutcome c.exports[j].ty r)
      ((answerPayload w).bind (Adapter.up (.lift c.exports[j].ty))) := by
    rw [answerPayload_of_ofResult? hw', hres]
    exact obsAns_liftOutcome _ _
  exact ⟨_, [⟨opAt hI hk hxs, w⟩], [⟨(⟨c.exports[j].core, hk⟩, .flat xs), answerPayload w⟩],
    hA, h2, .call (h := exportH (instNum hI)) (exportH_round hI hk hxs) rfl .nil,
    exportsH_call c j.isLt vs hk hl _ _ rfl⟩

/-- **The last call**: a terminating outcome of the specification at a well-formed store is at
most one play of the instance at that store and one round through the export handlers. -/
theorem last_rounds {P : Profile} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hc : c.Good) (hI : c.mod.IsInst I) {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {s : Store Nat} (hw : I.WellFormed s) {b : Outcome}
    (hb : b ∈ specAt P c I c.exports[j] vs s) :
    b = .diverges ∨ ∃ (A : Option Payload) (li : List (Round I.F))
      (lc : List (Round (CoreIface.sig (CoreModule.exports c.mod)))),
      ObsAns b A ∧ twos li ∈ I.strategy P s ∧ HRounds (exportH (instNum hI)) lc li ∧
      HRounds (exportsH c.mod.exports.length c.toComp.exports)
        [⟨(j.val, .vals vs), A⟩] (lc.map Round.forget) := by
  obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem j.isLt)
  have hk : c.exports[j].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcore).1
  cases hl : checkLower c.exports[j].ty.params vs with
  | none =>
    have hb' : b = .traps := by simpa only [specAt, hl, Set.mem_singleton_iff] using hb
    exact .inr ⟨none, [], [], hb' ▸ rfl, (I.strategy P s).nil_mem, .nil,
      exportsH_trap c j.isLt vs hk hl⟩
  | some xs =>
    have hb' : b ∈ {b | ∃ r ∈ coreAt P I c.exports[j].core xs s,
        b = liftOutcome c.exports[j].ty r} ∪ {b | b = .diverges ∧
          Diverges P Det.noHost (invoke s (I.addrs.getD c.exports[j].core 0) (xs.map ofFlat))} := by
      simpa only [specAt, hl] using hb
    exact hb'.elim (fun ⟨r, hr, hbr⟩ => .inr (hbr ▸ last_rounds_core hc hI hw hl hr))
      (fun h => .inl h.1)

/-! ## Sequences -/

/-- The IR rounds of resolved calls `calls` with IR results `wss`. -/
def seqRounds (c : Simple) :
    List (Fin c.exports.length × List Silmaril.Wasm.Component.Val) →
    List (List Silmaril.Wasm.Component.Val) → List (Round (sigN c.toComp.exports.length))
  | (j, vs) :: cs, ws :: wss =>
    ⟨(⟨j, by simp [Simple.toComp]⟩, .vals vs), some (.vals ws)⟩ :: seqRounds c cs wss
  | _, _ => []

theorem seqMoves_eq (c : Simple) :
    ∀ (cs : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)), seqMoves c cs wss = twos (seqRounds c cs wss)
  | [], _ => rfl
  | (_, _) :: _, [] => rfl
  | (j, vs) :: cs, ws :: wss => by
    show _ :: _ :: seqMoves c cs wss = _ :: _ :: twos (seqRounds c cs wss)
    rw [seqMoves_eq c cs wss]

theorem seqRounds_append (c : Simple) (j : Fin c.exports.length)
    (vs ws : List Silmaril.Wasm.Component.Val) :
    ∀ (cs : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)), cs.length = wss.length →
      seqRounds c (cs ++ [(j, vs)]) (wss ++ [ws]) =
        seqRounds c cs wss ++ [⟨(⟨j, by simp [Simple.toComp]⟩, .vals vs), some (.vals ws)⟩]
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)
  | (j', vs') :: cs, ws' :: wss, h => by
    have h' : cs.length = wss.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff]
      using h
    show _ :: seqRounds c (cs ++ [(j, vs)]) (wss ++ [ws]) = _ :: (seqRounds c cs wss ++ _)
    rw [seqRounds_append c j vs ws cs wss h']

/-- **A sequence of returned calls** is a sequence of complete activations of the instance and
of rounds through the export handlers. -/
theorem seq_rounds {P : Profile} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hc : c.Good) (hI : c.mod.IsInst I) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)) (s s' : Store Nat), I.WellFormed s →
      SeqSpec P c I s (specCalls c calls) wss s' →
      I.WellFormed s' ∧ calls.length = wss.length ∧
      ∃ (li : List (Round I.F)) (lc : List (Round (CoreIface.sig (CoreModule.exports c.mod)))),
        I.Activation P s (twos li) s' ∧ HRounds (exportH (instNum hI)) lc li ∧
        HRounds (exportsH c.mod.exports.length c.toComp.exports)
          ((seqRounds c calls wss).map Round.forget) (lc.map Round.forget)
  | [], wss, s, s', hw, h => by
    cases h
    exact ⟨hw, rfl, [], [], .nil _, .nil, .nil⟩
  | (j, vs) :: calls, wss, s, s', hw, h => by
    have h' : SeqSpec P c I s ((c.exports[j], vs) :: specCalls c calls) wss s' := h
    cases h' with
    | @cons _ s₁ _ _ _ ws _ wss' hret hseq =>
      show I.WellFormed s' ∧ calls.length + 1 = wss'.length + 1 ∧ _
      have hw₁ : I.WellFormed s₁ := hret.wellFormed hI (hc.core _ (List.getElem_mem j.isLt)) hw
      obtain ⟨li₁, lc₁, hact₁, H₁, X₁⟩ := retAt_rounds hc hI hw hret
      obtain ⟨hw', hlen, li, lc, hact, H, X⟩ := seq_rounds hc hI calls wss' s₁ s' hw₁ hseq
      refine ⟨hw', by rw [hlen], li₁ ++ li, lc₁ ++ lc, ?_, H₁.append H, ?_⟩
      · rw [twos_append]
        exact path_append hact₁ hact
      · rw [List.map_append]
        exact X₁.append X

/-- The IR rounds of a sequence and of further rounds `U`, through every layer. -/
theorem seq_den {P : Profile} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : c.mod.IsInst I) {calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)}
    {wss : List (List Silmaril.Wasm.Component.Val)} {s : Store Nat}
    {U : List (Round (sigN c.toComp.exports.length))} {li₀ li : List (Round I.F)}
    {lc₀ lc : List (Round (CoreIface.sig (CoreModule.exports c.mod)))}
    (hact : I.Activation P I.store (twos li₀) s) (hli : twos li ∈ I.strategy P s)
    (H₀ : HRounds (exportH (instNum hI)) lc₀ li₀) (H : HRounds (exportH (instNum hI)) lc li)
    (X₀ : HRounds (exportsH c.mod.exports.length c.toComp.exports)
      ((seqRounds c calls wss).map Round.forget) (lc₀.map Round.forget))
    (X : HRounds (exportsH c.mod.exports.length c.toComp.exports)
      (U.map Round.forget) (lc.map Round.forget)) :
    twos (seqRounds c calls wss ++ U) ∈ c.toComp.den (modSem P) := by
  have hinst : twos (li₀ ++ li) ∈ I.strategy P I.store := by
    rw [twos_append]
    exact Silmaril.Wasm.Game.ScalarInstance.append_mem_of hact hli
  have hsem : twos (lc₀ ++ lc) ∈ (modSem P).sem c.mod := sem_rounds hI (H₀.append H) hinst
  have henv : twos (lc₀.map Round.forget ++ lc.map Round.forget) ∈ envS (modSem P) c :=
    List.map_append ▸ envS_rounds (modSem P) c hsem
  refine den_rounds (modSem P) c.toComp ?_
  rw [denU_toComp, List.map_append]
  exact twos_comp_ofHandler (X₀.append X) henv

/-- **The resolved calls of a sequence** are a play of the IR denotation. -/
theorem seq_prefix {P : Profile} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hc : c.Good) (hI : c.mod.IsInst I)
    {calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)}
    {wss : List (List Silmaril.Wasm.Component.Val)} {s : Store Nat}
    (hseq : SeqSpec P c I I.store (specCalls c calls) wss s) :
    seqMoves c calls wss ∈ c.toComp.den (modSem P) := by
  obtain ⟨-, -, li₀, lc₀, hact, H₀, X₀⟩ :=
    seq_rounds hc hI calls wss I.store s hI.1.choose_spec.ok hseq
  have h : twos (seqRounds c calls wss ++ []) ∈ c.toComp.den (modSem P) :=
    seq_den (U := []) (li := []) (lc := []) hI hact (I.strategy P s).nil_mem H₀ .nil X₀ .nil
  rw [List.append_nil] at h
  rw [seqMoves_eq]
  exact h

/-- The observation of the last call, from the rounds. -/
theorem seq_obs {P : Profile} {c : Simple}
    {calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)}
    {wss : List (List Silmaril.Wasm.Component.Val)} (hlen : calls.length = wss.length)
    {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val} :
    ∀ (b : Outcome) (A : Option Payload), ObsAns b A →
      twos (seqRounds c calls wss ++ [⟨(⟨j, by simp [Simple.toComp]⟩, .vals vs), A⟩]) ∈
        c.toComp.den (modSem P) →
      match b with
      | .returns (some rs) => ∃ ws, rs = ws.map toRefVal ∧
          seqMoves c (calls ++ [(j, vs)]) (wss ++ [ws]) ∈ c.toComp.den (modSem P)
      | .traps => seqMoves c calls wss ++
          [.inr (.ask (⟨j, by simp [Simple.toComp]⟩, .vals vs)),
            .inr (.ans (m := (⟨j, by simp [Simple.toComp]⟩, .vals vs)) none)] ∈
          c.toComp.den (modSem P)
      | _ => True
  | .returns (some _), _, ⟨ws, hrs, hAw⟩, hden => ⟨ws, hrs, by
      rw [seqMoves_eq, seqRounds_append c j vs ws calls wss hlen]
      exact hAw ▸ hden⟩
  | .traps, _, hAn, hden => by
      show seqMoves c calls wss ++ twos [⟨(⟨j, by simp [Simple.toComp]⟩, .vals vs), none⟩] ∈ _
      rw [seqMoves_eq, ← twos_append]
      exact hAn ▸ hden

/-- **The IR side for sequences** (proved). -/
theorem seqSpecToIR : SeqSpecToIR := by
  intro P c hc I hI calls wss s j vs b hseq hb
  obtain ⟨hw, hlen, li₀, lc₀, hact, H₀, X₀⟩ :=
    seq_rounds hc hI calls wss I.store s hI.1.choose_spec.ok hseq
  exact (last_rounds hc hI hw hb).elim (fun hd => hd ▸ trivial)
    fun ⟨A, li, lc, hA, hli, H, X⟩ => seq_obs hlen b A hA (seq_den (U := [_]) hI hact hli H₀ H X₀ X)

/-- `SeqIRObs` is the conclusion of `SeqSpecToIR`. -/
theorem seqIRObs_of {P : Profile} {c : Simple}
    {calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)}
    {wss : List (List Silmaril.Wasm.Component.Val)} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} :
    ∀ b : Outcome, (match b with
      | .returns (some rs) => ∃ ws, rs = ws.map toRefVal ∧
          seqMoves c (calls ++ [(j, vs)]) (wss ++ [ws]) ∈ c.toComp.den (modSem P)
      | .traps => seqMoves c calls wss ++
          [.inr (.ask (⟨j, by simp [Simple.toComp]⟩, .vals vs)),
            .inr (.ans (m := (⟨j, by simp [Simple.toComp]⟩, .vals vs)) none)] ∈
          c.toComp.den (modSem P)
      | _ => True) → SeqIRObs c (c.toComp.den (modSem P)) calls wss j vs b
  | .returns (some _), h => h
  | .returns none, _ => trivial
  | .traps, h => h
  | .deadlocks, _ => trivial
  | .diverges, _ => trivial

/-- **Soundness of the component IR for sequences of calls on one instance** (every profile,
every component choice profile): for a float-free simple component in the fragment within the
flat arities, every behaviour of instantiating `c.toRef` and calling its exports `calls`, each
resolving, then export `j`, on reference images of well-typed IR values, records reference
images of IR results `wss` of the earlier calls; the IR plays the earlier calls with these
results, and the last outcome is matched by the IR as in `SeqIRObs`. -/
theorem Simple.sound_seq (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple)
    (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      seqMoves c calls wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObs c (c.toComp.den (modSem P)) calls wss j vs p.2 := by
  obtain ⟨I, wss, s, hI, hseq, hp1, hp2⟩ :=
    seq_refToSpec P prof c hc hf hi ha calls j vs ht hvs p hp
  exact ⟨wss, hp1, seq_prefix hc hI hseq,
    seqIRObs_of p.2 (seqSpecToIR P c hc I hI calls wss s j vs p.2 hseq hp2)⟩

end Silmaril.Proofs.Wasm.Component.Reference
