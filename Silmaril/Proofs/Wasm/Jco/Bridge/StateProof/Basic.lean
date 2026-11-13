module

public import Silmaril.Wasm.Jco.Bridge.StateFix.Defs
public import Silmaril.Games.Answer.Thms
public import Silmaril.Games.PairProj.Thms
public import Silmaril.Proofs.Wasm.Jco.Bridge.IR

/-!
# The stateful component bridge: proofs

`Fuse.simpleComp [] W m` over a stateful module has one stateful instance (the module) and
otherwise handlers. Its strategy is

* the forwarding of the (empty) imports, below
* the module's machine `m.lts`, below
* the handler `topH W m` of the glue code and the `canon lift`s (`simpleComp_denU_state`).

The first environment extension (`ext 0`) is a right projection of a pairing
(`Strategy.pair_comp_ofHom_inr`); the second one and the exports are handlers, simplified by the
identities of `Silmaril.Proofs.Wasm.Jco.Bridge.IR` (`top_eq`). The module's machine is an answering
machine (`lts_eq`), so the handler above it collapses into the answering machine of
`(topH W m).overAns m.ans` (`Strategy.ofAns_comp_ofHandler`) and the forwarding below it
disappears (`Strategy.ofHandler_comp_ofAns`). Evaluating `overAns` gives `compAnsS`
(`overAns_eq`).
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Bridge.StateProof

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco.Fuse
open Silmaril.Wasm.Jco.Bridge
open Silmaril.Proofs.Wasm.Jco.Bridge

local notation "ofH" => Strategy.ofHandler

variable {σ : Type}

/-! ## The machines are answering machines -/

theorem step_eq (m : SMod σ) : SMod.Step m = LTS.AnsStep m.ans := by
  funext x l y
  apply propext
  constructor
  · intro h
    cases h with
    | ask s q => exact .ask s q
    | ret s q => exact .ret s q
  · intro h
    cases h with
    | ask s q => exact .ask s q
    | ret s q => exact .ret s q

theorem lts_eq (m : SMod σ) : m.lts = LTS.ofAns m.ans m.init := by
  show (⟨_, _, SMod.Step m⟩ : LTS _ _) = ⟨_, _, LTS.AnsStep m.ans⟩
  rw [step_eq]

theorem ansStep_eq (f : sigU.Op → σ → Option Payload × σ) :
    Silmaril.Wasm.Jco.Bridge.AnsStep f = LTS.AnsStep (E := sigU) (F := sigU) f := by
  funext x l y
  apply propext
  constructor
  · intro h
    cases h with
    | ask s q => exact .ask s q
    | ret s q => exact .ret s q
  · intro h
    cases h with
    | ask s q => exact .ask s q
    | ret s q => exact .ret s q

theorem ansLTS_eq (f : sigU.Op → σ → Option Payload × σ) (init : σ) :
    ansLTS f init = LTS.ofAns f init := by
  show (⟨_, _, Silmaril.Wasm.Jco.Bridge.AnsStep f⟩ : LTS _ _) = ⟨_, _, LTS.AnsStep f⟩
  rw [ansStep_eq]

/-! ## The component's strategy -/

theorem splitH_zero : splitH 0 = Handler.ofHom (Sig.Hom.inr sigU sigU) := by
  funext q
  simp [splitH, Handler.ofHom, Sig.Hom.inr]

/-- **The first environment extension is a right projection.** -/
theorem ext_zero {X : Sig.{0}} (D : Strategy X sigU) (N : Strategy sigU sigU) :
    ext 0 D N = D.comp N := by
  rw [ext, splitH_zero, Strategy.pair_comp_ofHom_inr]

/-- Extending any environment by a handler. -/
theorem ext_ofH_right {X : Sig.{0}} (e : Nat) (D : Strategy X sigU) (hN : Handler sigU sigU) :
    ext e D (ofH hN) = D.comp (ofH ((Handler.case (Handler.id sigU) hN).comp (splitH e))) := by
  rw [ext, ← Strategy.ofHandler_id, pairLaws.cp, ← Strategy.ofHandler_comp]

theorem coreNode_glueS (e : Nat) (g : Glue) (args : List Impl) :
    coreNode (baseSem (smodSem σ)) e (.glue g) args =
      ofH ((implsN e args g.imports.length).comp (g.handler.comp (widenH g.exports.length))) := by
  rw [Strategy.ofHandler_comp, Strategy.ofHandler_comp]
  rfl

/-- The `canon lift` adapters of the world exports, over forwarding to function `j` (a copy of
`Silmaril.Proofs.Wasm.Jco.Bridge.liftsH` with an exposed body). -/
@[expose] def liftsS (W : Iface) : Handler sigU sigU := fun q =>
  match W[q.1]? with
  | some x => runChain [.lift x.2] (fun a => .call (q.1, a) fun n => .pure n) q.2
  | none => .pure none

theorem exportsH_liftS (e b : Nat) (W : Iface) (hb : b + W.length ≤ e) :
    exportsH e (liftExports W b) = (implsH e (fwdFrom b W.length)).comp (liftsS W) := by
  funext q
  obtain ⟨j, p⟩ := q
  rcases hx : W[j]? with _ | x
  · simp [exportsH, implsH, liftExports_get, hx, Handler.comp, liftsS]
  have hj : j < W.length := (List.getElem?_eq_some_iff.1 hx).1
  have hf : (fwdFrom b W.length)[j]? = some (Impl.fwd (b + j)) := by
    simp [fwdFrom, List.getElem?_range hj]
  have hbj : b + j < e := by omega
  cases hd : (Adapter.lift x.2).down p with
  | none =>
    simp [exportsH, implsH, liftExports_get, hx, Handler.comp, liftsS, Impl.prog, runChain, hd]
  | some a =>
    simp [exportsH, implsH, liftExports_get, hx, Handler.comp, liftsS, Impl.prog, runChain, hd,
      Prog.interp_call, hf, Target.prog, hbj]

/-- The handler of the glue code and the `canon lift`s, above the module. -/
def topH (W : Iface) (m : SMod σ) : Handler (sigN m.exports.length) sigU :=
  (widenH m.exports.length).comp
    ((maskH m.exports.length).comp ((glueH (simpleAdaptor W m.exports).code).comp (liftsS W)))

/-- The handler identities above the module. -/
theorem top_eq (W : Iface) (k : Nat) (c : List Code) (n : Nat) (hn : n = W.length)
    (hc : c.length ≤ W.length) :
    ((Handler.case (Handler.id sigU) ((implsN k (fwdFrom 0 k) k).comp
        (((widenH k).comp ((glueH c).comp (narrowH n))).comp (widenH n)))).comp
      (splitH k)).comp (exportsH (k + n) (liftExports W k)) =
    (maskH k).comp ((glueH c).comp (liftsS W)) := by
  subst hn
  have hle : k + W.length ≤ k + W.length := Nat.le_refl _
  rw [exportsH_liftS _ _ _ hle]
  simp only [Handler.comp_assoc', case_split_r _ _ _ _ hle, implsN_widenH_r, fwdFrom_zero,
    implsH_fwd, maskH_maskH_r, narrowH_widenH_r, glueH_maskH_r _ _ hc]

/-- **The component's strategy**: the module's machine between the forwarding of the imports
and `topH`. -/
theorem simpleComp_denU_state (W : Iface) (m : SMod σ) :
    (simpleComp [] W m).denU (baseSem (smodSem σ)) =
      (ofH ((maskH 0).comp (implsN 0 [] 0))).comp
        ((Strategy.ofLTS m.lts).comp (ofH (topH W m))) := by
  have hge : (simpleAdaptor W m.exports).exports.length = W.length := by simp [simpleAdaptor]
  have hc : (simpleAdaptor W m.exports).code.length ≤ W.length := by simp [simpleAdaptor]
  have ht := top_eq W m.exports.length (simpleAdaptor W m.exports).code _ hge hc
  simp only [simpleComp, adaptorComp, Comp.denU, denNodes, Node.den, envAfter, Node.width]
  show (ext (0 + m.exports.length) (ext 0 (ofH (maskH 0))
      ((ofH (implsN 0 [] 0)).comp ((Strategy.ofLTS m.lts).comp (ofH (widenH m.exports.length)))))
      (coreNode (baseSem (smodSem σ)) (0 + m.exports.length) (.glue (simpleAdaptor W m.exports))
        (fwdFrom 0 m.exports.length))).comp
      (ofH (exportsH (0 + m.exports.length + (simpleAdaptor W m.exports).exports.length)
        (liftExports W (0 + m.exports.length)))) = _
  simp only [Nat.zero_add]
  rw [ext_zero, coreNode_glueS, ext_ofH_right, Strategy.comp_assoc, ← Strategy.ofHandler_comp]
  erw [ht]
  simp only [Strategy.comp_assoc]
  rw [← Strategy.ofHandler_comp (widenH _), ← Strategy.comp_assoc (ofH (maskH 0)),
    ← Strategy.ofHandler_comp]
  rfl

/-! ## Evaluating the handler above the module -/

open Silmaril.Wasm.Jco (PTy PVal Meta inMem)

theorem nameIdx_lt_iffS (m : SMod σ) (n : String) :
    nameIdx m.exports n < m.exports.length ↔ m.exports.any (·.1 == n) = true := by
  rw [nameIdx, List.findIdx_lt_length, List.any_eq_true]

theorem exports_nameIdx (m : SMod σ) (n : String) (h : nameIdx m.exports n < m.exports.length) :
    (m.exports[nameIdx m.exports n]'h).1 = n := by
  have hb : (m.exports[nameIdx m.exports n].1 == n) = true := List.findIdx_getElem (w := h)
  exact beq_iff_eq.1 hb

theorem topH_none (md : Meta) (m : SMod σ) (j : Nat) (hs : md.world[j]? = none) (p : Payload)
    (s : σ) : (topH (Meta.iface md) m).overAns m.ans (j, p) s = (none, s) := by
  have hx : (Meta.iface md)[j]? = none := by simp [Meta.iface, hs]
  simp [topH, Handler.overAns, Handler.comp, liftsS, hx, Prog.runAns]

theorem topH_flat (md : Meta) (m : SMod σ) (j : Nat) (sg : Silmaril.Wasm.Jco.Sig)
    (hs : md.world[j]? = some sg) (xs : List Flat) (s : σ) :
    (topH (Meta.iface md) m).overAns m.ans (j, .flat xs) s = (none, s) := by
  have hx : (Meta.iface md)[j]? = some (sg.name, Sig.toFuncTy sg) := by simp [Meta.iface, hs]
  simp [topH, Handler.overAns, Handler.comp, liftsS, hx, Prog.runAns, runChain, Adapter.down]

theorem topH_vals (md : Meta) (m : SMod σ) (j : Nat) (sg : Silmaril.Wasm.Jco.Sig)
    (hs : md.world[j]? = some sg) (hr : inMem sg.result = false) (vs : List Val) (s : σ) :
    (topH (Meta.iface md) m).overAns m.ans (j, .vals vs) s = compAnsS md m (j, .vals vs) s := by
  have hx : (Meta.iface md)[j]? = some (sg.name, Sig.toFuncTy sg) := by simp [Meta.iface, hs]
  have hcode : (simpleAdaptor (Meta.iface md) m.exports).code[j]? =
      some (Code.delegate (nameIdx m.exports sg.name)) := by simp [simpleAdaptor, hx]
  have hl : ∀ ys, (Adapter.lift (Sig.toFuncTy sg)).up (.flat ys) =
      (liftRes sg.result ys).map resPayload := fun ys => liftArgs_liftRes sg.result hr ys
  rcases hc : checkLower (sg.params.map PTy.toVal) vs with _ | xs
  · simp [topH, Handler.overAns, Handler.comp, liftsS, hx, Prog.runAns, runChain,
      Adapter.down, Sig.toFuncTy, hc, compAnsS, hs]
  · show (topH (Meta.iface md) m).overAns m.ans (j, .vals vs) s = compAnsS md m (j, .vals vs) s
    by_cases hk : nameIdx m.exports sg.name < m.exports.length
    · show (topH (Meta.iface md) m).overAns m.ans (j, .vals vs) s = compAnsS md m (j, .vals vs) s
      have hany : m.exports.any (·.1 == sg.name) = true := (nameIdx_lt_iffS m sg.name).1 hk
      have hn : (m.exports[nameIdx m.exports sg.name]'hk).1 = sg.name := exports_nameIdx m sg.name hk
      rcases hf : m.fn sg.name xs s with _ | ⟨ys, s'⟩
      · simp [topH, Handler.overAns, Handler.comp, liftsS, hx, Prog.interp, Prog.runAns, runChain,
          Adapter.down, Sig.toFuncTy, hc, compAnsS, hs, glueH, hcode, Code.run, cont, maskH,
          Target.prog, hk, widenH, SMod.ans, hn, hf, SMod.callN, hany]
      · simpa [topH, Handler.overAns, Handler.comp, liftsS, hx, Prog.interp, Prog.runAns, runChain,
          Adapter.down, Sig.toFuncTy, hc, compAnsS, hs, glueH, hcode, Code.run, cont, maskH,
          Target.prog, hk, widenH, SMod.ans, hn, hf, SMod.callN, hany] using hl ys
    · have hany : m.exports.any (·.1 == sg.name) = false :=
        Bool.eq_false_iff.2 fun hb => hk ((nameIdx_lt_iffS m sg.name).2 hb)
      simp [topH, Handler.overAns, Handler.comp, liftsS, hx, Prog.interp, Prog.runAns, runChain,
        Adapter.down, Sig.toFuncTy, hc, compAnsS, hs, glueH, hcode, Code.run, cont, maskH,
        Target.prog, hk, SMod.callN, hany]

/-- **The answers of the handler above the module are `compAnsS`.** -/
theorem overAns_eq (md : Meta) (m : SMod σ) (h : ∀ s ∈ md.world, inMem s.result = false) :
    (topH (Meta.iface md) m).overAns m.ans = compAnsS md m := by
  funext q s
  obtain ⟨j, p⟩ := q
  rcases hs : md.world[j]? with _ | sg
  · rw [topH_none md m j hs]
    cases p <;> simp [compAnsS, hs]
  · have hr : inMem sg.result = false := h sg (List.mem_of_getElem? hs)
    cases p with
    | flat xs => rw [topH_flat md m j sg hs]; rfl
    | vals vs => exact topH_vals md m j sg hs hr vs s

end Silmaril.Proofs.Wasm.Jco.Bridge.StateProof
