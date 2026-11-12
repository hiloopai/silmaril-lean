module

public import Silmaril.Wasm.Jco.Bridge.Defs
public import Silmaril.Wasm.Component.Env.Thms
public import Silmaril.Wasm.Component.Laws.Defs

/-!
# The IR side of the bridge: proofs

The adaptor-style component of the simple FFI style over a pure module has only handler
instances, so its strategy is a handler (`ext_ofH`, by the pairing law `cp`). The handler
identities at the interface boundaries (masks, splits, forwarding) reduce it to the composite
`finalH`: the module's handler below the glue code below the `canon lift` adapters (`liftsH`).
Evaluating that composite on a question gives `bridgeAns` (`finalH_eq`).

The handler identities `ext_ofH`, `case_inr_call`, `case_split_fwdFrom`, `implsN_comp_widenH`,
`narrowH_comp_widenH`, `glueH_comp_maskH` restate (and re-prove) those of the `Fuse` proofs,
which this topic does not import.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Bridge

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco.Fuse
open Silmaril.Wasm.Jco.Bridge

local notation "ofH" => Strategy.ofHandler

/-! ## Handler identities -/

theorem ext_ofH (e : Nat) (hD hN : Handler sigU sigU) :
    ext e (ofH hD) (ofH hN) =
      ofH (hD.comp ((Handler.case (Handler.id sigU) hN).comp (splitH e))) := by
  rw [ext, ← Strategy.ofHandler_id, pairLaws.cp, ← Strategy.ofHandler_comp,
    ← Strategy.ofHandler_comp]

theorem case_inr_call (H : Handler sigU sigU) (q : sigU.Op) :
    (Prog.call (E := sigU ⊕ₛ sigU) (.inr q) fun n => .pure n).interp
      (Handler.case (Handler.id sigU) H) = H q := by
  exact Prog.bind_pure (H q)

theorem case_split_fwdFrom (H : Handler sigU sigU) (e n k : Nat) (hk : e + k ≤ n) :
    ((Handler.case (Handler.id sigU) H).comp (splitH e)).comp (implsH n (fwdFrom e k)) =
      H.comp (maskH k) := by
  funext q
  obtain ⟨j, x⟩ := q
  by_cases hj : j < k
  · have h₁ : (fwdFrom e k)[j]? = some (Impl.fwd (e + j)) := by
      simp [fwdFrom, List.getElem?_range hj]
    have h₂ : e + j < n := by omega
    have h₃ : ¬ e + j < e := by omega
    simp only [Handler.comp, implsH, h₁, Impl.prog, runChain, Target.prog, h₂, ↓reduceIte,
      Prog.interp_call, Prog.interp_pure, Prog.bind_pure, splitH, h₃, maskH, hj]
    have h₄ : e + j - e = j := by omega
    rw [h₄]
    exact case_inr_call H (j, x)
  · have h₁ : (fwdFrom e k)[j]? = none := by simp [fwdFrom]; omega
    simp [Handler.comp, implsH, h₁, maskH, Target.prog, hj]

theorem case_split_zero (H : Handler sigU sigU) :
    (Handler.case (Handler.id sigU) H).comp (splitH 0) = H := by
  funext q
  obtain ⟨j, x⟩ := q
  have hs : splitH 0 (j, x) = .call (.inr (j, x)) fun n => .pure n := by simp [splitH]
  show ((splitH 0) (j, x)).interp _ = H (j, x)
  rw [hs]
  exact case_inr_call H (j, x)

theorem implsN_comp_widenH (e : Nat) (args : List Impl) (p : Nat) :
    (implsN e args p).comp (widenH p) = (implsH e args).comp (maskH p) := by
  funext q
  by_cases hq : q.1 < p
  · simp [Handler.comp, widenH, maskH, Target.prog, hq, Prog.interp_call, implsN]
  · simp [Handler.comp, widenH, maskH, Target.prog, hq]

theorem narrowH_comp_widenH (k : Nat) : (narrowH k).comp (widenH k) = maskH k := by
  funext q
  by_cases hq : q.1 < k
  · simp [Handler.comp, widenH, maskH, Target.prog, hq, Prog.interp_call, narrowH]
  · simp [Handler.comp, widenH, maskH, Target.prog, hq]

theorem glueH_comp_maskH (c : List Code) (n : Nat) (h : c.length ≤ n) :
    (glueH c).comp (maskH n) = glueH c := by
  funext q
  obtain ⟨j, x⟩ := q
  by_cases hj : j < n
  · simp [Handler.comp, maskH, Target.prog, hj, Prog.interp_call]
  · have h₁ : c[j]? = none := by simp; omega
    simp [Handler.comp, maskH, Target.prog, hj, glueH, h₁]

/-! ## The lift adapters -/

/-- The `canon lift` adapters of the world exports, over forwarding to function `j`. -/
def liftsH (W : Iface) : Handler sigU sigU := fun q =>
  match W[q.1]? with
  | some x => runChain [.lift x.2] (fun a => .call (q.1, a) fun n => .pure n) q.2
  | none => .pure none

theorem liftExports_get (W : Iface) : ∀ (b j : Nat),
    (liftExports W b)[j]? = W[j]?.map fun x => ⟨x.1, x.2, ⟨[.lift x.2], .call (b + j)⟩⟩ := by
  induction W with
  | nil => intro b j; rfl
  | cons x W ih =>
    intro b j
    cases j with
    | zero => rfl
    | succ j =>
      have e : b + 1 + j = b + (j + 1) := by omega
      simp only [liftExports, List.getElem?_cons_succ, ih (b + 1) j, e]

theorem exportsH_lift (e b : Nat) (W : Iface) (hb : b + W.length ≤ e) :
    exportsH e (liftExports W b) = (implsH e (fwdFrom b W.length)).comp (liftsH W) := by
  funext q
  obtain ⟨j, p⟩ := q
  rcases hx : W[j]? with _ | x
  · simp [exportsH, implsH, liftExports_get, hx, Handler.comp, liftsH]
  have hj : j < W.length := (List.getElem?_eq_some_iff.1 hx).1
  have hf : (fwdFrom b W.length)[j]? = some (Impl.fwd (b + j)) := by
    simp [fwdFrom, List.getElem?_range hj]
  have hbj : b + j < e := by omega
  cases hd : (Adapter.lift x.2).down p with
  | none =>
    simp [exportsH, implsH, liftExports_get, hx, Handler.comp, liftsH, Impl.prog, runChain, hd]
  | some a =>
    simp [exportsH, implsH, liftExports_get, hx, Handler.comp, liftsH, Impl.prog, runChain, hd,
      Prog.interp_call, hf, Target.prog, hbj]

/-! ## Right-associated forms -/

section Assoc

variable {E F G H : Sig.{0}}

theorem comp_r {a : Handler E F} {b : Handler F G} {c : Handler E G} (h : a.comp b = c)
    (r : Handler G H) : a.comp (b.comp r) = c.comp r := by
  rw [← Handler.comp_assoc', h]

theorem maskH_maskH_r (n : Nat) (r : Handler sigU H) :
    (maskH n).comp ((maskH n).comp r) = (maskH n).comp r := comp_r (maskH_comp_maskH n) r

theorem implsN_widenH_r (e : Nat) (args : List Impl) (n : Nat) (r : Handler sigU H) :
    (implsN e args n).comp ((widenH n).comp r) = (implsH e args).comp ((maskH n).comp r) := by
  rw [comp_r (implsN_comp_widenH e args n) r, Handler.comp_assoc']

theorem narrowH_widenH_r (k : Nat) (r : Handler sigU H) :
    (narrowH k).comp ((widenH k).comp r) = (maskH k).comp r := comp_r (narrowH_comp_widenH k) r

theorem glueH_maskH_r (c : List Code) (n : Nat) (h : c.length ≤ n) (r : Handler sigU H) :
    (glueH c).comp ((maskH n).comp r) = (glueH c).comp r := comp_r (glueH_comp_maskH c n h) r

theorem case_split_r (K : Handler sigU sigU) (e n k : Nat) (hk : e + k ≤ n) (r : Handler sigU H) :
    (Handler.case (Handler.id sigU) K).comp ((splitH e).comp ((implsH n (fwdFrom e k)).comp r)) =
      K.comp ((maskH k).comp r) := by
  rw [← Handler.comp_assoc', ← Handler.comp_assoc', case_split_fwdFrom K e n k hk,
    Handler.comp_assoc']

end Assoc

theorem fwdFrom_zero (n : Nat) : fwdFrom 0 n = (List.range n).map Impl.fwd := by
  simp [fwdFrom]

/-! ## The component as a handler -/

theorem coreNode_base (e : Nat) (m : PMod) (args : List Impl) :
    coreNode (baseSem pureSem) e (.base m) args =
      ofH ((implsN e args 0).comp (m.handler.comp (widenH m.exports.length))) := by
  rw [Strategy.ofHandler_comp, Strategy.ofHandler_comp]
  rfl

theorem coreNode_glue (e : Nat) (g : Glue) (args : List Impl) :
    coreNode (baseSem pureSem) e (.glue g) args =
      ofH ((implsN e args g.imports.length).comp (g.handler.comp (widenH g.exports.length))) := by
  rw [Strategy.ofHandler_comp, Strategy.ofHandler_comp]
  rfl

/-- The handler of the module's instance. -/
def nodeH (m : PMod) : Handler sigU sigU :=
  (implsN 0 [] 0).comp (m.handler.comp (widenH m.exports.length))

/-- The glue code of the simple FFI style. -/
def simpleCode (W : Iface) (m : PMod) : List Code :=
  W.map fun x => Code.delegate (nameIdx m.exports x.1)

/-- The composite handler of the component. -/
def finalH (W : Iface) (m : PMod) : Handler sigU sigU :=
  ((maskH 0).comp (nodeH m)).comp
    ((maskH m.exports.length).comp ((glueH (simpleCode W m)).comp (liftsH W)))

theorem simpleComp_denU (W : Iface) (m : PMod) :
    (simpleComp [] W m).denU (baseSem pureSem) = ofH (finalH W m) := by
  simp only [simpleComp, adaptorComp, Comp.denU, denNodes, Node.den, coreNode_base, coreNode_glue,
    ext_ofH, envAfter, Node.width]
  rw [← Strategy.ofHandler_comp]
  congr 1
  have hge : (simpleAdaptor W m.exports).exports.length = W.length := by simp [simpleAdaptor]
  have hc : (simpleCode W m).length ≤ W.length := by simp [simpleCode]
  show ((((maskH 0).comp ((Handler.case (Handler.id sigU)
      ((implsN 0 [] 0).comp (m.handler.comp (widenH m.exports.length)))).comp (splitH 0))).comp
    ((Handler.case (Handler.id sigU)
      ((implsN (0 + m.exports.length) (fwdFrom 0 m.exports.length) m.exports.length).comp
        (((widenH m.exports.length).comp ((glueH (simpleCode W m)).comp
          (narrowH (simpleAdaptor W m.exports).exports.length))).comp
          (widenH (simpleAdaptor W m.exports).exports.length)))).comp
      (splitH (0 + m.exports.length)))).comp
    (exportsH (0 + m.exports.length + (simpleAdaptor W m.exports).exports.length)
      (liftExports W (0 + m.exports.length)))) = _
  simp only [Nat.zero_add]
  have hle : m.exports.length + W.length ≤
      m.exports.length + (simpleAdaptor W m.exports).exports.length := by omega
  rw [exportsH_lift _ _ _ hle, case_split_zero]
  simp only [Handler.comp_assoc', case_split_r _ _ _ _ hle, implsN_widenH_r, fwdFrom_zero,
    implsH_fwd, maskH_maskH_r, narrowH_widenH_r]
  simp only [hge, maskH_maskH_r, glueH_maskH_r _ _ hc, finalH, nodeH, Handler.comp_assoc']

/-! ## Evaluating the handler -/

/-- What the module answers to the glue's call of the export named `n`. -/
def glueAns (m : PMod) (n : String) : Payload → Option Payload
  | .flat xs => if nameIdx m.exports n < m.exports.length then (m.fn n xs).map .flat else none
  | .vals _ => none

theorem fn_nameIdx (m : PMod) (n : String) (h : nameIdx m.exports n < m.exports.length)
    (xs : List Flat) : m.fn (m.exports[nameIdx m.exports n]'h).1 xs = m.fn n xs := by
  have hb : (m.exports[nameIdx m.exports n].1 == n) = true := List.findIdx_getElem (w := h)
  rw [beq_iff_eq.1 hb]

theorem finalH_none (W : Iface) (m : PMod) (j : Nat) (hx : W[j]? = none) (p : Payload) :
    finalH W m (j, p) = .pure none := by
  simp [finalH, Handler.comp, liftsH, hx]

theorem finalH_some (W : Iface) (m : PMod) (j : Nat) (x : String × FuncTy) (hx : W[j]? = some x)
    (p : Payload) :
    finalH W m (j, p) =
      .pure (((Adapter.lift x.2).down p).bind fun a => (glueAns m x.1 a).bind (Adapter.lift x.2).up) := by
  have hc : (simpleCode W m)[j]? = some (Code.delegate (nameIdx m.exports x.1)) := by
    simp [simpleCode, hx]
  rcases hd : (Adapter.lift x.2).down p with _ | a
  · simp [finalH, Handler.comp, liftsH, hx, runChain, hd]
  cases a with
  | vals vs => simp [finalH, Handler.comp, liftsH, hx, runChain, hd, Prog.interp_call, glueH, hc, glueAns]
  | flat xs =>
    by_cases hk : nameIdx m.exports x.1 < m.exports.length
    · rcases hf : m.fn x.1 xs with _ | ys <;>
        simp [finalH, Handler.comp, liftsH, hx, runChain, hd, Prog.interp_call, glueH, hc, glueAns,
          Code.run, cont, maskH, Target.prog, hk, nodeH, widenH, PMod.handler, fn_nameIdx m x.1 hk,
          hf]
    · simp [finalH, Handler.comp, liftsH, hx, runChain, hd, Prog.interp_call, glueH, hc, glueAns,
        Code.run, cont, maskH, Target.prog, hk]

/-! ## The world's interface -/

open Silmaril.Wasm.Jco (PTy PVal Meta inMem)

theorem nameIdx_lt_iff (m : PMod) (n : String) :
    nameIdx m.exports n < m.exports.length ↔ m.exports.any (·.1 == n) = true := by
  rw [nameIdx, List.findIdx_lt_length, List.any_eq_true]

theorem glueAns_flat (m : PMod) (n : String) (xs : List Flat) :
    glueAns m n (.flat xs) = (m.callN n xs).map .flat := by
  by_cases hk : nameIdx m.exports n < m.exports.length
  · simp [glueAns, hk, PMod.callN, (nameIdx_lt_iff m n).1 hk]
  · have hn : m.exports.any (·.1 == n) = false :=
      Bool.eq_false_iff.2 fun hb => hk ((nameIdx_lt_iff m n).2 hb)
    simp [glueAns, hk, PMod.callN, hn]

theorem liftArgs_liftRes (r : Option PTy) (hr : inMem r = false) (ys : List Flat) :
    (liftArgs (Sig.toFuncTy ⟨"", [], r⟩).results ys).map .vals = (liftRes r ys).map resPayload := by
  rcases r with _ | (t | _ | _)
  · cases ys <;> rfl
  · show (liftArgs [t] ys).map Payload.vals = (liftRes (some (.val t)) ys).map resPayload
    rcases ht : t.lift ys with _ | ⟨v, rest⟩
    · simp [liftArgs, ValTy.liftList, liftRes, ht]
    · cases rest <;> simp [liftArgs, ValTy.liftList, liftRes, ht, resPayload]
  · cases hr
  · cases hr

theorem bridge_vals (m : PMod) (s : Silmaril.Wasm.Jco.Sig) (hr : inMem s.result = false) (vs : List Val) :
    (((Adapter.lift (Sig.toFuncTy s)).down (.vals vs)).bind fun a =>
        (glueAns m s.name a).bind (Adapter.lift (Sig.toFuncTy s)).up) =
      (pureCall m s vs).map resPayload := by
  have hl : ∀ ys, (Adapter.lift (Sig.toFuncTy s)).up (.flat ys) =
      (liftRes s.result ys).map resPayload := fun ys => liftArgs_liftRes s.result hr ys
  rcases hc : checkLower (s.params.map PTy.toVal) vs with _ | xs
  · simp [Adapter.down, Sig.toFuncTy, hc, pureCall]
  · rcases hn : m.callN s.name xs with _ | ys
    · simp [Adapter.down, Sig.toFuncTy, hc, pureCall, glueAns_flat, hn]
    · have hu := hl ys
      simp only [Adapter.down, Sig.toFuncTy] at hu ⊢
      simp [hc, pureCall, glueAns_flat, hn, hu]

/-- **The IR side**: the adaptor-style component of the simple FFI style over a pure module is
the handler `bridgeAns`. -/
theorem simpleComp_bridge (md : Meta) (m : PMod) (h : ∀ s ∈ md.world, inMem s.result = false) :
    (simpleComp [] (Meta.iface md) m).denU (baseSem pureSem) =
      ofH (fun q => .pure (bridgeAns md m q)) := by
  rw [simpleComp_denU]
  congr 1
  funext q
  obtain ⟨j, p⟩ := q
  rcases hs : md.world[j]? with _ | s
  · have hx : (Meta.iface md)[j]? = none := by simp [Meta.iface, hs]
    rw [finalH_none _ m j hx]
    cases p <;> simp [bridgeAns, hs]
  · have hx : (Meta.iface md)[j]? = some (s.name, Sig.toFuncTy s) := by simp [Meta.iface, hs]
    have hr : inMem s.result = false := h s (List.mem_of_getElem? hs)
    rw [finalH_some _ m j _ hx]
    cases p with
    | flat xs => simp [bridgeAns, Adapter.down]
    | vals vs => simp only [bridgeAns, hs, bridge_vals m s hr vs]

end Silmaril.Proofs.Wasm.Jco.Bridge
