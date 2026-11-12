module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.Types

/-!
# Round 5: export-free module instances are typed

`typedV_moduleinst_ne`: a module instance whose defined types are bounded (`Round4.ModuleBnd`)
and which exports nothing is a typed `moduleinst`, in every `simEnv B`, without validity. Its
types are typed by `typedV_deftype` and its addresses are naturals. This is
`PosTypingNE.moduleinst` (`moduleinst_ne`). The export-free restriction is necessary: with a
one-character export name no `simEnv B` types it (`not_typedV_moduleinst_of_export`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Pos

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_xaddr (x : IL.Id) (hx : x ∈ ["tagaddr", "globaladdr", "memaddr", "tableaddr",
    "funcaddr", "dataaddr", "elemaddr"]) :
    (simEnv B).findTyp? x = some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A list of addresses is an `xaddr*`. -/
theorem typedV_addrs (x : IL.Id) (hx : x ∈ ["tagaddr", "globaladdr", "memaddr", "tableaddr",
    "funcaddr", "dataaddr", "elemaddr"]) (l : List Nat) :
    TypedV (simEnv B) (.iterT (.varT x []) .list) (.list (l.map fun a => .num (.natN a))) :=
  typedV_list_iff.2 fun u hu => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hu
    exact Typing.typedV_alias (findTyp_xaddr x hx) (Typing.typedV_natAlias Typing.findTyp_addr a)

/-- One field of a record, typed. -/
theorem hasTypFields_cons_of {a : AtomS} {t : Typ} {fs : List TypField} {v : Value}
    {gs : List (AtomS × Value)} (hv : TypedV (simEnv B) t v)
    (hr : HasTypFields (simEnv B) VarEnv.empty fs gs) :
    HasTypFields (simEnv B) VarEnv.empty (.mk a t [] [] :: fs) ((a, v) :: gs) :=
  hasTypFields_cons_iff.2 ⟨_, _, rfl, hv _ ⟨rfl, rfl, rfl⟩, premsOk_nil, hr⟩

/-- **An export-free module instance with bounded types is a typed `moduleinst`.** -/
theorem typedV_moduleinst_ne (m : ModuleInst) (hb : Round4.ModuleBnd m) (he : m.exports = []) :
    TypedV (simEnv B) (.varT "moduleinst" [])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.moduleInstToValue CT m) := fun ρ hρ => by
  have htypes : TypedV (simEnv B) (.iterT (.varT "deftype" []) .list)
      (.list (m.types.map CT.defType)) := typedV_list_iff.2 fun u hu => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hu
    exact typedV_deftype d (hb.1 d hd)
  refine hasTyp_varT_struct (by simp [localTyp?, VarEnv.findTyp?, hρ.1])
    ConfigOk.findTyp_moduleinst' Equiv.evalArgs_nil matchArgs_nil ?_
  simp only [he, List.map_nil]
  exact hasTypFields_cons_of htypes <| hasTypFields_cons_of (typedV_addrs _ (by simp) _) <|
    hasTypFields_cons_of (typedV_addrs _ (by simp) _) <|
    hasTypFields_cons_of (typedV_addrs _ (by simp) _) <|
    hasTypFields_cons_of (typedV_addrs _ (by simp) _) <|
    hasTypFields_cons_of (typedV_addrs _ (by simp) _) <|
    hasTypFields_cons_of (typedV_addrs _ (by simp) _) <|
    hasTypFields_cons_of (typedV_addrs _ (by simp) _) <|
    hasTypFields_cons_of typedV_list_nil (hasTypFields_nil_iff.2 rfl)

/-- **`PosTypingNE.moduleinst`**, in every `simEnv B`. -/
theorem moduleinst_ne {H : Type} (s : Store H) (m : ModuleInst) (C : Context)
    (_ : ModuleInstOk s m C) (hb : Round4.ModuleBnd m) (he : m.exports = []) :
    TypedV (simEnv B) (.varT "moduleinst" [])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.moduleInstToValue CT m) :=
  typedV_moduleinst_ne m hb he

end Silmaril.Wasm.SpecTec.Sim.Round5.Pos
