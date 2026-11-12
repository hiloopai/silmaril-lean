module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Defs

/-!
# Round 5: `ConfigOk ∧ BoundedNE → Typed`, reduced to `PosTypingNE`

`typed_of_configOk_ne` is `Round4.typed_of_configOk` with the export-free restriction threaded
through the recursion: the frame module and every frame in the code export nothing
(`NoExports`), so `PosTypingNE.moduleinst` applies to them, and so does `PosTypingNE.store` to
the store.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Pos

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type} {B : Builtins} {hn : H → String}

/-- `AdminsNE` splits over `++`. -/
theorem adminsNE_append : ∀ {a b : List Admin}, AdminsNE (a ++ b) ↔ AdminsNE a ∧ AdminsNE b
  | [], b => by simp [AdminsNE]
  | x :: a, b => by
    simp only [List.cons_append, AdminsNE]
    rw [adminsNE_append]
    exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨⟨h₁, h₂⟩, h₃⟩, fun ⟨⟨h₁, h₂⟩, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-- Source code holds no frame. -/
theorem adminsNE_expression : ∀ l : List Instr, AdminsNE (expression l)
  | [] => trivial
  | _ :: l => ⟨trivial, adminsNE_expression l⟩

/-- The frame of a valid frame judgement, bounded and export-free, is typed. -/
theorem typedV_frame_ok_ne (K : PosTypingNE B hn) {s : Store H} {f : Frame} {C : Context}
    (hf : FrameOk s f C) (hb : Round4.ModuleBnd f.module) (he : f.module.exports = []) :
    TypedV (simEnv B) frameT (frameV f) := by
  obtain ⟨C₀, lts, hm, -, -⟩ := hf
  exact Round4.typedV_frame_of (K.moduleinst _ _ _ hm hb he)

mutual
/-- **Every valid, bounded, export-free administrative instruction is typed.** -/
theorem adminOk_typed_ne (K : PosTypingNE B hn) {s : Store H} :
    ∀ {C : Context} {a : Admin} {it : InstrType}, AdminOk s C a it → Round4.AdminBnd a →
      AdminNE a → TypedV (simEnv B) instrsT (.list [adminToV a])
  | _, _, _, .plain h, hb, _ => typedV_list_single.2 (K.instr _ _ _ h hb)
  | _, _, _, .callRefType hok _, hb, _ => typedV_list_single.2 (K.callRefType _ hok hb)
  | _, _, _, .returnCallRefType hok _ _ _ _, hb, _ =>
    typedV_list_single.2 (K.returnCallRefType _ hok hb)
  | _, _, _, .ref _, _, _ => typedV_list_single.2 (Round4.typedV_refAdmin _)
  | _, _, _, .label (n := n) (cont := cont) _ hc hbody, hb, he => by
    have hcont := adminsOk_typed_ne K hc (Round4.adminsBnd_expression hb.1)
      (adminsNE_expression cont)
    rw [adminsToV_expression] at hcont
    exact FwdMem.typedV_label ((Typing.stateTyping_simEnv B).nat n) hcont
      (adminsOk_typed_ne K hbody hb.2 he)
  | _, _, _, .frame (n := n) hf _ hbody _, hb, he =>
    FwdMem.typedV_frame ((Typing.stateTyping_simEnv B).nat n)
      (typedV_frame_ok_ne K hf hb.1 he.1) (adminsOk_typed_ne K hbody hb.2 he.2)
  | _, _, _, .handler (n := n) _ hbody, hb, he =>
    FwdMem.typedV_handler ((Typing.stateTyping_simEnv B).nat n)
      (typedV_list_iff.2 fun u hu => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hu
        exact Round4.typedV_catch c)
      (adminsOk_typed_ne K hbody hb he)
  | _, _, _, .trap _, _, _ => typedV_list_single.2 Round4.typedV_trap
  | _, _, _, .throwRefInits _, _, _ => typedV_list_single.2 Round4.typedV_throwRef

/-- **Every valid, bounded, export-free code sequence is typed.** -/
theorem adminsOk_typed_ne (K : PosTypingNE B hn) {s : Store H} :
    ∀ {C : Context} {l : List Admin} {it : InstrType}, AdminsOk s C l it → Round4.AdminsBnd l →
      AdminsNE l → TypedV (simEnv B) instrsT (.list (adminsToV l))
  | _, _, _, .nil, _, _ => typedV_list_nil
  | _, _, _, .single h, hb, he => adminOk_typed_ne K h hb.1 he.1
  | _, _, _, .seq h₁ _ h₂, hb, he => by
    obtain ⟨hb₁, hb₂⟩ := Round4.adminsBnd_append.1 hb
    obtain ⟨he₁, he₂⟩ := adminsNE_append.1 he
    rw [adminsToV_append]
    exact typedV_list_append.2 ⟨adminsOk_typed_ne K h₁ hb₁ he₁, adminsOk_typed_ne K h₂ hb₂ he₂⟩
  | _, _, _, .cons ha _ hs, hb, he => by
    have h₁ := adminOk_typed_ne K ha hb.1 he.1
    have h₂ := adminsOk_typed_ne K hs hb.2 he.2
    exact typedV_list_cons_iff.2 ⟨typedV_list_single.1 h₁, h₂⟩
  | _, _, _, .sub h _ _, hb, he => adminsOk_typed_ne K h hb he
  | _, _, _, .frame h _, hb, he => adminsOk_typed_ne K h hb he
end

/-- **`ConfigOk ∧ BoundedNE → Typed`**, given `PosTypingNE`. -/
theorem typed_of_configOk_ne (K : PosTypingNE B hn) {c : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hb : BoundedNE c) : Typed (simEnv B) hn c := by
  obtain ⟨C, ⟨hs, hf⟩, hcode⟩ := hc
  have T := Typing.typingFacts_simEnv B hn
  exact (T.config c).2 ⟨(T.state _ _).2 ⟨K.store _ hs hb.1.store hb.1.storeBnd hb.2.store,
    typedV_frame_ok_ne K hf hb.1.frame hb.2.frame⟩, adminsOk_typed_ne K hcode hb.1.code hb.2.code⟩

/-- `PosTyping` gives `PosTypingNE` (vacuously: `PosTyping` is uninhabited, `not_posTyping`). -/
theorem posTypingNE_of_posTyping (K : Round4.PosTyping B hn) : PosTypingNE B hn where
  instr := K.instr
  callRefType := K.callRefType
  returnCallRefType := K.returnCallRefType
  moduleinst s m C hm hb _ := K.moduleinst s m C hm hb
  store s hs hs' hb _ := K.store s hs hs' hb

end Silmaril.Wasm.SpecTec.Sim.Round5.Pos
