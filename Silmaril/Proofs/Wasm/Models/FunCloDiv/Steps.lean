module

public import Silmaril.Proofs.Wasm.Models.FunCloDiv.Bridge

/-!
# Divergence in the every-run logic: the instruction groups of the compiled code

Step-indexed versions of FunCompile's instruction-group lemmas (`twp_localGet`, `twp_localSet`,
`twp_box`, `twp_unbox`, `twp_castBox`, `twp_getBox`, `twp_newBox`, `twp_constBox`): each is
the total lemma on the instruction alone followed by `safe_of_twp`, so a diverging continuation
can follow it.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCloDiv

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Models.FunCompile (anyref dBox lx fx boxIdx boxRef unbox)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK twp_unbox twp_box twp_castBox twp_getBox
  twp_newBox twp_localGet twp_localSet twp_constBox)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- One instruction, totally correct, then a partial continuation. -/
theorem safe_bridge {n : Nat} {s : Store H} {f : Frame} {W : List Val} {i : Instr}
    {rest : List Admin} {Q : Post H}
    (h : TWP P host s f (vals W ++ [.plain i]) (thenSafe P host Q n rest)) :
    Safe P host Q n ⟨s, f, vals W ++ .plain i :: rest⟩ := by
  have h' : Safe P host Q n ⟨s, f, (vals W ++ [.plain i]) ++ rest⟩ := safe_of_twp h
  simpa using h'

theorem safe_localGet {n : Nat} {s : Store H} {f : Frame} (hf : FrameOK f) {us : List Val}
    {rest : List Admin} {Q : Post H} {x : Nat} {w : Val} (hx : f.locals[x]? = some (some w))
    (h : Safe P host Q n ⟨s, f, vals (us ++ [w]) ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals us ++ .plain (.localGet (lx x)) :: rest⟩ :=
  safe_bridge (twp_localGet hf hx (twp_thenSafe' h))

theorem safe_localSet {n : Nat} {s : Store H} {f : Frame} (hf : FrameOK f) {us : List Val}
    {rest : List Admin} {Q : Post H} {x : Nat} {w : Val} (hx : x < f.locals.length)
    (h : Safe P host Q n ⟨s, f.setLocal (lx x) w, vals us ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals (us ++ [w]) ++ .plain (.localSet (lx x)) :: rest⟩ :=
  safe_bridge (twp_localSet hf hx (twp_thenSafe' h))

theorem safe_box {n : Nat} {s : Store H} {f : Frame} {us : List Val} {rest : List Admin}
    {Q : Post H} {k : BitVec 32}
    (h : Safe P host Q n ⟨s, f, vals (us ++ [.ref (.i31 (k.setWidth 31))]) ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals (us ++ [.i32 k]) ++ .plain .refI31 :: rest⟩ :=
  safe_bridge (twp_box (twp_thenSafe' h))

theorem safe_castBox {n : Nat} {s : Store H} {f : Frame} (hf : FrameOK f) {us : List Val}
    {rest : List Admin} {Q : Post H} {addr : Nat} {fv : List FieldVal}
    (hs : s.structs[addr]? = some ⟨dBox, fv⟩)
    (h : Safe P host Q n ⟨s, f, vals (us ++ [.ref (.struct addr)]) ++ rest⟩) :
    Safe P host Q n
      ⟨s, f, vals (us ++ [.ref (.struct addr)]) ++ .plain (.refCast boxRef) :: rest⟩ :=
  safe_bridge (twp_castBox hf hs (twp_thenSafe' h))

theorem safe_getBox {n : Nat} {s : Store H} {f : Frame} (hf : FrameOK f) {us : List Val}
    {rest : List Admin} {Q : Post H} {addr : Nat} {w₀ w₁ : Val} {i : Nat} (hi : i < 2)
    (hs : s.structs[addr]? = some ⟨dBox, [.val w₀, .val w₁]⟩)
    (h : Safe P host Q n ⟨s, f, vals (us ++ [[w₀, w₁][i]]) ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals (us ++ [.ref (.struct addr)]) ++
      .plain (.structGet none boxIdx (fx i)) :: rest⟩ :=
  safe_bridge (twp_getBox hf hi hs (twp_thenSafe' h))

theorem safe_newBox {n : Nat} {s : Store H} {f : Frame} (hf : FrameOK f) {us : List Val}
    {rest : List Admin} {Q : Post H} {w₀ w₁ : Val}
    (h : Safe P host Q n ⟨s.addStruct ⟨dBox, [.val w₀, .val w₁]⟩, f,
      vals (us ++ [.ref (.struct s.structs.length)]) ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals (us ++ [w₀, w₁]) ++ .plain (.structNew boxIdx) :: rest⟩ :=
  safe_bridge (twp_newBox hf (twp_thenSafe' h))

theorem safe_unbox {n : Nat} {s : Store H} {f : Frame} {us : List Val} {rest : List Admin}
    {Q : Post H} {k : BitVec 31}
    (h : Safe P host Q n ⟨s, f, vals (us ++ [.i32 (k.setWidth 32)]) ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals (us ++ [.ref (.i31 k)]) ++ (expression unbox ++ rest)⟩ := by
  have ht : TWP P host s f (vals (us ++ [.ref (.i31 k)]) ++ (expression unbox ++ []))
      (thenSafe P host Q n rest) := twp_unbox (twp_thenSafe' h)
  have h' := safe_of_twp ht
  simpa using h'

theorem safe_constBox {n : Nat} {s : Store H} {f : Frame} {us : List Val} {rest : List Admin}
    {Q : Post H} {k : BitVec 32}
    (h : Safe P host Q n ⟨s, f, vals (us ++ [.ref (.i31 (k.setWidth 31))]) ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals us ++ (expression [.intConst .i32 k, .refI31] ++ rest)⟩ := by
  have ht : TWP P host s f (vals us ++ (expression [.intConst .i32 k, .refI31] ++ []))
      (thenSafe P host Q n rest) := twp_constBox (twp_thenSafe' h)
  have h' := safe_of_twp ht
  simpa using h'

end Silmaril.Proofs.Wasm.Models.FunCloDiv
