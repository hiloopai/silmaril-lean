module

public import Silmaril.Wasm.Models.BinProfile.Thms

/-!
# The copied Lime1 encoder emits strict (`overlong = false`) encodings

The copied encoder (`Lime1.Binary.Encoder.encModule`) always writes the 1.0 literal
`call_indirect` byte, and its instruction-level soundness (`encInstr_sound`, `encExpr_sound`) is
already stated for every `overlong` flag; only the module-level `encModule_sound` and the four
declaration lemmas under it are stated at `overlong = true`. This file restates them for every
flag, with the same proofs:

* `encCode_soundW`, `encGlobal_soundW`, `encElem_soundW`, `encData_soundW`;
* **`encModule_soundW ov`**: every byte string the encoder returns is an `EncodesWith ov`
  encoding of its input. At `ov = false` this is the grammar `v1_iff_lime1` compares with 1.0.

New proofs over the copied encoder.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.BinWitV1

open Silmaril.Wasm Silmaril.Wasm.Binary
open Silmaril.Wasm.Lime1.Binary Silmaril.Wasm.Lime1.Binary.Encoder

theorem encCode_soundW (ov : Bool) (c : List V1.ValType × Lime1.Expr) (b : Bytes)
    (h : encCode c = .ok b) : Scalar.Binary.Code (Lime1.Binary.Expr ov) b c := by
  obtain ⟨_, hg₁, h⟩ := bind_ok h
  obtain ⟨bl, hl, h⟩ := bind_ok h
  obtain ⟨be, he, h⟩ := bind_ok h
  obtain ⟨_, hg₂, h⟩ := bind_ok h
  cases h
  have hv : Vec (fun b (p : Nat × V1.ValType) => Scalar.Binary.Locals b (List.replicate p.1 p.2))
      bl (runs c.1) := encVec_sound (fun p b hp => by
        obtain ⟨_, hg, hp⟩ := bind_ok hp
        cases hp
        exact .mk (encU_spec _ 32 (by decide) (guardE_ok hg)) (encValType_spec p.2)) _ _ hl
  have hv' := Scalar.Binary.vec_map (G' := Scalar.Binary.Locals)
    (fun p : Nat × V1.ValType => List.replicate p.1 p.2) (fun h => h) hv
  have hf := Scalar.Binary.Func.mk hv' (encExpr_sound ov c.2 be he)
    (by rw [runs_flatten]; exact guardE_ok hg₁)
  rw [runs_flatten] at hf
  exact .mk (encU_spec _ 32 (by decide) (guardE_ok hg₂)) rfl hf

theorem encGlobal_soundW (ov : Bool) (g : Lime1.Global) (b : Bytes) (h : encGlobal g = .ok b) :
    Scalar.Binary.Global (Lime1.Binary.Expr ov) b g := by
  obtain ⟨e, he, h⟩ := bind_ok h
  cases h
  exact .mk (encGlobalType_spec g.type) (encExpr_sound ov g.init e he)

theorem encElem_soundW (ov : Bool) (el : Lime1.Elem) (b : Bytes) (h : encElem el = .ok b) :
    Scalar.Binary.Elem (Lime1.Binary.Expr ov) b el := by
  obtain ⟨e, he, h⟩ := bind_ok h
  obtain ⟨ys, hys, h⟩ := bind_ok h
  cases h
  exact .mk (encU_index el.table) (encExpr_sound ov el.offset e he)
    (encVec_sound (fun x b h => by cases h; exact encU_index x) _ _ hys)

theorem encData_soundW (ov : Bool) (d : Lime1.Data) (b : Bytes) (h : encData d = .ok b) :
    Scalar.Binary.Data (Lime1.Binary.Expr ov) b d := by
  obtain ⟨e, he, h⟩ := bind_ok h
  obtain ⟨bs, hbs, h⟩ := bind_ok h
  cases h
  have hd := Scalar.Binary.Data.mk (G := Lime1.Binary.Expr ov) (encU_index d.memory)
    (encExpr_sound ov d.offset e he)
    (encVec_sound (G := Silmaril.Wasm.Binary.Byte) (fun x b h => by cases h; exact .mk x) _ _ hbs)
  rcases d with ⟨m, o, ⟨arr⟩⟩
  simpa using hd

/-- The module grammar from the eleven sections the encoder emits. -/
theorem encModule_of_sections (ov : Bool) (m : Lime1.Module)
    {bty bim bfn btb bme bgl bex bst bel bco bda : Bytes}
    (hty : encSection 1 (encVec encFuncType) m.types = .ok bty)
    (him : encSection 2 (encVec encImport) m.imports = .ok bim)
    (hfn : encSection 3 (encVec fun x => .ok (encU (Idx.toNat x))) (m.funcs.map (·.type)) = .ok bfn)
    (htb : encSection 4 (encVec fun t => .ok (encTableType t)) m.tables = .ok btb)
    (hme : encSection 5 (encVec fun t => .ok (encMemType t)) m.memories = .ok bme)
    (hgl : encSection 6 (encVec encGlobal) m.globals = .ok bgl)
    (hex : encSection 7 (encVec encExport) m.exports = .ok bex)
    (hst : encSection 8 encStart m.start.toList = .ok bst)
    (hel : encSection 9 (encVec encElem) m.elems = .ok bel)
    (hco : encSection 10 (encVec encCode) (m.funcs.map fun f => (f.locals, f.body)) = .ok bco)
    (hda : encSection 11 (encVec encData) m.data = .ok bda) :
    EncodesWith ov (magic ++ version ++ bty ++ bim ++ bfn ++ btb ++ bme ++ bgl ++ bex ++ bst ++
      bel ++ bco ++ bda) m := by
  simpa only [zipFuncs_funcs, List.append_nil, Option.head?_toList] using
    Scalar.Binary.Module.mk (G := Lime1.Binary.Expr ov) .nil
    (encSection_sound (fun xs b h => encVec_sound encFuncType_sound xs b h) _ _ hty) .nil
    (encSection_sound (fun xs b h => encVec_sound encImport_sound xs b h) _ _ him) .nil
    (encSection_sound (fun xs b h => encVec_sound
      (G := Index (k := .type_)) (fun x b h => by cases h; exact encU_index x) xs b h) _ _ hfn)
    .nil
    (encSection_sound (fun xs b h => encVec_sound
      (fun t b h => by cases h; exact encTableType_spec t) xs b h) _ _ htb) .nil
    (encSection_sound (fun xs b h => encVec_sound
      (fun t b h => by cases h; exact encMemType_spec t) xs b h) _ _ hme) .nil
    (encSection_sound (fun xs b h => encVec_sound (encGlobal_soundW ov) xs b h) _ _ hgl) .nil
    (encSection_sound (fun xs b h => encVec_sound encExport_sound xs b h) _ _ hex) .nil
    (StartSec.mk (encSection_sound encStart_sound _ _ hst)) .nil
    (encSection_sound (fun xs b h => encVec_sound (encElem_soundW ov) xs b h) _ _ hel) .nil
    (encSection_sound (fun xs b h => encVec_sound (encCode_soundW ov) xs b h) _ _ hco) .nil
    (encSection_sound (fun xs b h => encVec_sound (encData_soundW ov) xs b h) _ _ hda) .nil
    (by simp)

/-- **The encoder is sound for every `overlong` flag.** -/
theorem encModule_soundW (ov : Bool) (m : Lime1.Module) (b : Bytes) (h : encModule m = .ok b) :
    EncodesWith ov b m := by
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨bty, hty, h⟩ := bind_ok h
  obtain ⟨bim, him, h⟩ := bind_ok h
  obtain ⟨bfn, hfn, h⟩ := bind_ok h
  obtain ⟨btb, htb, h⟩ := bind_ok h
  obtain ⟨bme, hme, h⟩ := bind_ok h
  obtain ⟨bgl, hgl, h⟩ := bind_ok h
  obtain ⟨bex, hex, h⟩ := bind_ok h
  obtain ⟨bst, hst, h⟩ := bind_ok h
  obtain ⟨bel, hel, h⟩ := bind_ok h
  obtain ⟨bco, hco, h⟩ := bind_ok h
  obtain ⟨bda, hda, h⟩ := bind_ok h
  cases h
  exact encModule_of_sections ov m hty him hfn htb hme hgl hex hst hel hco hda

end Silmaril.Proofs.Wasm.Models.BinWitV1
