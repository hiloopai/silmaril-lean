module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.Defs

/-!
# Round 7, memory SIMD: `$hostcall` at `BM` is undefined on stores with memory SIMD code

`OpenRMRest` fixes the builtins `BM = withVBytes (Prims.builtins P hn host)`. Their `$hostcall`
(`Prims.hostcallCall`) answers only at arguments `hostArgs hn h s vs`, whose store argument is
round 3's `storeV hn s`. A configuration with memory SIMD code in a function body of its store is
encoded by `configVD`, whose store is `storeVD hn s`. These never meet:

* `schemaV_ne_tuple`, `schemaV_ne_struct`: the provisional schema images are never tuples or
  records, while `instrToVM` carries the record `memargV` in a tuple
  (`schemaInstrV_ne_instrToVM`);
* `instrToVD_ne`, `instrsToVD_ne`: an instruction (sequence) with memory SIMD code at some depth
  has a `instrToVD` image that is no `instrToV` image;
* `storeVD_ne_storeV`: a store with memory SIMD code in a Wasm function body has a `storeVD`
  image that is no `storeV` image;
* `bm_hostcall_none`: so `$hostcall` at `BM` is undefined at every argument list whose store is
  such a `storeVD` image.

So on configurations whose store holds memory SIMD code, `BM` cannot answer the host call that a
Core `call_ref-hostfunc-res` step makes.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim
open Round6.MemSimd (instrMS instrsMS StoreMS memSimd instrToVM)
open Round7.MemSimd (instrToVD instrsToVD storeVD funcInstVD)

variable {H : Type}

/-! ## Schema images -/

theorem schemaV_ne (t : Silmaril.Formats.TExpr String Int) :
    (∀ L, schemaV t ≠ .tuple L) ∧ (∀ gs, schemaV t ≠ .struct gs) := by
  unfold schemaV
  split <;> (try split) <;> simp

theorem schemaV_ne_struct (t : Silmaril.Formats.TExpr String Int)
    (gs : List (Silmaril.SpecTec.IL.AtomS × Value)) : schemaV t ≠ .struct gs := (schemaV_ne t).2 gs

theorem schemaV_ne_tuple (t : Silmaril.Formats.TExpr String Int) (L : List Value) :
    schemaV t ≠ .tuple L := (schemaV_ne t).1 L

/-- The image of a memory SIMD instruction at `instrToVM`: a case whose payload is a tuple holding
the record `memargV a`. -/
theorem instrToVM_shape {i : Instr} (hi : memSimd i = true) :
    ∃ op L a, instrToVM i = .case op (.tuple L) ∧ memargV a ∈ L := by
  cases i with
  | vecLoad op m a => exact ⟨_, _, a, rfl, by simp⟩
  | vecLoadLane p m a l => exact ⟨_, _, a, rfl, by simp⟩
  | vecStore m a => exact ⟨_, _, a, rfl, by simp⟩
  | vecStoreLane p m a l => exact ⟨_, _, a, rfl, by simp⟩
  | _ => simp [memSimd] at hi

/-- **A schema image is no `instrToVM` image of a memory SIMD instruction.** -/
theorem schemaInstrV_ne_instrToVM (c : Silmaril.Wasm.SpecTec.Constructor) {i : Instr}
    (hi : memSimd i = true) : schemaInstrV c ≠ instrToVM i := by
  obtain ⟨op, L, a, hv, ha⟩ := instrToVM_shape hi
  rw [hv]
  unfold schemaInstrV
  split
  · intro h
    simp only [Value.case.injEq] at h
    exact schemaV_ne_tuple _ _ h.2
  · intro h
    simp only [Value.case.injEq, Value.tuple.injEq] at h
    rw [← h.2] at ha
    obtain ⟨x, -, hx⟩ := List.mem_map.1 ha
    exact schemaV_ne_struct _ _ hx

/-! ## Heads -/

theorem memSimd_of_head {i : Instr}
    (h : Typing.instrHead i = "VLOAD" ∨ Typing.instrHead i = "VLOAD_LANE" ∨
      Typing.instrHead i = "VSTORE" ∨ Typing.instrHead i = "VSTORE_LANE") :
    memSimd i = true := by
  cases i <;> simp only [Typing.instrHead] at h <;> first | rfl | simp at h

theorem head_memSimd {i : Instr} (h : memSimd i = true) :
    Typing.instrHead i = "VLOAD" ∨ Typing.instrHead i = "VLOAD_LANE" ∨
      Typing.instrHead i = "VSTORE" ∨ Typing.instrHead i = "VSTORE_LANE" := by
  cases i <;> simp only [memSimd, Bool.false_eq_true] at h <;> simp [Typing.instrHead]

theorem instrToV_memSimd {i : Instr} (h : memSimd i = true) :
    instrToV i = schemaInstrV (Silmaril.Wasm.SpecTec.encodeInstruction i) := by
  cases i <;> simp only [memSimd, Bool.false_eq_true] at h <;> rfl

theorem block_of_head {i : Instr} (h : Typing.instrHead i = "BLOCK") :
    ∃ bt b, i = .block bt b := by
  cases i <;> simp only [Typing.instrHead] at h <;> first | exact ⟨_, _, rfl⟩ | simp at h

theorem loop_of_head {i : Instr} (h : Typing.instrHead i = "LOOP") :
    ∃ bt b, i = .loop bt b := by
  cases i <;> simp only [Typing.instrHead] at h <;> first | exact ⟨_, _, rfl⟩ | simp at h

theorem if_of_head {i : Instr} (h : Typing.instrHead i = "IF%%ELSE%") :
    ∃ bt b₁ b₂, i = .if_ bt b₁ b₂ := by
  cases i <;> simp only [Typing.instrHead] at h <;> first | exact ⟨_, _, _, rfl⟩ | simp at h

theorem tryTable_of_head {i : Instr} (h : Typing.instrHead i = "TRY_TABLE") :
    ∃ bt cs b, i = .tryTable bt cs b := by
  cases i <;> simp only [Typing.instrHead] at h <;> first | exact ⟨_, _, _, rfl⟩ | simp at h

/-! ## Code with memory SIMD has no `instrToV` image -/

/-- At a memory SIMD instruction `instrToVD` is `instrToVM`. -/
theorem instrToVD_of_memSimd {i : Instr} (h : memSimd i = true) : instrToVD i = instrToVM i := by
  cases i <;> simp only [memSimd, Bool.false_eq_true] at h <;> rfl

/-- The four ways an instruction can contain memory SIMD code. -/
theorem instrMS_false_cases {i : Instr} (hi : instrMS i = false) :
    memSimd i = true ∨ (∃ bt b, i = .block bt b ∧ instrsMS b = false) ∨
      (∃ bt b, i = .loop bt b ∧ instrsMS b = false) ∨
      (∃ bt b₁ b₂, i = .if_ bt b₁ b₂ ∧ (instrsMS b₁ = false ∨ instrsMS b₂ = false)) ∨
      (∃ bt cs b, i = .tryTable bt cs b ∧ instrsMS b = false) := by
  cases i with
  | if_ bt b₁ b₂ =>
    have h : instrsMS b₁ = false ∨ instrsMS b₂ = false := by
      cases h₁ : instrsMS b₁ <;> simp_all [instrMS]
    exact .inr (.inr (.inr (.inl ⟨bt, b₁, b₂, rfl, h⟩)))
  | _ => simp_all [instrMS, memSimd]

/-- The memory SIMD case of `instrToVD_ne`. -/
theorem instrToVM_ne {i : Instr} (hm : memSimd i = true) (i' : Instr) :
    instrToVM i ≠ instrToV i' := by
  intro he
  obtain ⟨op, L, a, hc, -⟩ := instrToVM_shape hm
  have hop : op = Typing.instrHead i := Round7.MemSimd.instrToVM_case_memSimd hm hc
  have hop' : op = Typing.instrHead i' := Typing.instrToV_case (he ▸ hc)
  have hm' : memSimd i' = true := memSimd_of_head (hop' ▸ hop ▸ head_memSimd hm)
  rw [instrToV_memSimd hm'] at he
  exact schemaInstrV_ne_instrToVM _ hm he.symm

/-- The `block` case of `instrToVD_ne`. -/
theorem block_ne {bt : BlockType} {b : List Instr} (ih : ∀ is', instrsToVD b ≠ instrsToV is')
    (i' : Instr) : instrToVD (.block bt b) ≠ instrToV i' := by
  intro he
  obtain ⟨bt', b', rfl⟩ := block_of_head (Typing.instrToV_case he.symm).symm
  have he' : Value.case "BLOCK" (.tuple [Encode.toValue bt, .list (instrsToVD b)]) =
      .case "BLOCK" (.tuple [Encode.toValue bt', .list (instrsToV b')]) := he
  have hl : Encode.toValue bt = Encode.toValue bt' ∧ instrsToVD b = instrsToV b' := by
    simpa only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
      and_true, true_and] using he'
  exact ih b' hl.2

/-- The `loop` case of `instrToVD_ne`. -/
theorem loop_ne {bt : BlockType} {b : List Instr} (ih : ∀ is', instrsToVD b ≠ instrsToV is')
    (i' : Instr) : instrToVD (.loop bt b) ≠ instrToV i' := by
  intro he
  obtain ⟨bt', b', rfl⟩ := loop_of_head (Typing.instrToV_case he.symm).symm
  have he' : Value.case "LOOP" (.tuple [Encode.toValue bt, .list (instrsToVD b)]) =
      .case "LOOP" (.tuple [Encode.toValue bt', .list (instrsToV b')]) := he
  have hl : Encode.toValue bt = Encode.toValue bt' ∧ instrsToVD b = instrsToV b' := by
    simpa only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
      and_true, true_and] using he'
  exact ih b' hl.2

/-- The `if` case of `instrToVD_ne`. -/
theorem if_ne {bt : BlockType} {b₁ b₂ : List Instr}
    (ih : (∀ is', instrsToVD b₁ ≠ instrsToV is') ∨ (∀ is', instrsToVD b₂ ≠ instrsToV is'))
    (i' : Instr) : instrToVD (.if_ bt b₁ b₂) ≠ instrToV i' := by
  intro he
  obtain ⟨bt', c₁, c₂, rfl⟩ := if_of_head (Typing.instrToV_case he.symm).symm
  have he' : Value.case "IF%%ELSE%" (.tuple [Encode.toValue bt, .list (instrsToVD b₁),
      .list (instrsToVD b₂)]) = .case "IF%%ELSE%" (.tuple [Encode.toValue bt',
      .list (instrsToV c₁), .list (instrsToV c₂)]) := he
  have hl : Encode.toValue bt = Encode.toValue bt' ∧ instrsToVD b₁ = instrsToV c₁ ∧
      instrsToVD b₂ = instrsToV c₂ := by
    simpa only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
      and_true, true_and] using he'
  rcases ih with ih | ih
  · exact ih c₁ hl.2.1
  · exact ih c₂ hl.2.2

/-- The `try_table` case of `instrToVD_ne`. -/
theorem tryTable_ne {bt : BlockType} {cs : List Catch} {b : List Instr}
    (ih : ∀ is', instrsToVD b ≠ instrsToV is') (i' : Instr) :
    instrToVD (.tryTable bt cs b) ≠ instrToV i' := by
  intro he
  obtain ⟨bt', cs', b', rfl⟩ := tryTable_of_head (Typing.instrToV_case he.symm).symm
  have he' : Value.case "TRY_TABLE" (.tuple [Encode.toValue bt,
      .case "%" (.tuple [.list (cs.map Encode.toValue)]), .list (instrsToVD b)]) =
      .case "TRY_TABLE" (.tuple [Encode.toValue bt',
      .case "%" (.tuple [.list (cs'.map Encode.toValue)]), .list (instrsToV b')]) := he
  have hl : Encode.toValue bt = Encode.toValue bt' ∧
      cs.map Encode.toValue = cs'.map Encode.toValue ∧ instrsToVD b = instrsToV b' := by
    simpa only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
      and_true, true_and] using he'
  exact ih b' hl.2.2

mutual
/-- **An instruction with memory SIMD code at some depth has no `instrToV` image at
`instrToVD`.** -/
theorem instrToVD_ne {i : Instr} (hi : instrMS i = false) (i' : Instr) :
    instrToVD i ≠ instrToV i' := by
  rcases instrMS_false_cases hi with hm | ⟨bt, b, rfl, hb⟩ | ⟨bt, b, rfl, hb⟩ |
      ⟨bt, b₁, b₂, rfl, hb⟩ | ⟨bt, cs, b, rfl, hb⟩
  · exact instrToVD_of_memSimd hm ▸ instrToVM_ne hm i'
  · exact block_ne (instrsToVD_ne hb) i'
  · exact loop_ne (instrsToVD_ne hb) i'
  · exact if_ne (hb.imp (fun h => instrsToVD_ne h) (fun h => instrsToVD_ne h)) i'
  · exact tryTable_ne (instrsToVD_ne hb) i'
termination_by sizeOf i

/-- A sequence with memory SIMD code at some depth has no `instrsToV` image at `instrsToVD`. -/
theorem instrsToVD_ne {is : List Instr} (hi : instrsMS is = false) (is' : List Instr) :
    instrsToVD is ≠ instrsToV is' := by
  intro he
  match is, is', hi, he with
  | [], _, hi, _ => simp [instrsMS] at hi
  | i :: is, [], _, he => simp [instrsToVD, instrsToV] at he
  | i :: is, i' :: is', hi, he =>
    have hl : instrToVD i = instrToV i' ∧ instrsToVD is = instrsToV is' := by
      simpa [instrsToVD, instrsToV] using he
    have hb : instrMS i = false ∨ instrsMS is = false := by
      cases h₁ : instrMS i <;> simp_all [instrsMS]
    rcases hb with hb | hb
    · exact instrToVD_ne hb i' hl.1
    · exact instrsToVD_ne hb is' hl.2
termination_by sizeOf is
end

/-! ## Stores -/

/-- **A store with memory SIMD code in a Wasm function body has no `storeV` image at
`storeVD`.** -/
theorem storeVD_ne_storeV (hn : H → String) {s : Store H} (hs : ¬ StoreMS s) (s' : Store H) :
    storeVD hn s ≠ storeV hn s' := by
  intro he
  have hall := he
  simp only [storeVD, storeV, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    Value.list.injEq, true_and] at hall
  have hf : s.funcs.map (funcInstVD hn) = s'.funcs.map (funcInstV hn) := hall.2.2.2.2.1
  simp only [StoreMS, not_forall, Bool.not_eq_true] at hs
  obtain ⟨fi, hfi, fn, hcode, hb⟩ := hs
  have hmem : funcInstVD hn fi ∈ s'.funcs.map (funcInstV hn) := hf ▸ List.mem_map_of_mem hfi
  obtain ⟨fi', -, hfi'⟩ := List.mem_map.1 hmem
  cases hc' : fi'.code with
  | wasm fn' =>
    have hl := hfi'
    simp only [funcInstVD, funcInstV, hcode, hc', Value.struct.injEq, List.cons.injEq,
      Prod.mk.injEq, Value.case.injEq, Value.tuple.injEq, Value.list.injEq, true_and] at hl
    exact instrsToVD_ne hb fn'.body hl.2.2.1.2.2.1.symm
  | host h =>
    simp [funcInstVD, funcInstV, hcode, hc'] at hfi'

/-! ## `$hostcall` -/

/-- **`Prims.hostcallCall` is undefined at a store image with memory SIMD code.** -/
theorem hostcallCall_storeVD (hn : H → String) (host : HostSemantics H) {s : Store H}
    (hs : ¬ StoreMS s) (x : Value) (vs : Value) :
    Prims.hostcallCall hn host [.val x, .val (storeVD hn s), .val vs] = none := by
  unfold Prims.hostcallCall
  split
  · rename_i hp
    obtain ⟨p, hp, -⟩ := hp
    simp only [Prims.hostArgs, List.cons.injEq, ArgV.val.injEq] at hp
    exact absurd hp.2.1 (storeVD_ne_storeV hn hs p.2.1)
  · rfl

/-- **`$hostcall` at `BM` is undefined at a store image with memory SIMD code**, whatever the host
function and the arguments. -/
theorem bm_hostcall_none (P : Profile) (hn : H → String) (host : HostSemantics H) {s : Store H}
    (hs : ¬ StoreMS s) (x : Value) (vs : Value) :
    (Round7.MemSimd.BM P hn host).call "hostcall" [.val x, .val (storeVD hn s), .val vs] = none := by
  have h : (Prims.builtins P hn host).call "hostcall" [.val x, .val (storeVD hn s), .val vs] =
      Prims.hostcallCall hn host [.val x, .val (storeVD hn s), .val vs] := by
    have h₁ : Floats.floatCall P "hostcall" [.val x, .val (storeVD hn s), .val vs] = none :=
      ite_eq_right_iff.2 (fun h => absurd h (by decide))
    have h₂ : IntNumeric.intCall "hostcall" [.val x, .val (storeVD hn s), .val vs] = none := rfl
    show Prims.call P hn host "hostcall" _ = _
    unfold Prims.call
    rw [h₁, h₂]
    rfl
  simp only [Round7.MemSimd.BM, Round7.MemSimd.withVBytes]
  rw [ite_eq_right_of_eq_false _ _ (by decide), h, hostcallCall_storeVD hn host hs x vs]

end Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres
