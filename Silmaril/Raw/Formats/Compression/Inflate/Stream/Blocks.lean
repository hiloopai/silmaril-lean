module

public import Silmaril.Formats.Compression.Inflate.Stream.Blocks
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.ParserBridge
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Fuel

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.Blocks`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

namespace Parser

/-- Every successful parsing program only consumes unread bits. -/
theorem eval_bitsLeft_le {α : Type} (parser : Parser α) {reader rest : LSBReader} {value : α}
    (h : parser.eval reader = .ok (value, rest)) : rest.bitsLeft ≤ reader.bitsLeft := by
  induction parser generalizing reader rest value with
  | pure a =>
    simp only [eval, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  | fail error => cases h
  | bits count error next ih =>
    simp only [eval] at h
    cases hr : reader.readBits count with
    | none => simp [hr] at h
    | some pair =>
      obtain ⟨n, middle⟩ := pair
      rw [hr] at h
      have hnext := ih n h
      have hread := Deflate.readBits_bitsLeft hr
      omega
  | align next ih =>
    have hnext := ih h
    simp only [LSBReader.alignToByte, LSBReader.bitsLeft] at hnext ⊢
    omega

end Parser

namespace Blocks

theorem body_versions_agree (symbolBudget kind : Nat) (output : List UInt8) :
    body131 symbolBudget kind output = bodyDevelop symbolBudget kind output := by
  cases kind with
  | zero => simp only [body131, bodyDevelop, ↓reduceIte]
  | succ n =>
    cases n with
    | zero => simp only [body131, bodyDevelop, Nat.reduceEqDiff, ↓reduceIte]
    | succ n =>
      cases n with
      | zero => simp only [body131, bodyDevelop, Nat.reduceEqDiff, ↓reduceIte]
      | succ n => simp only [body131, bodyDevelop, Nat.reduceEqDiff, ↓reduceIte]

theorem storedBody_eval (output : List UInt8) (r : LSBReader) :
    (storedBody output).eval r =
      match Deflate.decompressStored r with
      | .error err => .error err
      | .ok (bytes, next) => .ok (output ++ bytes, next) := by
  rw [storedBody, Parser.eval_bind, ParserPhases.stored_eval, Manual.decompressStored_eq]
  cases Deflate.decompressStored r <;> rfl

theorem fixedBody_eval (symbolBudget : Nat) (output : List UInt8) (r : LSBReader)
    (hbudget : r.bitsLeft + 1 ≤ symbolBudget) :
    (fixedBody symbolBudget output).eval r =
      match Deflate.fixedLitLenTable, Deflate.fixedDistTable with
      | some litLen, some dist => Deflate.decodeSymbol litLen dist r output
      | _, _ => .error .badFixedTable := by
  unfold fixedBody
  cases Deflate.fixedLitLenTable with
  | none => cases Deflate.fixedDistTable <;> rfl
  | some litLen =>
    cases Deflate.fixedDistTable with
    | none => rfl
    | some dist =>
      rw [ParserPhases.symbols_eval,
        Deflate.decodeSymbolsFuel_eq_decodeSymbol litLen dist r output symbolBudget hbudget]

theorem dynamicBody_eval (symbolBudget : Nat) (output : List UInt8) (r : LSBReader)
    (hbudget : r.bitsLeft + 1 ≤ symbolBudget) :
    (dynamicBody symbolBudget output).eval r =
      match Deflate.readDynamicTables r with
      | .error err => .error err
      | .ok (litLen, dist, next) => Deflate.decodeSymbol litLen dist next output := by
  rw [dynamicBody, Parser.eval_bind, ParserPhases.dynamicTables_eval]
  cases ht : Deflate.readDynamicTables r with
  | error err => rfl
  | ok triple =>
    obtain ⟨litLen, dist, next⟩ := triple
    dsimp only
    have hp : ParserPhases.dynamicTables.eval r = .ok ((litLen, dist), next) := by
      rw [ParserPhases.dynamicTables_eval, ht]
    have hnext := Parser.eval_bitsLeft_le ParserPhases.dynamicTables hp
    rw [ParserPhases.symbols_eval,
      Deflate.decodeSymbolsFuel_eq_decodeSymbol litLen dist next output symbolBudget (by omega)]

set_option maxRecDepth 4096 in
theorem body131_eval (symbolBudget kind : Nat) (output : List UInt8) (r : LSBReader)
    (hbudget : r.bitsLeft + 1 ≤ symbolBudget) :
    (body131 symbolBudget kind output).eval r = Deflate.decompressBlockBody kind r output := by
  by_cases h0 : kind = 0
  · simp only [body131, Deflate.decompressBlockBody, h0, ite_true]
    exact storedBody_eval output r
  · by_cases h1 : kind = 1
    · simp only [body131, Deflate.decompressBlockBody, h1, Nat.reduceEqDiff, ↓reduceIte]
      exact fixedBody_eval symbolBudget output r hbudget
    · by_cases h2 : kind = 2
      · simp only [body131, Deflate.decompressBlockBody, h2, Nat.reduceEqDiff, ↓reduceIte]
        exact dynamicBody_eval symbolBudget output r hbudget
      · simp only [body131, Deflate.decompressBlockBody, h0, h1, h2, ite_false, Parser.eval]

theorem bodyDevelop_eval (symbolBudget kind : Nat) (output : List UInt8) (r : LSBReader)
    (hbudget : r.bitsLeft + 1 ≤ symbolBudget) :
    (bodyDevelop symbolBudget kind output).eval r = Deflate.decompressBlockBody kind r output := by
  rw [← body_versions_agree]
  exact body131_eval symbolBudget kind output r hbudget

theorem header_eval (r : LSBReader) :
    header.eval r =
      match r.readBit with
      | none => .error .decodeOverrun
      | some (final, next) =>
        match next.readBits 2 with
        | none => .error .decodeOverrun
        | some (kind, rest) => .ok ((final, kind), rest) := by
  simp only [header, Parser.eval, LSBReader.readBits]
  cases r.readBit with
  | none => rfl
  | some pair =>
    obtain ⟨final, next⟩ := pair
    cases final <;> rfl

theorem blocks_eval (body : Nat → List UInt8 → Parser (List UInt8)) (symbolBudget : Nat)
    (correct : ∀ kind output r, r.bitsLeft + 1 ≤ symbolBudget →
      (body kind output).eval r = Deflate.decompressBlockBody kind r output)
    (blockFuel : Nat) (output : List UInt8) (r : LSBReader)
    (hbudget : r.bitsLeft + 1 ≤ symbolBudget) :
    (blocks body blockFuel output).eval r = Deflate.decompressBlocks blockFuel r output := by
  induction blockFuel generalizing r output with
  | zero => rfl
  | succ blockFuel ih =>
    rw [blocks, Parser.eval_bind, header_eval, Deflate.decompressBlocks]
    cases hf : r.readBit with
    | none => rfl
    | some pair =>
      obtain ⟨final, r1⟩ := pair
      dsimp only
      cases hk : r1.readBits 2 with
      | none => rfl
      | some pair =>
        obtain ⟨kind, r2⟩ := pair
        dsimp only
        have hh : header.eval r = .ok ((final, kind), r2) := by
          simp only [header_eval, hf, hk]
        have h2 := Parser.eval_bitsLeft_le header hh
        have hb := correct kind output r2 (by omega)
        rw [Parser.eval_bind, hb]
        cases hd : Deflate.decompressBlockBody kind r2 output with
        | error err => rfl
        | ok pair =>
          obtain ⟨out, r3⟩ := pair
          dsimp only
          have hp : (body kind output).eval r2 = .ok (out, r3) := hb.trans hd
          have h3 := Parser.eval_bitsLeft_le (body kind output) hp
          cases final with
          | true => rfl
          | false => exact ih out r3 (by omega)

theorem blocks131_eval (symbolBudget blockFuel : Nat) (output : List UInt8) (r : LSBReader)
    (hbudget : r.bitsLeft + 1 ≤ symbolBudget) :
    (blocks (body131 symbolBudget) blockFuel output).eval r =
      Deflate.decompressBlocks blockFuel r output :=
  blocks_eval (body131 symbolBudget) symbolBudget
    (body131_eval symbolBudget) blockFuel output r hbudget

theorem blocksDevelop_eval (symbolBudget blockFuel : Nat) (output : List UInt8) (r : LSBReader)
    (hbudget : r.bitsLeft + 1 ≤ symbolBudget) :
    (blocks (bodyDevelop symbolBudget) blockFuel output).eval r =
      Deflate.decompressBlocks blockFuel r output :=
  blocks_eval (bodyDevelop symbolBudget) symbolBudget
    (bodyDevelop_eval symbolBudget) blockFuel output r hbudget

theorem take131_eq_spec (bytes : List UInt8) : take131 bytes = Deflate.deflateTake bytes := by
  unfold take131 program131
  rw [blocks131_eval _ _ _ _ (by simp [initialReader, LSBReader.bitsLeft, inputBudget])]
  simp only [inputView, Deflate.deflateTake, initialReader, LSBReader.bitsLeft,
    Nat.zero_add, inputBudget]
  cases Deflate.decompressBlocks (8 * bytes.length + 1) ⟨0, 0, bytes, 0⟩ [] <;> rfl

theorem takeDevelop_eq_spec (bytes : List UInt8) : takeDevelop bytes = Deflate.deflateTake bytes := by
  unfold takeDevelop programDevelop
  rw [blocksDevelop_eval _ _ _ _ (by simp [initialReader, LSBReader.bitsLeft, inputBudget])]
  simp only [inputView, Deflate.deflateTake, initialReader, LSBReader.bitsLeft,
    Nat.zero_add, inputBudget]
  cases Deflate.decompressBlocks (8 * bytes.length + 1) ⟨0, 0, bytes, 0⟩ [] <;> rfl

theorem take_versions_agree (bytes : List UInt8) : take131 bytes = takeDevelop bytes :=
  (take131_eq_spec bytes).trans (takeDevelop_eq_spec bytes).symm

theorem ofBytes_normalizes (bytes : List UInt8) :
    Reservoir.Normalizes (Reservoir.ofBytes bytes) (initialReader bytes) :=
  ⟨Reservoir.ofBytes_valid bytes, rfl, ⟨by change 0 < 1; decide, rfl⟩, rfl⟩

end Blocks

theorem RunResult.resumeChunks_correct_feed {α : Type} (result : RunResult α)
    (schedulerFuel : Nat) (chunks : List (List UInt8)) {reader : LSBReader}
    (h : Reservoir.Normalizes result.state reader) :
    ∃ rest, Reservoir.Normalizes (result.resumeChunks schedulerFuel chunks).state rest ∧
      ∀ future, result.observe (Reservoir.readerFeed reader (chunks.flatten ++ future)) =
        (result.resumeChunks schedulerFuel chunks).observe (Reservoir.readerFeed rest future) := by
  induction chunks generalizing result reader with
  | nil => exact ⟨reader, h, fun _ => rfl⟩
  | cons chunk chunks ih =>
    obtain ⟨middle, hmiddle, first⟩ := result.resume_correct_feed schedulerFuel chunk h
    obtain ⟨rest, hrest, subsequent⟩ := ih (result.resume schedulerFuel chunk) hmiddle
    refine ⟨rest, hrest, ?_⟩
    intro future
    simpa only [List.flatten_cons, List.append_assoc, resumeChunks] using
      (first (chunks.flatten ++ future)).trans (subsequent future)

namespace Blocks

/-- A generic bridge from a complete-input correctness theorem to streaming
observations. The semantic budget is fixed using the known full byte length;
all scheduler fuel and all chunk boundaries remain arbitrary. The observation
includes the retained continuation if the scheduler has not completed it. -/
theorem program_chunks_future
    (program : Nat → Parser (List UInt8))
    (complete : ∀ bytes, inputView ((program (inputBudget bytes)).eval (initialReader bytes)) =
      Deflate.deflateTake bytes)
    (totalLength schedulerFuel : Nat) (initialInput : List UInt8) (chunks : List (List UInt8)) :
    ∃ rest, Reservoir.Normalizes
        ((Parser.run schedulerFuel (program (8 * totalLength + 1))
          (Reservoir.ofBytes initialInput)).resumeChunks schedulerFuel chunks).state rest ∧
      ∀ future, (initialInput ++ (chunks.flatten ++ future)).length = totalLength →
        Deflate.deflateTake (initialInput ++ (chunks.flatten ++ future)) =
          inputView (((Parser.run schedulerFuel (program (8 * totalLength + 1))
            (Reservoir.ofBytes initialInput)).resumeChunks schedulerFuel chunks).observe
              (Reservoir.readerFeed rest future)) := by
  obtain ⟨middle, hmiddle, first⟩ :=
    Parser.run_correct_feed schedulerFuel (program (8 * totalLength + 1))
      (ofBytes_normalizes initialInput)
  obtain ⟨rest, hrest, subsequent⟩ :=
    RunResult.resumeChunks_correct_feed
      (Parser.run schedulerFuel (program (8 * totalLength + 1)) (Reservoir.ofBytes initialInput))
      schedulerFuel chunks hmiddle
  refine ⟨rest, hrest, ?_⟩
  intro future hlength
  have observed := congrArg inputView
    ((first (chunks.flatten ++ future)).trans (subsequent future))
  change inputView ((program (8 * totalLength + 1)).eval
    (initialReader (initialInput ++ (chunks.flatten ++ future)))) = _ at observed
  have hbudget : 8 * totalLength + 1 = inputBudget (initialInput ++ (chunks.flatten ++ future)) :=
    congrArg (fun length => 8 * length + 1) hlength.symm
  rw [hbudget] at observed
  rw [hbudget]
  exact (complete (initialInput ++ (chunks.flatten ++ future))).symm.trans observed

theorem program131_chunks_future (totalLength schedulerFuel : Nat)
    (initialInput : List UInt8) (chunks : List (List UInt8)) :
    ∃ rest, Reservoir.Normalizes
        ((Parser.run schedulerFuel (program131 (8 * totalLength + 1) [])
          (Reservoir.ofBytes initialInput)).resumeChunks schedulerFuel chunks).state rest ∧
      ∀ future, (initialInput ++ (chunks.flatten ++ future)).length = totalLength →
        Deflate.deflateTake (initialInput ++ (chunks.flatten ++ future)) =
          inputView (((Parser.run schedulerFuel (program131 (8 * totalLength + 1) [])
            (Reservoir.ofBytes initialInput)).resumeChunks schedulerFuel chunks).observe
              (Reservoir.readerFeed rest future)) :=
  program_chunks_future (fun budget => program131 budget []) take131_eq_spec
    totalLength schedulerFuel initialInput chunks

theorem programDevelop_chunks_future (totalLength schedulerFuel : Nat)
    (initialInput : List UInt8) (chunks : List (List UInt8)) :
    ∃ rest, Reservoir.Normalizes
        ((Parser.run schedulerFuel (programDevelop (8 * totalLength + 1) [])
          (Reservoir.ofBytes initialInput)).resumeChunks schedulerFuel chunks).state rest ∧
      ∀ future, (initialInput ++ (chunks.flatten ++ future)).length = totalLength →
        Deflate.deflateTake (initialInput ++ (chunks.flatten ++ future)) =
          inputView (((Parser.run schedulerFuel (programDevelop (8 * totalLength + 1) [])
            (Reservoir.ofBytes initialInput)).resumeChunks schedulerFuel chunks).observe
              (Reservoir.readerFeed rest future)) :=
  program_chunks_future (fun budget => programDevelop budget []) takeDevelop_eq_spec
    totalLength schedulerFuel initialInput chunks

/-! Kernel-reduced witnesses: LEN and NLEN are split across input deliveries,
and a non-final empty block exercises the recursive block-header loop. -/

theorem stored_split_len :
    match storedPrefix with
    | .needInput _ state => state = ⟨3, 8, [], 8⟩
    | _ => False := rfl

theorem stored_three_chunks :
    storedPrefix.resumeChunks 128 [[0, 0xfc], [0xff, 65, 66, 67]] =
      .done [65, 66, 67] ⟨0, 0, [], 64⟩ := rfl

theorem two_stored_blocks :
    Parser.run 128 (programDevelop 89 [])
      (Reservoir.ofBytes [0, 0, 0, 0xff, 0xff, 1, 1, 0, 0xfe, 0xff, 65]) =
      .done [65] ⟨0, 0, [], 88⟩ := rfl

end Blocks
end Silmaril.Formats.Compression.Inflate.Stream
