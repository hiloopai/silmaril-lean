module

public import Silmaril.Machine.DecodeGraph.Decoder.Thms
public import Silmaril.Parse.DecodeGraph.Institution.Thms
public import Silmaril.Parse.DecodeGraph.Thms
public import Silmaril.Semantics.Accept.Rel.Defs
public import Silmaril.X86.Stack

/-! A stack-subset decoder, with a toy observable block machine, not x86 execution. -/

namespace Silmaril.Machine.DecodeGraph.X86Example

open scoped SetRel
open Silmaril.Parse.DecodeGraph
open Silmaril.X86 (Insn)

private inductive Exit where
  | call (displacement : BitVec 32)
  | ret

private def transfer : Insn → Option Exit
  | .call displacement => some (.call displacement)
  | .ret => some .ret
  | _ => none

/-- A syntactic boundary policy for this subset, distinct from branch execution. -/
private def ends (_ : Unit) (_ : Nat) (instr : Insn) : Prop := (transfer instr).isSome = true

private def decoder : Reference Unit Insn := ofDecoder Insn.byteDecoder
private def blockDecoder : Reference Unit (List Insn) := blocks decoder ends 2
private def sequential : Reference Unit (List Insn) := sequentialPrefixes Insn.byteDecoder 2

private def input : Input Unit (List UInt8) := ⟨(), List.replicate 16 0x90 ++ [0x41, 0x50, 0xC3, 0xCC], 20, 16⟩
private def code : List Insn := [.push .r8, .ret]

/-- `41 50` decodes as `push r8`, then `c3` terminates at exit boundary 19.
`cc` is outside the block, and the return target is not computed by decoding. -/
theorem pushRet_decodes : (input, (code, 19)) ∈ blockDecoder := by
  change Path decoder ends 2 input [.push .r8, .ret] 19
  exact .next (nextPos := 18) ⟨by decide, 2, rfl, rfl⟩ (by decide) (by decide) (by change ¬ (false = true); decide)
    (.last ⟨by decide, 1, rfl, rfl⟩ (by decide) (by decide) rfl)

theorem pushRet_outcome {result : List Insn × Nat} :
    (input, result) ∈ blockDecoder ↔ result = (code, 19) :=
  ⟨fun h => blocks_deterministic (ofDecoder_deterministic Insn.byteDecoder) ends 2 h pushRet_decodes,
    fun h => h.symm ▸ pushRet_decodes⟩

private def retQuery : Input Unit (List UInt8) := ⟨(), [0xCC, 0xC3], 2, 1⟩
private def asRet (_ : Bool) : Insn := .ret

/-- Two proposed source instructions with the same image both become exact
successes of the reduct of the deterministic x86 decoder. -/
theorem stack_reduct_not_deterministic : ¬ Deterministic (Institution.reduct asRet decoder) :=
  Institution.reduct_not_deterministic_of_collision (input := retQuery) (endPos := 2)
    (by decide : false ≠ true) rfl ⟨by decide, 1, rfl, rfl⟩

/-- All factored successes refine the executable sequential decoder after
restricting it to the claimed prefix and erasing its listing offsets. -/
theorem stack_blocks_refine_sequential : blockDecoder ⊆ sequential :=
  blocks_subset_sequentialPrefixes Insn.byteDecoder ends 2

/-- The existing executable lists both instructions and their exact offsets. -/
theorem legacy_pushRet : Insn.byteDecoder.decodeBlock 2 16 (decoderWindow input.bytes input.pos 19) =
    some [(16, .push .r8), (18, .ret)] := rfl

theorem legacy_with_suffix : Insn.byteDecoder.decodeBlock 3 16 (decoderWindow input.bytes input.pos input.stop) =
    none := rfl

theorem sequential_accepts_unterminated_prefix : (input, ([.push .r8], 18)) ∈ sequential :=
  ⟨by decide, by decide, by decide, rfl⟩

theorem sequential_not_refine_stack_blocks : ¬ sequential ⊆ blockDecoder := by
  intro converse
  have conflict := pushRet_outcome.mp (converse sequential_accepts_unterminated_prefix)
  cases conflict

/-- A truncated REX prefix is not a fault outcome or an empty decoded block. -/
theorem truncated_no_block : (⟨(), [0x41], 1, 0⟩ : Input Unit (List UInt8)) ∉ blockDecoder.dom := by
  rintro ⟨⟨code, span⟩, path⟩
  change Path decoder ends 2 ⟨(), [0x41], 1, 0⟩ code span at path
  cases path with
  | last decoded => obtain ⟨_, _, read, _⟩ := decoded; cases (show none = some _ from read)
  | next decoded => obtain ⟨_, _, read, _⟩ := decoded; cases (show none = some _ from read)

private def classify (instr : Insn) : Insn ⊕ Exit :=
  match transfer instr with
  | none => .inl instr
  | some exit => .inr exit

private def typedDecoder : Reference Unit (TerminatedBlock Insn Exit) :=
  assembleBlocks (map (List.map classify) blockDecoder) TerminatedBlock.Assembles

/-- The same listing can build a record with a separate exit field. The
token check excludes any earlier exit, independently of cursor arithmetic. -/
theorem pushRet_assembles :
    (input, (⟨[Insn.push .r8], Exit.ret⟩, 19)) ∈ typedDecoder :=
  ⟨[.inl (.push .r8), .inr .ret], ⟨(code, 19), pushRet_decodes, rfl, rfl⟩, rfl⟩

private abbrev Summary := Nat × Exit

private def typedMachine : Observed (TerminatedBlock Insn Exit) Summary :=
  Function.graph fun block => (block.body.length, block.exit)

theorem pushRet_typed_byte_observation :
    (input, (1, .ret)) ∈ rebase (typedDecoder ○ Function.graph Prod.fst) typedMachine :=
  ⟨_, ⟨_, pushRet_assembles, rfl⟩, rfl⟩

/-- Ordinary instructions increment a toy observation counter. A transfer emits
an exit tag only at the end of the listing. There is no stack or PC state here. -/
private def summarize : List Insn → Option Summary
  | [] => none
  | instr :: rest =>
    match transfer instr with
    | some exit => if rest.isEmpty then some (0, exit) else none
    | none => (summarize rest).map fun (count, exit) => (count + 1, exit)

private def listing : SetRel (List Insn) (List Summary) :=
  Accept.ofPartial fun instructions => (summarize instructions).map fun summary => [summary]

private def machine : Observed (List Summary) Summary :=
  Accept.ofPartial fun
    | [summary] => some summary
    | _ => none

private def listMachine : Observed (List Insn) Summary := rebase listing machine

private def byteToList : SetRel (Input Unit (List UInt8)) (List Insn) :=
  blockDecoder ○ Function.graph Prod.fst

/-- An entire two-instruction listing maps to one abstract block, not pointwise. -/
theorem pushRet_abstracts : (code, [(1, .ret)]) ∈ listing := rfl

theorem pushRet_transports : (input, ([(1, .ret)], 19)) ∈ transport listing blockDecoder :=
  ⟨(code, 19), pushRet_decodes, pushRet_abstracts, rfl⟩

theorem pushRet_list_observation : (code, (1, .ret)) ∈ listMachine :=
  ⟨[(1, .ret)], pushRet_abstracts, rfl⟩

theorem pushRet_byte_observation : (input, (1, .ret)) ∈ rebase byteToList listMachine :=
  ⟨code, ⟨(code, 19), pushRet_decodes, rfl⟩, pushRet_list_observation⟩

theorem pushRet_staged_rebase :
    rebase (byteToList ○ listing) machine = rebase byteToList listMachine := rebase_comp ..

theorem stack_byte_observations_refine : rebase byteToList listMachine ⊆
    rebase (sequential ○ Function.graph Prod.fst) listMachine :=
  rebase_mono (SetRel.comp_subset_comp_left stack_blocks_refine_sequential) (fun _ observed => observed)

end Silmaril.Machine.DecodeGraph.X86Example
