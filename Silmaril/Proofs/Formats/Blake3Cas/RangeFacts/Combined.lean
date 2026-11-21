module

public import Silmaril.Formats.Blake3Cas.RangeFacts.Combined.Defs
import Init.Data.Vector.OfFn
import Silmaril.Formats.Blake3Cas.RangeFacts.Projection.Thms

public section

namespace Silmaril.Proofs.Formats.Blake3Cas.RangeFacts.Combined

open Silmaril.Crypto.Blake3
open Silmaril.Formats
open Silmaril.Formats.Blake3Cas
open Silmaril.Formats.Blake3Cas.RangeFacts
open Silmaril.Formats.Blake3Cas.RangeFacts.Combined
open Silmaril.Formats.Blake3Cas.RangeFacts.Projection (Contiguous)

private theorem split_bounds {width : Nat} (large : 1024 < width) :
    0 < splitBytes width ∧ splitBytes width < width ∧ splitBytes width % 1024 = 0 := by
  have below := (Nat.le_log2 (n := (width - 1) / 1024) (by omega)).mp (Nat.le_refl _)
  have positive := Nat.two_pow_pos ((width - 1) / 1024).log2
  unfold splitBytes
  omega

private theorem split_span (first width : Nat) (large : 1024 < width) :
    (Bao.Span.mk first (Bao.chunks width)).split =
      (⟨first, Bao.chunks (splitBytes width)⟩,
        ⟨first + splitBytes width / 1024, Bao.chunks (width - splitBytes width)⟩) := by
  have ⟨pos, less, modulo⟩ := split_bounds large
  have index : Bao.chunks width - 1 = (width - 1) / 1024 := by
    unfold Bao.chunks Bao.chunkBytes
    omega
  simp only [Bao.Span.split, index]
  unfold splitBytes Bao.chunks Bao.chunkBytes at *
  generalize 2 ^ ((width - 1) / 1024).log2 = half at *
  simp only [Prod.mk.injEq, Bao.Span.mk.injEq, true_and]
  omega

private theorem childBounds {total first width : Nat} (large : 1024 < width)
    (fits : first * 1024 + width ≤ total)
    (boundary : (0 < width ∧ width % 1024 = 0) ∨ first * 1024 + width = total) :
    first * 1024 + splitBytes width ≤ total ∧
    ((0 < splitBytes width ∧ splitBytes width % 1024 = 0) ∨ first * 1024 + splitBytes width = total) ∧
    (first + splitBytes width / 1024) * 1024 + (width - splitBytes width) ≤ total ∧
    ((0 < width - splitBytes width ∧ (width - splitBytes width) % 1024 = 0) ∨
      (first + splitBytes width / 1024) * 1024 + (width - splitBytes width) = total) := by
  have := split_bounds large
  omega

private theorem planAt_geometry (total first width : Nat)
    (fits : first * 1024 + width ≤ total)
    (boundary : (0 < width ∧ width % 1024 = 0) ∨ first * 1024 + width = total)
    (inside : first + Bao.chunks width ≤ Bao.chunks total) :
    Bao.planAt total 1 [⟨0, Bao.chunks total⟩] ⟨first, Bao.chunks width⟩ =
      chunkPlan (geometry first width) := by
  have overlaps : Bao.overlaps [⟨0, Bao.chunks total⟩] ⟨first, Bao.chunks width⟩ = true := by
    have pos : 0 < Bao.chunks width := by simp [Bao.chunks]
    simp [Bao.overlaps, Bao.Span.endChunk]
    omega
  rw [Bao.planAt, geometry]
  simp only [overlaps, Bool.not_true, Bool.false_eq_true, ite_false]
  by_cases small : width ≤ 1024
  · have single : Bao.chunks width = 1 := by unfold Bao.chunks Bao.chunkBytes; omega
    have widthEq : (Bao.Span.mk first 1).byteSize total = width := by
      change min total ((first + 1) * 1024) - first * 1024 = width
      omega
    simp [small, single, chunkPlan, widthEq]
  · have many : ¬Bao.chunks width ≤ 1 := by unfold Bao.chunks Bao.chunkBytes; omega
    have large : 1024 < width := Nat.lt_of_not_ge small
    have split := split_span first width large
    have ⟨leftFits, leftBoundary, rightFits, rightBoundary⟩ := childBounds large fits boundary
    have ⟨positive, smaller, _⟩ := split_bounds large
    have leftInside : first + Bao.chunks (splitBytes width) ≤ Bao.chunks total := by
      unfold Bao.chunks Bao.chunkBytes at *
      omega
    have rightInside : first + splitBytes width / 1024 + Bao.chunks (width - splitBytes width) ≤ Bao.chunks total := by
      have := (split_bounds large).2.2
      unfold Bao.chunks Bao.chunkBytes at *
      omega
    have spanEq : shapeSpan (.fork (geometry first (splitBytes width))
        (geometry (first + splitBytes width / 1024) (width - splitBytes width))) =
          ⟨first, Bao.chunks width⟩ := by
      have eq := canonicalSpan first width
      rw [geometry.eq_def, dite_eq_right small] at eq
      exact eq
    simp [many, small, split, chunkPlan, spanEq,
      planAt_geometry total first (splitBytes width) leftFits leftBoundary leftInside,
      planAt_geometry total (first + splitBytes width / 1024) (width - splitBytes width) rightFits rightBoundary rightInside]
termination_by width
decreasing_by all_goals omega

theorem fullPlan_geometry (size : Nat) : Bao.fullPlan size 1 = chunkPlan (geometry 0 size) :=
  planAt_geometry size 0 size (by omega) (Or.inr (by omega)) (by omega)

private theorem shapePlan_width (shape : Shape) :
    ((chunkPlan shape).preorder.map Bao.Slot.width).sum = 64 * ((shapeSpan shape).count - 1) + shape.size := by
  have positive : ∀ shape : Shape, 0 < (shapeSpan shape).count := by
    intro node
    induction node with
    | leaf => simp [shapeSpan]
    | fork left right lhs rhs => exact Nat.add_pos_left lhs _
  induction shape with
  | leaf => simp [chunkPlan, Bao.Plan.preorder, Bao.Slot.width, shapeSpan, Shape.size]
  | fork left right lhs rhs =>
    simp only [chunkPlan, Bao.Plan.preorder, List.map_cons, List.map_append, List.sum_cons, List.sum_append,
      Bao.Slot.width, lhs, rhs, shapeSpan, Shape.size]
    have := positive left
    have := positive right
    omega

private theorem mapFields_tape {source : Bao.Slot → Option Bytes} {layout : List Bao.Slot} {fields : List Bytes}
    (found : (layout.mapM fun slot => do
      let field ← source slot
      if field.length = slot.width then some field else none) = some fields) : Bao.Tape layout fields := by
  induction layout generalizing fields with
  | nil =>
    cases Option.some.inj found
    trivial
  | cons slot slots ih =>
    rw [List.mapM_cons] at found
    cases get : source slot with
    | none => simp [get] at found
    | some field =>
      by_cases width : field.length = slot.width
      · simp only [get, Option.bind_eq_bind, Option.bind_some, ite_eq_left width] at found
        cases success : (slots.mapM fun entry => (source entry).bind fun raw =>
          if raw.length = entry.width then some raw else none) with
        | none => simp [success] at found
        | some rest =>
          rw [success] at found
          cases Option.some.inj found
          exact ⟨width, ih success⟩
      · simp [get, width] at found

private theorem tape_length {layout : List Bao.Slot} {fields : List Bytes} (tape : Bao.Tape layout fields) :
    fields.flatten.length = (layout.map Bao.Slot.width).sum := by
  induction layout generalizing fields with
  | nil => cases fields <;> simp_all [Bao.Tape]
  | cons slot slots ih =>
    cases fields with
    | nil => simp [Bao.Tape] at tape
    | cons field rest =>
      obtain ⟨width, tail⟩ := tape
      simp [width, ih tail]

private def sizedSource (original : Bytes) (slot : Bao.Slot) : Option Bytes := do
  let field ← source original slot
  if field.length = slot.width then some field else none

private inductive Renders (size : Nat) : Shape → Nat → Bool → CV → Bytes → List Bytes → Prop where
  | leaf {first width base : Nat} {root : Bool} {cv : CV} {bytes : Bytes}
      (aligned : Aligned ⟨first, 1⟩ (.leaf first width) base)
      (slotWidth : bytes.length = (Bao.Span.mk first 1).byteSize size)
      (length : bytes.length = width)
      (eval : subtreeCV? root (.leaf first width) bytes = some cv) :
      Renders size (.leaf first width) base root cv bytes [bytes]
  | fork {left right : Shape} {base : Nat} {root : Bool} {lcv rcv : CV}
      {lhs rhs : Bytes} {leftFields rightFields : List Bytes}
      (baseEq : (shapeSpan (.fork left right)).byteStart = base)
      (leftSize : lhs.length = left.size)
      (lhsRender : Renders size left base false lcv lhs leftFields)
      (rhsRender : Renders size right (base + left.size) false rcv rhs rightFields) :
      Renders size (.fork left right) base root (parentCV root lcv rcv) (lhs ++ rhs)
        ((digestBytes lcv ++ digestBytes rcv) :: (leftFields ++ rightFields))

private theorem spanWidth {total first width : Nat}
    (boundary : (0 < width ∧ width % 1024 = 0 ∧ first * 1024 + width ≤ total) ∨
      first * 1024 + width = total) :
    (Bao.Span.mk first (Bao.chunks width)).byteSize total = width := by
  change min total ((first + Bao.chunks width) * 1024) - first * 1024 = width
  unfold Bao.chunks Bao.chunkBytes
  omega

private theorem part_length {original : Bytes} {start width : Nat} (fits : start + width ≤ original.length) :
    (part original start width).length = width := by
  simp [part, List.length_take]
  omega

private theorem part_take (original : Bytes) (start left right : Nat) :
    (part original start (left + right)).take left = part original start left := by
  simp [part, List.take_take]

private theorem part_drop (original : Bytes) (start left right : Nat) :
    (part original start (left + right)).drop left = part original (start + left) right := by
  simp [part, List.drop_take, List.drop_drop]

private theorem eval_fork (root : Bool) (left right : Shape) (bytes : Bytes) :
    subtreeCV? root (.fork left right) bytes = (do
      let lcv ← subtreeCV? false left (bytes.take left.size)
      let rcv ← subtreeCV? false right (bytes.drop left.size)
      return parentCV root lcv rcv) := rfl

private theorem render {original : Bytes} (first width : Nat) (root : Bool) {cv : CV}
    (fits : first * 1024 + width ≤ original.length)
    (boundary : (0 < width ∧ width % 1024 = 0) ∨ first * 1024 + width = original.length)
    (hit : subtreeCV? root (geometry first width) (part original (first * 1024) width) = some cv) :
    ∃ fields, ((chunkPlan (geometry first width)).preorder.mapM (sizedSource original)) = some fields ∧
      Renders original.length (geometry first width) (first * 1024) root cv (part original (first * 1024) width) fields := by
  induction width using Nat.strongRecOn generalizing first root cv
  rename_i width ih
  have wsize := part_length (original := original) fits
  by_cases small : width ≤ 1024
  · have widthAt : (Bao.Span.mk first 1).byteSize original.length = width := by
      change min original.length ((first + 1) * 1024) - first * 1024 = width
      omega
    rw [geometry.eq_def, dite_eq_left small] at hit ⊢
    refine ⟨_, ?_, .leaf ⟨rfl, rfl⟩ (wsize.trans widthAt.symm) wsize hit⟩
    simp [chunkPlan, Bao.Plan.preorder, sizedSource, source, Bao.Span.byteStart, Bao.chunkBytes, Bao.Slot.width, wsize]
  · have large := Nat.lt_of_not_ge small
    have ⟨pos, less, modulo⟩ := split_bounds large
    have ⟨leftFits, leftBoundary, rightFits, rightBoundary⟩ := childBounds large fits boundary
    let leftWidth := splitBytes width
    let rightWidth := width - leftWidth
    let next := first + leftWidth / 1024
    have widthEq : leftWidth + rightWidth = width := by dsimp [leftWidth, rightWidth]; omega
    have baseEq : first * 1024 + leftWidth = next * 1024 := by dsimp [next, leftWidth]; omega
    change ∃ fields, ((chunkPlan (geometry first width)).preorder.mapM (sizedSource original)) = some fields ∧ _
    have ls : (geometry first leftWidth).size = leftWidth := geometry_size ..
    have toFork : geometry first width = .fork (geometry first leftWidth) (geometry next rightWidth) := by
      rw [geometry.eq_def, dite_eq_right small]
    have takeEq : (part original (first * 1024) width).take (geometry first leftWidth).size =
        part original (first * 1024) leftWidth := by
      rw [ls, ← widthEq]
      exact part_take ..
    have dropEq : (part original (first * 1024) width).drop (geometry first leftWidth).size =
        part original (next * 1024) rightWidth := by
      rw [ls, ← widthEq, part_drop, baseEq]
    rw [toFork] at hit ⊢
    rw [eval_fork, takeEq, dropEq] at hit
    cases lc : subtreeCV? false (geometry first leftWidth) (part original (first * 1024) leftWidth) with
    | none => simp [lc] at hit
    | some lcv =>
      cases rc : subtreeCV? false (geometry next rightWidth) (part original (next * 1024) rightWidth) with
      | none => simp [lc, rc] at hit
      | some rcv =>
        simp only [lc, rc, Option.bind_eq_bind, Option.bind_some] at hit
        cases Option.some.inj hit
        have rightSmaller : rightWidth < width := Nat.sub_lt (by omega) pos
        obtain ⟨leftFields, leftWrite, leftRender⟩ := ih leftWidth less first false leftFits leftBoundary lc
        obtain ⟨rightFields, rightWrite, rightRender⟩ := ih rightWidth rightSmaller next false rightFits rightBoundary rc
        have join : part original (first * 1024) leftWidth ++ part original (next * 1024) rightWidth =
            part original (first * 1024) width := by
          rw [← takeEq, ← dropEq, List.take_append_drop]
        have spanEq := canonicalSpan first width
        rw [toFork] at spanEq
        have leftAt : (Bao.Span.mk first (Bao.chunks leftWidth)).byteSize original.length = leftWidth :=
          spanWidth (leftBoundary.imp (fun b => ⟨b.1, b.2, leftFits⟩) id)
        have rightAt : (Bao.Span.mk next (Bao.chunks rightWidth)).byteSize original.length = rightWidth :=
          spanWidth (rightBoundary.imp (fun b => ⟨b.1, b.2, rightFits⟩) id)
        refine ⟨(digestBytes lcv ++ digestBytes rcv) :: (leftFields ++ rightFields), ?_, ?_⟩
        · have atPair : sizedSource original (.pair ⟨first, Bao.chunks width⟩) =
              some (digestBytes lcv ++ digestBytes rcv) := by
            have split : (Bao.Span.mk first (Bao.chunks width)).split =
                (⟨first, Bao.chunks leftWidth⟩, ⟨next, Bao.chunks rightWidth⟩) := split_span first width large
            simp [sizedSource, source, split, leftAt, rightAt, Bao.Span.byteStart, Bao.chunkBytes,
              lc, rc, digestBytes_length, Bao.Slot.width]
          simp [chunkPlan, Bao.Plan.preorder, List.mapM_append, spanEq, atPair, leftWrite, rightWrite]
        · rw [← join]
          exact .fork (by rw [spanEq]; rfl) ((part_length leftFits).trans ls.symm)
            leftRender (by rw [ls, baseEq]; exact rightRender)

private theorem parse_loaded {bytes : Bytes} {raw : Bao.Digest} {cv : CV}
    (parsed : Bao.digest? bytes = some raw) (roundTrip : loadWords raw = cv) (wire : digestBytes cv = bytes) :
    parseCV bytes = some ⟨cv, wire⟩ := by
  simp only [parseCV, parsed, Option.bind_eq_bind, Option.bind_some, roundTrip, dite_eq_left wire]

private theorem parse_digest (cv : CV) : parseCV (digestBytes cv) = some ⟨cv, rfl⟩ := by
  let raw := Vector.ofFn (fun pos : Fin 32 => wordByte cv[pos.val / 4] (pos.val % 4))
  have wire : raw.toList = digestBytes cv := rfl
  have parsed : Bao.digest? (digestBytes cv) = some raw := by
    simp only [Bao.digest?, digestBytes_length, dite_true, Option.some.injEq]
    exact Vector.toList_inj.mp (by simp [wire])
  have roundTrip : loadWords raw = cv := by
    apply Vector.ext
    intro index bound
    have atByte (delta : Nat) (small : delta < 4) :
        raw[4 * index + delta]'(by omega) = wordByte cv[index] delta := by
      simp [raw, show (4 * index + delta) / 4 = index by omega,
        show (4 * index + delta) % 4 = delta by omega]
    simp only [loadWords, Vector.getElem_ofFn]
    have zero : raw[4 * index] = wordByte cv[index] 0 := by simpa only [Nat.add_zero] using atByte 0 (by decide)
    calc
      _ = packWord (wordByte cv[index] 0) (wordByte cv[index] 1) (wordByte cv[index] 2)
          (wordByte cv[index] 3) := by simp only [zero, atByte 1 (by decide), atByte 2 (by decide), atByte 3 (by decide)]
      _ = cv[index] := by simpa only [wordByte] using Silmaril.Crypto.Word.pack32LE_unpack32LE cv[index]
  exact parse_loaded parsed roundTrip rfl

private theorem parse_pair (left right : CV) :
    parsePair (digestBytes left ++ digestBytes right) = some ⟨(left, right), rfl⟩ := by
  have take : (digestBytes left ++ digestBytes right).take 32 = digestBytes left := by
    rw [← show (digestBytes left).length = 32 from digestBytes_length left, List.take_left]
  have drop : (digestBytes left ++ digestBytes right).drop 32 = digestBytes right := by
    rw [← show (digestBytes left).length = 32 from digestBytes_length left, List.drop_left]
  have getLeft : ∃ cv, parseCV ((digestBytes left ++ digestBytes right).take 32) = some cv ∧ cv.val = left := by
    rw [take, parse_digest]
    exact ⟨_, rfl, rfl⟩
  have getRight : ∃ cv, parseCV ((digestBytes left ++ digestBytes right).drop 32) = some cv ∧ cv.val = right := by
    rw [drop, parse_digest]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨lcv, parsedLeft, eqLeft⟩ := getLeft
  obtain ⟨rcv, parsedRight, eqRight⟩ := getRight
  unfold parsePair
  rw [parsedLeft, parsedRight]
  exact congrArg some (Subtype.ext (Prod.ext eqLeft eqRight))

private def scheduled {size : Nat} {digest : Bytes} {shape : Shape} {base : Nat} {root edge : Bool} {cv : CV}
    (anchor : Anchor size digest shape root cv base edge) : Work size digest :=
  ⟨chunkPlan shape, shape, root, cv, base, edge, anchor⟩

private theorem enqueue_scheduled {size : Nat} {digest : Bytes} {shape : Shape} {base : Nat}
    {root edge : Bool} {cv : CV} (anchor : Anchor size digest shape root cv base edge) (tail : List (Work size digest)) :
    (scheduled anchor).enqueue tail = scheduled anchor :: tail := by
  cases shape <;> rfl

private inductive Replay {size : Nat} {digest : Bytes} : Session size digest → List Bytes → Session size digest → Type where
  | nil (state : Session size digest) : Replay state [] state
  | cons {state next final : Session size digest} {raw : Bytes} {rest : List Bytes} {cell : Cell size digest raw}
      (step : step? state raw = some (next, cell)) (tail : Replay next rest final) : Replay state (raw :: rest) final

private def Replay.tape {size : Nat} {digest : Bytes} {start finish : Session size digest} {fields : List Bytes} :
    Replay start fields finish → Tape size digest fields
  | .nil _ => .nil
  | .cons (cell := cell) _ rest => .cons cell rest.tape

private def Replay.append {size : Nat} {digest : Bytes} {start mid finish : Session size digest}
    {lhs rhs : List Bytes} (left : Replay start lhs mid) (right : Replay mid rhs finish) :
    Replay start (lhs ++ rhs) finish :=
  match left with
  | .nil _ => right
  | .cons step tail => .cons step (tail.append right)

private theorem Replay.check {size : Nat} {digest : Bytes} {start finish : Session size digest} {fields : List Bytes}
    (run : Replay start fields finish) : checkTape? start fields = some (finish, run.tape) := by
  induction run with
  | nil => rfl
  | cons step rest ih => simp [checkTape?, step, ih, Replay.tape]

private theorem Replay.spans_append {size : Nat} {digest : Bytes} {start mid finish : Session size digest}
    {lhs rhs : List Bytes} (left : Replay start lhs mid) (right : Replay mid rhs finish) :
    (left.append right).tape.spans = left.tape.spans ++ right.tape.spans := by
  induction left with
  | nil => rfl
  | @cons state next final raw fields cell step rest ih =>
    cases cell <;> simp [Replay.append, Replay.tape, Tape.spans, ih]

private theorem Renders.replay {size : Nat} {digest bytes : Bytes} {shape : Shape} {base : Nat}
    {root : Bool} {cv : CV} {fields : List Bytes} (rendered : Renders size shape base root cv bytes fields)
    {edge : Bool} (anchor : Anchor size digest shape root cv base edge)
    (pending : List (Work size digest)) (eof : Option (EOFProof size digest)) :
    ∃ nextEOF, ∃ run : Replay ⟨scheduled anchor :: pending, eof⟩ fields ⟨pending, nextEOF⟩,
      nextEOF.isSome = (edge || eof.isSome) ∧ Contiguous base run.tape.spans bytes := by
  induction rendered generalizing edge pending eof with
  | @leaf first width base root cv bytes aligned slotWidth length eval =>
    let facts := anchor.openCell length eval
    let nextEOF := if right : edge = true then some ⟨facts.2 right⟩ else eof
    let fact : SpanFact size digest := ⟨base, bytes, facts.1⟩
    let cell : Cell size digest bytes := .data ⟨first, 1⟩ fact
      ⟨_, root, cv, edge, aligned, slotWidth, length, anchor, eval⟩
    have exactWidth : bytes.length = width ∧ bytes.length = (Bao.Span.mk first 1).byteSize size ∧
        bytes.length = (Shape.leaf first width).size := ⟨length, slotWidth, length⟩
    have accepted : step? (⟨scheduled anchor :: pending, eof⟩ : Session size digest) bytes =
        some (⟨pending, nextEOF⟩, cell) := by
      simp only [scheduled, chunkPlan]
      rw [step?]
      dsimp only
      rw [dite_eq_left aligned, dite_eq_left exactWidth, dite_eq_left eval]
    refine ⟨nextEOF, .cons accepted (.nil _), ?_, ?_⟩
    · cases edge <;> simp [nextEOF]
    · change Contiguous base [fact] bytes
      simpa only [List.append_nil] using (Contiguous.cons (fact := fact) rfl (.nil (base + bytes.length)))
  | @fork left right base root lcv rcv lhs rhs leftFields rightFields baseEq leftSize leftRender rightRender leftIH rightIH =>
    let lhsAnchor := anchor.left (lcv := lcv) (rcv := rcv) rfl
    let rhsAnchor := anchor.right (lcv := lcv) (rcv := rcv) rfl
    let raw := digestBytes lcv ++ digestBytes rcv
    have aligned : Aligned (shapeSpan (.fork left right)) (.fork left right) base := ⟨rfl, baseEq⟩
    let cell : Cell size digest raw := .pair (shapeSpan (.fork left right)) root lcv rcv
      (parentCV root lcv rcv) rfl rfl ⟨left, right, base, edge, aligned, anchor⟩
    have accepted : step? (⟨scheduled anchor :: pending, eof⟩ : Session size digest) raw =
        some (⟨scheduled lhsAnchor :: scheduled rhsAnchor :: pending, eof⟩, cell) := by
      simp only [scheduled, chunkPlan]
      rw [step?]
      dsimp only
      rw [dite_eq_left aligned]
      have parsed : parsePair raw = some ⟨(lcv, rcv), rfl⟩ := parse_pair lcv rcv
      simp only [parsed, Option.bind_eq_bind, Option.bind_some]
      rw [dite_true]
      change some ((⟨(scheduled lhsAnchor).enqueue ((scheduled rhsAnchor).enqueue pending), eof⟩ :
        Session size digest), cell) = _
      rw [enqueue_scheduled, enqueue_scheduled]
      rfl
    obtain ⟨midEOF, leftRun, leftEOF, leftBytes⟩ := leftIH lhsAnchor (scheduled rhsAnchor :: pending) eof
    obtain ⟨finalEOF, rightRun, rightEOF, rightBytes⟩ := rightIH rhsAnchor pending midEOF
    refine ⟨finalEOF, .cons accepted (leftRun.append rightRun), ?_, ?_⟩
    · simpa [leftEOF] using rightEOF
    · change Contiguous base (leftRun.append rightRun).tape.spans (lhs ++ rhs)
      rw [Replay.spans_append]
      exact leftBytes.append (by simpa only [leftSize] using rightBytes)

set_option maxRecDepth 2048 in
theorem completeWindow {digest original : Bytes} {cap : Nat} (request : Request)
    (named : Named concrete digest original) (withinCap : original.length ≤ cap)
    (within : let window := request.window original.length; window.start + window.count ≤ original.length) :
    ∃ wire response, encode? original = some wire ∧
      decodeCombined? cap digest request wire = some response ∧
      response.claim = original.length ∧ response.eof.isSome = true ∧
      response.done.bytes = (original.drop (request.window original.length).start).take (request.window original.length).count := by
  obtain ⟨valid, cv, hashTrace, digestEq⟩ := named
  subst digest
  let size := original.length
  have partAll : part original (0 * 1024) size = original := by simp [part, size]
  obtain ⟨fields, writes, renders⟩ := render (original := original) 0 size true (by simp [size]) (by simp [size])
    (cv := cv) (by rw [partAll]; exact eval_graph.mpr hashTrace)
  rw [partAll] at renders
  have validWire : size < Bao.u64Limit := valid
  let wire := Bao.putLE64 size ++ fields.flatten
  have output : encode? original = some wire := by
    have layout : Bao.Encoding.combined.layout size = (chunkPlan (geometry 0 size)).preorder := by
      exact congrArg Bao.Plan.preorder (fullPlan_geometry size)
    change Bao.encode .combined size (source original) = some wire
    simp only [Bao.encode, Bao.Encoding.valid, validWire, decide_true, Bool.and_true, Bool.not_true,
      Bool.false_eq_true, ite_false, Bao.writeSlots, layout]
    change (do
        let body ← (do
          let checked ← (chunkPlan (geometry 0 size)).preorder.mapM (sizedSource original)
          return checked.flatten)
        return Bao.putLE64 size ++ body) = some wire
    simp [writes, wire]
  have header : Bao.readHeader wire = some (size, fields.flatten) := Bao.readHeader_putLE64 fields.flatten validWire
  have tape := mapFields_tape writes
  have widths : fields.flatten.length = 64 * (Bao.chunks size - 1) + size := by
    rw [tape_length tape]
    simp [shapePlan_width, canonicalSpan, geometry_size]
  have parsed : Bao.decode .combined wire = some (size, fields) := by
    apply Bao.decode_spec.mpr
    exact ⟨rfl, by simp [Bao.Encoding.bodyFits, widths], header, by
      rw [show Bao.Encoding.combined.layout size = (Bao.fullPlan size 1).preorder from rfl, fullPlan_geometry]; exact tape⟩
  let anchor := rootAnchor valid (show digestBytes cv = digestBytes cv from rfl)
  obtain ⟨eof, run, right, contiguous⟩ := renders.replay anchor [] none
  have init : begin? size cap (digestBytes cv) (Bao.fullPlan size 1) = some ⟨[scheduled anchor], none⟩ := by
    rw [fullPlan_geometry]
    have within : ¬cap < size := Nat.not_lt.mpr withinCap
    have validAtSize : validSize size := valid
    simp only [begin?, within, ite_false, dite_eq_left validAtSize, parse_digest, Option.bind_eq_bind, Option.bind_some]
    cases eq : chunkPlan (geometry 0 size) with
    | skip =>
      have neq : ∀ shape, chunkPlan shape ≠ .skip := by intro shape; cases shape <;> simp [chunkPlan]
      exact False.elim (neq _ eq)
    | leaf span width => simpa only [scheduled] using congrArg (fun plan =>
        some (⟨[⟨plan, geometry 0 size, true, cv, 0, true, anchor⟩], none⟩ : Session size _)) eq.symm
    | fork span left right => simpa only [scheduled] using congrArg (fun plan =>
        some (⟨[⟨plan, geometry 0 size, true, cv, 0, true, anchor⟩], none⟩ : Session size _)) eq.symm
  let body : CompleteBody size (digestBytes cv) fields := ⟨run.tape, ⟨[], eof⟩, rfl⟩
  have checked : checkBody? size cap (digestBytes cv) (Bao.fullPlan size 1) fields = some body := by
    simp [checkBody?, init, run.check, body]
  have ends : (request.window size).start + (request.window size).count ≤ 0 + original.length := by
    simpa only [Nat.zero_add] using within
  obtain ⟨result, done, bytes⟩ := Projection.range (base := 0) (request.window size) body contiguous
    (Nat.zero_le _) ends within
  refine ⟨wire, ⟨size, .body body done, eof⟩, output, ?_, rfl, right, ?_⟩
  swap
  · change result.coverage.bytes = _
    simpa only [Nat.sub_zero] using bytes
  have within : ¬cap < size := Nat.not_lt.mpr withinCap
  simp only [decodeCombined?, checkBaoInline?, InlineEncoding.encoding, header, Option.bind_eq_bind,
    Option.bind_some, within, ite_false]
  split
  · rename_i failed; exact nomatch parsed.symm.trans failed
  · rename_i gotSize gotFields success
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (parsed.symm.trans success))
    simp only [InlineEncoding.plan, checked, Option.bind_some, Option.pure_def]
    unfold ofBody?
    split
    · rename_i failed; exact nomatch done.symm.trans failed
    · rename_i answer success
      have same := Option.some.inj (success.symm.trans done)
      cases same
      rfl

theorem complete {digest original : Bytes} {cap : Nat}
    (named : Named concrete digest original) (withinCap : original.length ≤ cap) :
    ∃ wire response, encode? original = some wire ∧
      decodeCombined? cap digest (.toEnd 0) wire = some response ∧
      response.claim = original.length ∧ response.eof.isSome = true ∧ response.done.bytes = original := by
  simpa [Request.window] using completeWindow (.toEnd 0) named withinCap (by simp [Request.window])

end Silmaril.Proofs.Formats.Blake3Cas.RangeFacts.Combined
