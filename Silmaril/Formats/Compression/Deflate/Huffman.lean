module

public import Silmaril.Formats.Compression.Bits.Bitstream

@[expose] public section

namespace Silmaril.Formats.Compression

def maxCodeBitsDefault : Nat := 15
def maxAlphabetSize : Nat := 286

abbrev CodeLengths := List Nat

structure CodeEntry where
  symbol : Nat
  code : Nat
  length : Nat
deriving Repr, Inhabited

structure HuffmanTable where
  maxBits : Nat
  entries : List CodeEntry
  symbolCodes : List (Option (Nat × Nat))
  alphabetSize : Nat
deriving Repr

def HuffmanTable.empty (maxBits : Nat) (alphabetSize : Nat := maxAlphabetSize) : HuffmanTable :=
  { maxBits, entries := [], symbolCodes := List.replicate alphabetSize none, alphabetSize }

def modifyListAtIdx.{u} {α : Type u} (l : List α) (idx : Nat) (f : α → α) : List α :=
  match l, idx with
  | [], _ => []
  | x :: xs, 0 => f x :: xs
  | x :: xs, n+1 => x :: modifyListAtIdx xs n f

def listGet.{u} {α : Type u} (l : List α) (i : Nat) : Option α :=
  match l, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n+1 => listGet xs n

def enumerateList.{u} {α : Type u} (l : List α) : List (Nat × α) :=
  let rec go (n : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: xs => (n, x) :: go (n+1) xs
  go 0 l

/-! ### Canonical code construction -/

/-- Count how many codes have each length 1..maxBits. -/
def countByLength (lengths : CodeLengths) (maxBits : Nat) : List Nat :=
  let rec go : CodeLengths → List Nat → List Nat
    | [], counts => counts
    | len :: rest, counts =>
      if 0 < len ∧ len ≤ maxBits then
        go rest (modifyListAtIdx counts (len-1) (λ c => c+1))
      else go rest counts
  go lengths (List.replicate maxBits 0)

/-- RFC 1951 step 2: compute smallest code value for each length. -/
def nextCode (blCount : List Nat) : List Nat :=
  let rec go : List Nat → Nat → List Nat
    | [], _ => []
    | c :: cs, code => code :: go cs ((code + c) <<< 1)
  go blCount 0

/-- RFC 1951 step 3: assign canonical codes in symbol order. -/
def assignCodes (lengths : CodeLengths) (maxBits : Nat) : List CodeEntry :=
  let blCount := countByLength lengths maxBits
  let nc := nextCode blCount
  let rec loop : Nat → List Nat → CodeLengths → List CodeEntry
    | _, _, [] => []
    | i, ncRemaining, len :: rest =>
      let entry : CodeEntry :=
        if len = 0 ∨ len > maxBits then
          { symbol := i, code := 0, length := 0 }
        else
          match listGet ncRemaining (len-1) with
          | none => { symbol := i, code := 0, length := 0 }
          | some c => { symbol := i, code := c, length := len }
      let ncRemaining' :=
        if len = 0 ∨ len > maxBits then ncRemaining
        else modifyListAtIdx ncRemaining (len-1) (λ c => c+1)
      entry :: loop (i+1) ncRemaining' rest
  loop 0 nc lengths

/-! ### Validation -/

/-- The Kraft sum Σ 2^(maxBits - len_i), in units of `2 ^ (-maxBits)`.
Only meaningful when every nonzero length is at most `maxBits`. -/
def kraftSum (lengths : CodeLengths) (maxBits : Nat) : Nat :=
  lengths.foldl (λ (acc : Nat) (len : Nat) =>
    if len = 0 then acc else acc + (1 <<< (maxBits - len))) 0

/-- Every length is at most `maxBits` and the Kraft inequality Σ 2^(-len_i) ≤ 1
holds.  RFC 1951 §3.2.7 caps code lengths at 15 and forbids over-subscribed
length sets, so both conjuncts are required; `Nat` subtraction would otherwise
let an over-long code contribute the *smallest* possible weight. -/
def isValidLengths (lengths : CodeLengths) (maxBits : Nat) : Bool :=
  lengths.all (λ (len : Nat) => len ≤ maxBits) && (kraftSum lengths maxBits ≤ (1 <<< maxBits))

/-- A complete code: every length is at most `maxBits` and the Kraft sum is
exactly 1.  RFC 1951 requires this of the code-length and literal/length codes;
the distance code may instead be the degenerate one-code set. -/
def isCompleteCode (lengths : CodeLengths) (maxBits : Nat) : Bool :=
  lengths.all (λ (len : Nat) => len ≤ maxBits) && (kraftSum lengths maxBits = (1 <<< maxBits))

/-! ### Building the table -/

/-- Build a canonical Huffman table from code lengths (RFC 1951 §3.2.2).
Returns `none` when `isValidLengths` rejects the lengths, i.e. when some length
exceeds `maxBits` or the set is over-subscribed.  An *incomplete* set (Kraft sum
< 1) is accepted: RFC 1951 permits one such case, the single distance code, and
the decoder simply fails on the unused bit patterns.  Callers that must reject
incomplete codes should check `isCompleteCode` as well. -/
def HuffmanTable.ofLengths (lengths : CodeLengths) (maxBits : Nat) : Option HuffmanTable :=
  if !isValidLengths lengths maxBits then none
  else
    let entries : List CodeEntry := assignCodes lengths maxBits
    -- `entries` lists symbols `0, 1, …` in order, so symbol `i`'s code is entry `i`.
    let symbolCodes : List (Option (Nat × Nat)) := entries.map (λ (e : CodeEntry) =>
      if e.length > 0 then some (e.code, e.length) else none)
    some { maxBits, entries, symbolCodes, alphabetSize := lengths.length }

/-! ### Encoding -/

/-- Get the (code, length) for a symbol, or `none` if not present. -/
def HuffmanTable.encodeSymbol (t : HuffmanTable) (sym : Nat) : Option (Nat × Nat) :=
  match listGet t.symbolCodes sym with
  | none => none
  | some opt => opt

/-- Encode a symbol to an LSB writer. -/
def HuffmanTable.writeSymbolLSB (t : HuffmanTable) (w : LSBWriter) (sym : Nat) :
    Option LSBWriter :=
  match t.encodeSymbol sym with
  | none => none
  | some (code, len) => some (w.writeCodeMSB code len)

/-- Encode a symbol to an MSB writer. -/
def HuffmanTable.writeSymbolMSB (t : HuffmanTable) (w : MSBWriter) (sym : Nat) :
    Option MSBWriter :=
  match t.encodeSymbol sym with
  | none => none
  | some (code, len) => some (w.writeVal code len)

/-! ### Decoding -/

/-- Linear scan through entries for a (code, len) pair. -/
def lookupEntry (entries : List CodeEntry) (code : Nat) (len : Nat) : Option Nat :=
  let rec go : List CodeEntry → Option Nat
    | [] => none
    | (e : CodeEntry) :: rest =>
      if 0 < e.length ∧ e.length = len ∧ e.code = code then some e.symbol
      else go rest
  go entries

theorem lookupEntry_go_eq_none_of_len_zero (code : Nat) :
    ∀ (es : List CodeEntry), lookupEntry.go code 0 es = none := by
  intro es
  induction es with
  | nil => rfl
  | cons e rest ih =>
    simp only [lookupEntry.go, ih]
    split
    · next h => exact absurd h.2.1 (by omega)
    · rfl

/-- Same scan with a `Bool` test and the loop-invariant `len ≠ 0` hoisted out of
the loop.  `lookupEntry` is called once per candidate code length per symbol, so
this inner loop is the decoder's hot spot; the `Decidable (_ ∧ _)` instance in
`lookupEntry.go` allocates on every entry. -/
def lookupEntryFast (entries : List CodeEntry) (code : Nat) (len : Nat) : Option Nat :=
  if len == 0 then none else
    let rec go : List CodeEntry → Option Nat
      | [] => none
      | (e : CodeEntry) :: rest =>
        if e.length == len && e.code == code then some e.symbol else go rest
    go entries

theorem lookupEntryFast_go_eq (code len : Nat) (hlen : len ≠ 0) :
    ∀ (es : List CodeEntry), lookupEntryFast.go code len es = lookupEntry.go code len es := by
  intro es
  induction es with
  | nil => rfl
  | cons e rest ih =>
    simp only [lookupEntryFast.go, lookupEntry.go, Bool.and_eq_true, beq_iff_eq, ih]
    by_cases h1 : e.length = len
    · by_cases h2 : e.code = code
      · simp only [h1, h2, and_true, ↓reduceIte]
        rw [ite_eq_left (by omega)]
      · simp [h1, h2]
    · simp [h1]

@[csimp] theorem lookupEntry_eq_lookupEntryFast : @lookupEntry = @lookupEntryFast := by
  funext entries code len
  by_cases h : len = 0
  · subst h
    simp only [lookupEntryFast, beq_self_eq_true, ↓reduceIte, lookupEntry]
    apply lookupEntry_go_eq_none_of_len_zero
  · simp only [lookupEntryFast, lookupEntry, beq_iff_eq, h, ↓reduceIte]
    exact (lookupEntryFast_go_eq code len h entries).symm

/-- Decode a symbol from an LSB reader, reading at most `maxIter` bits. -/
def decodeSymbolLSBAux (entries : List CodeEntry) (r : LSBReader)
    (code : Nat) (len : Nat) (maxIter : Nat) : Option (Nat × LSBReader) :=
  match maxIter with
  | 0 => none
  | n+1 =>
    match lookupEntry entries code len with
    | some sym => some (sym, r)
    | none =>
      match r.readBit with
      | none => none
      | some (b, r') =>
        -- Huffman codes are packed most-significant bit first.
        let newCode := code * 2 + (if b then 1 else 0)
        decodeSymbolLSBAux entries r' newCode (len+1) n

/-- Decode the next symbol from an LSB reader. A code of length `maxBits` needs
`maxBits + 1` lookups (lengths `0, …, maxBits`). -/
def HuffmanTable.readSymbolLSB (t : HuffmanTable) (r : LSBReader) : Option (Nat × LSBReader) :=
  decodeSymbolLSBAux t.entries r 0 0 (t.maxBits + 1)

/-! ### A decode index

`lookupEntry` is a linear scan, and `decodeSymbolLSBAux` calls it once per
candidate code length per symbol, so decoding costs `O(maxBits × |entries|)` per
symbol.  The index below is built once per block and answers the same question
in O(1); `lookupEntryIdx_eq` proves it gives exactly `lookupEntry`'s answer, so
the decoder's specification is untouched.

The key of a code is `2 ^ len + code`, which is injective on the codes that can
actually occur (`0 < len ≤ 15` and `code < 2 ^ len`, RFC 1951 §3.2.7).  Anything
outside that range falls back to the scan, so the equality holds for *every*
entry list, including malformed ones. -/

/-- RFC 1951 §3.2.7 caps code lengths at 15. -/
def decMaxBits : Nat := 15

/-- Number of slots in a decode index: one per `(len, code)` with `len ≤ 15`. -/
def decTableSize : Nat := 2 ^ (decMaxBits + 1)

/-- Index of the code `code` of length `len`. -/
def decKey (code len : Nat) : Nat := 2 ^ len + code

/-- A `(code, len)` pair the index can represent. -/
def DecKeyOK (code len : Nat) : Prop := 0 < len ∧ len ≤ decMaxBits ∧ code < 2 ^ len

instance (code len : Nat) : Decidable (DecKeyOK code len) := by
  unfold DecKeyOK; infer_instance

theorem decKey_lt {code len : Nat} (h : DecKeyOK code len) : decKey code len < decTableSize := by
  obtain ⟨_, h2, h3⟩ := h
  have : (2 : Nat) ^ len ≤ 2 ^ decMaxBits := Nat.pow_le_pow_right (by decide) h2
  simp only [decKey, decTableSize, decMaxBits] at *
  omega

theorem decKey_inj {c l c' l' : Nat} (h : DecKeyOK c l) (h' : DecKeyOK c' l')
    (he : decKey c l = decKey c' l') : l = l' ∧ c = c' := by
  obtain ⟨_, _, hc⟩ := h
  obtain ⟨_, _, hc'⟩ := h'
  simp only [decKey] at he
  have key : ∀ a b : Nat, a < b → 2 ^ a + 2 ^ a ≤ 2 ^ b := by
    intro a b hab
    have : (2 : Nat) ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hab
    rw [Nat.pow_succ] at this
    omega
  have hl : l = l' := by
    rcases Nat.lt_trichotomy l l' with h1 | h1 | h1
    · have := key l l' h1; omega
    · exact h1
    · have := key l' l h1; omega
  subst hl
  exact ⟨rfl, by omega⟩

/-- Record one entry in the index, keeping the *first* entry for each key so
that the index agrees with `lookupEntry`'s "first match wins". -/
def insertDecEntry (a : Array Nat) (e : CodeEntry) : Array Nat :=
  if DecKeyOK e.code e.length ∧ a.getD (decKey e.code e.length) 0 = 0 then
    a.setIfInBounds (decKey e.code e.length) (e.symbol + 1)
  else a

/-- The index for an entry list: slot `decKey code len` holds `symbol + 1`, or 0
when no entry has that code. -/
def buildDecTable : List CodeEntry → Array Nat → Array Nat
  | [], a => a
  | e :: rest, a => buildDecTable rest (insertDecEntry a e)

/-- The decode index of an entry list. -/
def decTable (entries : List CodeEntry) : Array Nat :=
  buildDecTable entries (Array.replicate decTableSize 0)

theorem insertDecEntry_size (a : Array Nat) (e : CodeEntry) :
    (insertDecEntry a e).size = a.size := by
  unfold insertDecEntry
  split
  · simp
  · rfl

theorem buildDecTable_get {code len : Nat} (hk : DecKeyOK code len) :
    ∀ (es : List CodeEntry) (a : Array Nat), decTableSize ≤ a.size →
      (buildDecTable es a).getD (decKey code len) 0 =
        if a.getD (decKey code len) 0 = 0 then
          ((lookupEntry.go code len es).map (· + 1)).getD 0
        else a.getD (decKey code len) 0 := by
  intro es
  induction es with
  | nil => intro a _; simp [buildDecTable, lookupEntry.go]
  | cons e rest ih =>
    intro a ha
    have hlt : decKey code len < a.size := Nat.lt_of_lt_of_le (decKey_lt hk) ha
    rw [buildDecTable, ih _ (by rw [insertDecEntry_size]; exact ha)]
    by_cases hg : DecKeyOK e.code e.length
    · by_cases hsame : decKey e.code e.length = decKey code len
      · obtain ⟨hl, hc⟩ := decKey_inj hg hk hsame
        have hmatch : (0 < e.length ∧ e.length = len ∧ e.code = code) := ⟨hg.1, hl, hc⟩
        rw [lookupEntry.go, ite_eq_left hmatch]
        by_cases hz : a.getD (decKey code len) 0 = 0
        · have hcond : DecKeyOK e.code e.length ∧ a.getD (decKey e.code e.length) 0 = 0 :=
            ⟨hg, by rw [hsame]; exact hz⟩
          have hset : (insertDecEntry a e).getD (decKey code len) 0 = e.symbol + 1 := by
            rw [insertDecEntry, ite_eq_left hcond, hsame, Array.getD_eq_getD_getElem?,
              Array.getElem?_setIfInBounds]
            simp [hlt]
          rw [hset, hz]
          simp
        · have hcond : ¬ (DecKeyOK e.code e.length ∧ a.getD (decKey e.code e.length) 0 = 0) := by
            intro hx
            rw [hsame] at hx
            exact hz hx.2
          have hkeep : insertDecEntry a e = a := by rw [insertDecEntry, ite_eq_right hcond]
          rw [hkeep, ite_eq_right hz, ite_eq_right hz]
      · have hnomatch : ¬ (0 < e.length ∧ e.length = len ∧ e.code = code) := by
          intro hx
          exact hsame (by rw [decKey, decKey, hx.2.1, hx.2.2])
        have hkeep : (insertDecEntry a e).getD (decKey code len) 0
            = a.getD (decKey code len) 0 := by
          rw [insertDecEntry]
          split
          · simp [Array.getD_eq_getD_getElem?, hsame, hlt]
          · rfl
        rw [hkeep, lookupEntry.go, ite_eq_right hnomatch]
    · have hnomatch : ¬ (0 < e.length ∧ e.length = len ∧ e.code = code) := by
        intro hx
        exact hg ⟨hx.1, by rw [hx.2.1]; exact hk.2.1, by rw [hx.2.1, hx.2.2]; exact hk.2.2⟩
      have hkeep : insertDecEntry a e = a := by
        rw [insertDecEntry, ite_eq_right (by intro hx; exact hg hx.1)]
      rw [hkeep, lookupEntry.go, ite_eq_right hnomatch]

/-- Look a code up in the index, falling back to the scan for keys the index
cannot represent. -/
def lookupEntryIdx (idx : Array Nat) (entries : List CodeEntry) (code len : Nat) : Option Nat :=
  if DecKeyOK code len then
    (if idx.getD (decKey code len) 0 = 0 then none
      else some (idx.getD (decKey code len) 0 - 1))
  else lookupEntry entries code len

theorem lookupEntryIdx_eq (entries : List CodeEntry) (code len : Nat) :
    lookupEntryIdx (decTable entries) entries code len = lookupEntry entries code len := by
  unfold lookupEntryIdx
  split
  · next hk =>
    have h := buildDecTable_get hk entries (Array.replicate decTableSize 0) (by simp)
    have hz : (Array.replicate decTableSize 0).getD (decKey code len) 0 = 0 := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    rw [hz] at h
    simp only [↓reduceIte] at h
    simp only [decTable, h, lookupEntry]
    cases lookupEntry.go code len entries with
    | none => simp
    | some sym => simp
  · rfl

/-- Decode a symbol through the index.  Mirrors `decodeSymbolLSBAux` exactly. -/
def decodeSymbolIdxAux (idx : Array Nat) (entries : List CodeEntry) (r : LSBReader)
    (code : Nat) (len : Nat) (maxIter : Nat) : Option (Nat × LSBReader) :=
  match maxIter with
  | 0 => none
  | n+1 =>
    match lookupEntryIdx idx entries code len with
    | some sym => some (sym, r)
    | none =>
      match r.readBit with
      | none => none
      | some (b, r') =>
        let newCode := code * 2 + (if b then 1 else 0)
        decodeSymbolIdxAux idx entries r' newCode (len+1) n

theorem decodeSymbolIdxAux_eq (entries : List CodeEntry) :
    ∀ (maxIter : Nat) (r : LSBReader) (code len : Nat),
      decodeSymbolIdxAux (decTable entries) entries r code len maxIter
        = decodeSymbolLSBAux entries r code len maxIter := by
  intro maxIter
  induction maxIter with
  | zero => intro r code len; rfl
  | succ n ih =>
    intro r code len
    rw [decodeSymbolIdxAux, decodeSymbolLSBAux, lookupEntryIdx_eq]
    cases lookupEntry entries code len with
    | some sym => rfl
    | none =>
      cases r.readBit with
      | none => rfl
      | some p => exact ih p.2 _ _

/-- Decode the next symbol using a prebuilt index. -/
def HuffmanTable.readSymbolIdx (t : HuffmanTable) (idx : Array Nat) (r : LSBReader) :
    Option (Nat × LSBReader) :=
  decodeSymbolIdxAux idx t.entries r 0 0 (t.maxBits + 1)

theorem HuffmanTable.readSymbolIdx_eq (t : HuffmanTable) (r : LSBReader) :
    t.readSymbolIdx (decTable t.entries) r = t.readSymbolLSB r :=
  decodeSymbolIdxAux_eq t.entries (t.maxBits + 1) r 0 0

/-- Decode a symbol from an MSB reader, reading at most `maxIter` bits. -/
def decodeSymbolMSBAux (entries : List CodeEntry) (r : MSBReader)
    (code : Nat) (len : Nat) (maxIter : Nat) : Option (Nat × MSBReader) :=
  match maxIter with
  | 0 => none
  | n+1 =>
    match lookupEntry entries code len with
    | some sym => some (sym, r)
    | none =>
      match r.readBit with
      | none => none
      | some (b, r') =>
        let newCode := code * 2 + (if b then 1 else 0)
        decodeSymbolMSBAux entries r' newCode (len+1) n

/-- Decode the next symbol from an MSB reader. -/
def HuffmanTable.readSymbolMSB (t : HuffmanTable) (r : MSBReader) : Option (Nat × MSBReader) :=
  decodeSymbolMSBAux t.entries r 0 0 (t.maxBits + 1)

/-! ### Huffman tree from frequencies -/

/-- A node in a Huffman tree: leaf or internal node. -/
inductive HuffmanNode where
  | leaf (symbol weight : Nat)
  | node (left right : HuffmanNode) (weight : Nat)
deriving Repr

/-- Weight of a Huffman node. -/
def HuffmanNode.weight : HuffmanNode → Nat
  | .leaf _ w => w
  | .node _ _ w => w

/-- Extract (symbol, depth) pairs from a tree. -/
def HuffmanNode.lengths (t : HuffmanNode) (depth : Nat) : List (Nat × Nat) :=
  match t with
  | .leaf sym _ => [(sym, depth)]
  | .node l r _ => l.lengths (depth + 1) ++ r.lengths (depth + 1)

/-- Insert a node into a weight-sorted list. -/
def insertSorted (node : HuffmanNode) : List HuffmanNode → List HuffmanNode
  | [] => [node]
  | h :: t =>
    if node.weight ≤ h.weight then node :: h :: t
    else h :: insertSorted node t

/-- Sort trees by weight ascending. -/
def sortByWeight : List HuffmanNode → List HuffmanNode
  | [] => []
  | h :: t => insertSorted h (sortByWeight t)

/-- Build a Huffman tree by bounded merges (at most `numLeaves` iterations). -/
def buildHuffmanTreeBounded (freqs : List (Nat × Nat)) : Option HuffmanNode :=
  let leaves : List HuffmanNode := freqs.map (λ (s, f) => .leaf s f)
  let rec go (remaining : Nat) : List HuffmanNode → Option HuffmanNode
    | [] => none
    | [t] => some t
    | a :: b :: rest =>
      match remaining with
      | 0 => none
      | r+1 => go r (insertSorted (.node a b (a.weight + b.weight)) rest)
  go leaves.length (sortByWeight leaves)

/-- Code lengths from symbol frequencies by classic Huffman tree depth.
Returns `none` when some depth exceeds `maxBits`: length-limiting (the
package-merge algorithm RFC 1951 §3.2.7 needs for its 15-bit cap) is not
implemented here. -/
def lengthsFromFreqs (freqs : List Nat) (maxBits : Nat) : Option CodeLengths :=
  let idxFreqs := enumerateList freqs
  let nonZero := idxFreqs.filter (λ (p : Nat × Nat) => p.2 > 0)
  let lengths : Option CodeLengths :=
    if nonZero.length ≤ 1 then
      some (freqs.map (λ (f : Nat) => if f > 0 then 1 else 0))
    else
      match buildHuffmanTreeBounded nonZero with
      | none => none
      | some tree =>
        let pairs := tree.lengths 0
        some ((List.range freqs.length).map (λ (s : Nat) =>
          match pairs.find? (λ (p : Nat × Nat) => p.1 = s) with
          | none => 0
          | some (_, d) => d))
  match lengths with
  | none => none
  | some ls => if ls.all (λ (len : Nat) => len ≤ maxBits) then some ls else none

end Silmaril.Formats.Compression
