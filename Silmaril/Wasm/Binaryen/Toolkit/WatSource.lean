module

public import Silmaril.Wasm.Binaryen.Toolkit.WatParseSound
public import Silmaril.Wasm.Text.Core.FunctionalInstrs

@[expose] public section

/-! A source-directed, proof-carrying WAT elaborator. Every accepted subtree
carries a derivation in the existing Core text grammar for that exact subtree.
Hints used to resolve the module's identifier/type context are untrusted and
checked against the independently elaborated field contributions at the end. -/

namespace Silmaril.Wasm.Binaryen.Toolkit.Wat.Source

open Silmaril Silmaril.Wasm Silmaril.Wasm.Text
open Silmaril.Formats.SExpEncoding (toList? doc)
open Text.Core

def list? (x : SExp) : Option {xs : List SExp // x = L xs} := do
  let xs ← toList? x
  if h : x = L xs then some ⟨xs, h⟩ else none

def mapCertified {α β : Type} {R : α → β → Prop}
    (f : (a : α) → Option {b : β // R a b}) :
    (as : List α) → Option {bs : List β // List.Forall₂ R as bs}
  | [] => some ⟨[], .nil⟩
  | a :: as => do
      let b ← f a
      let bs ← mapCertified f as
      pure ⟨b.1 :: bs.1, .cons b.2 bs.2⟩

def index? {k : IndexKind} (names : List (Option String)) (x : SExp) :
    Option {i : Wasm.Idx k // Text.Idx names x i} := do
  match hx : x with
  | .atom (.sym text) =>
      let n ← (ValuesExamples.unCands 32 text.toList).head?
      let i ← Wasm.Idx.ofNat? n
      if h : n ∈ ValuesExamples.unCands 32 text.toList ∧ i.toNat = n then
        some ⟨i, .inl ⟨text, hx, h.2 ▸ ValuesExamples.un_iff.mpr h.1⟩⟩
      else none
  | .atom (.id name) =>
      let n ← names.findIdx? (· == some name)
      let i ← Wasm.Idx.ofNat? n
      if h : names[i.toNat]? = some (some name) then
        some ⟨i, .inr ⟨name, hx, h⟩⟩
      else none
  | _ => none

def heap? (I : IdCtx) (x : SExp) : Option {h : HeapType // HeapTypeT I x h} := do
  match hx : x with
  | .atom (.sym name) =>
      match ha : absHeapKw name with
      | some a => some ⟨.abstract a, .inl ⟨name, a, hx, ha, rfl⟩⟩
      | none =>
          let i ← index? I.types x
          pure ⟨.typeIdx i.1, .inr ⟨i.1, i.2, rfl⟩⟩
  | _ =>
      let i ← index? I.types x
      pure ⟨.typeIdx i.1, .inr ⟨i.1, i.2, rfl⟩⟩

def reference? (I : IdCtx) (x : SExp) : Option {r : RefType // RefTypeT I x r} := do
  match hx : x with
  | .atom (.sym name) =>
      let a ← refAbbrevKw name
      if ha : refAbbrevKw name = some a then
        some ⟨⟨true, .abstract a⟩, .inr (.inr ⟨name, a, hx, ha, rfl⟩)⟩
      else none
  | _ =>
      match toList? x with
      | some [.atom (.sym "ref"), .atom (.sym "null"), ht] =>
          let h ← heap? I ht
          if hx : x = L [K "ref", K "null", ht] then
            some ⟨⟨true, h.1⟩, .inr (.inl ⟨ht, h.1, hx, h.2, rfl⟩)⟩
          else none
      | some [.atom (.sym "ref"), ht] =>
          let h ← heap? I ht
          if hx : x = L [K "ref", ht] then
            some ⟨⟨false, h.1⟩, .inl ⟨ht, h.1, hx, h.2, rfl⟩⟩
          else none
      | _ => none

def value? (I : IdCtx) (x : SExp) : Option {t : ValType // ValTypeT I x t} := do
  match hx : x with
  | .atom (.sym "v128") => pure ⟨.vec .v128, .inr (.inl ⟨hx, rfl⟩)⟩
  | .atom (.sym name) =>
      match hn : numTypeKw name with
      | some n => pure ⟨.num n, .inl ⟨name, n, hx, hn, rfl⟩⟩
      | none =>
          let r ← reference? I x
          pure ⟨.ref r.1, .inr (.inr ⟨r.1, r.2, rfl⟩)⟩
  | _ =>
      let r ← reference? I x
      pure ⟨.ref r.1, .inr (.inr ⟨r.1, r.2, rfl⟩)⟩

def integer? (width : Nat) (x : SExp) :
    Option {b : BitVec width // AtomI width x b} := do
  match hx : x with
  | .atom (.sym text) =>
      let b ← (ValuesExamples.inCands width text.toList).head?
      if h : b ∈ ValuesExamples.inCands width text.toList then
        some ⟨b, ⟨text, hx, ValuesExamples.in_iff.mpr h⟩⟩
      else none
  | _ => none

def float? (t : FloatType) (x : SExp) :
    Option {b : BitVec t.width // AtomF t x b} := do
  match hx : x with
  | .atom (.sym text) =>
      let b ← (ValuesExamples.fnCands t text.toList).head?
      if h : b ∈ ValuesExamples.fnCands t text.toList then
        some ⟨b, ⟨text, hx, ValuesExamples.fn_iff.mpr h⟩⟩
      else none
  | _ => none

def unsigned? (width : Nat) (x : SExp) :
    Option {n : Fin (2 ^ width) // AtomU width x n.val} := do
  match hx : x with
  | .atom (.sym text) =>
      let n ← (ValuesExamples.unCands width text.toList).head?
      if h : n < 2 ^ width ∧ n ∈ ValuesExamples.unCands width text.toList then
        some ⟨⟨n, h.1⟩, ⟨text, hx, ValuesExamples.un_iff.mpr h.2⟩⟩
      else none
  | _ => none

/-- An original attribute token, checked against the literal relation. -/
def attribute? (stem : String) (x : SExp) :
    Option {n : Fin (2 ^ 64) // ∃ t r, x = K t ∧
      t.toList = stem.toList ++ r ∧ UN 64 r n.val} := do
  match hx : x with
  | .atom (.sym text) =>
      let r := text.toList.drop stem.toList.length
      let n ← (ValuesExamples.unCands 64 r).head?
      if h : text.toList = stem.toList ++ r ∧ n < 2 ^ 64 ∧
          n ∈ ValuesExamples.unCands 64 r then
        some ⟨⟨n, h.2.1⟩, ⟨text, r, hx, h.1, ValuesExamples.un_iff.mpr h.2.2⟩⟩
      else none
  | _ => none

def takeAttribute (stem : String) : List SExp → List SExp × List SExp
  | .atom (.sym text) :: xs =>
      if stem.toList.isPrefixOf text.toList then ([K text], xs) else ([], K text :: xs)
  | xs => ([], xs)

def offsetPart? (xs : List SExp) : Option {o : Fin (2 ^ 64) //
    (xs = [] ∧ o = 0) ∨ ∃ t r, xs = [K t] ∧
      t.toList = "offset=".toList ++ r ∧ UN 64 r o.val} := do
  match hx : xs with
  | [] => pure ⟨0, .inl ⟨hx, rfl⟩⟩
  | [x] =>
      let o ← attribute? "offset=" x
      pure ⟨o.1, .inr (by
        obtain ⟨t, r, ht, hr, hn⟩ := o.2
        exact ⟨t, r, by simpa [ht] using hx, hr, hn⟩)⟩
  | _ => none

def alignPart? (N : Nat) (xs : List SExp) : Option {a : Fin (2 ^ 32) //
    (xs = [] ∧ a.val = Nat.log2 N) ∨ ∃ t r m, xs = [K t] ∧
      t.toList = "align=".toList ++ r ∧ UN 64 r m ∧ m = 2 ^ a.val} := do
  match hx : xs with
  | [] =>
      if h : Nat.log2 N < 2 ^ 32 then
        some ⟨⟨Nat.log2 N, h⟩, .inl ⟨hx, rfl⟩⟩
      else none
  | [x] =>
      let m ← attribute? "align=" x
      let n := Nat.log2 m.1.val
      if h : n < 2 ^ 32 ∧ m.1.val = 2 ^ n then
        some ⟨⟨n, h.1⟩, .inr (by
          obtain ⟨t, r, ht, hr, hn⟩ := m.2
          exact ⟨t, r, m.1.val, by simpa [ht] using hx, hr, hn, h.2⟩)⟩
      else none
  | _ => none

structure MemHead (N : Nat) (xs : List SExp) where
  consumed : List SExp
  rest : List SExp
  argument : MemArg
  split : xs = consumed ++ rest
  sound : MemArgT N consumed argument

def memArg? (N : Nat) (xs : List SExp) : Option (MemHead N xs) := do
  let (ox, rest) := takeAttribute "offset=" xs
  let (ax, tail) := takeAttribute "align=" rest
  let o ← offsetPart? ox
  let a ← alignPart? N ax
  if hs : xs = ox ++ ax ++ tail then
    some ⟨ox ++ ax, tail, ⟨a.1, o.1⟩, by simpa [List.append_assoc] using hs,
      ⟨ox, ax, rfl, o.2, a.2⟩⟩
  else none

structure OptionalIndex (k : IndexKind) (names : List (Option String)) (xs : List SExp) where
  consumed : List SExp
  rest : List SExp
  index : Wasm.Idx k
  split : xs = consumed ++ rest
  sound : OptIdx names consumed index

def optionalIndex? {k : IndexKind} (names : List (Option String)) (xs : List SExp) :
    OptionalIndex k names xs :=
  match xs with
  | x :: rest =>
      match index? names x with
      | some i => ⟨[x], rest, i.1, rfl, .inr ⟨x, rfl, i.2⟩⟩
      | none => ⟨[], x :: rest, ⟨0⟩, rfl, .inl ⟨rfl, rfl⟩⟩
  | [] => ⟨[], [], ⟨0⟩, rfl, .inl ⟨rfl, rfl⟩⟩

structure PlainHead (I : IdCtx) (xs : List SExp) where
  consumed : List SExp
  rest : List SExp
  instruction : Instr
  split : xs = consumed ++ rest
  sound : Plain I consumed instruction []

def unaryIndex? {k : IndexKind} (I : IdCtx) (name : String)
    (names : List (Option String)) (ctor : Wasm.Idx k → Instr)
    (prove : ∀ {x i}, Text.Idx names x i → Plain I [.atom (.sym name), x] (ctor i) [])
    (x : SExp) (rest : List SExp) : Option (PlainHead I (.atom (.sym name) :: x :: rest)) := do
  let i ← index? names x
  pure ⟨[.atom (.sym name), x], rest, ctor i.1, rfl, prove i.2⟩

def binaryIndex? {k l : IndexKind} (I : IdCtx) (name : String)
    (left right : List (Option String)) (ctor : Wasm.Idx k → Wasm.Idx l → Instr)
    (prove : ∀ {x y i j}, Text.Idx left x i → Text.Idx right y j →
      Plain I [K name, x, y] (ctor i j) [])
    (x y : SExp) (rest : List SExp) : Option (PlainHead I (K name :: x :: y :: rest)) := do
  let i ← index? left x
  let j ← index? right y
  pure ⟨[K name, x, y], rest, ctor i.1 j.1, rfl, prove i.2 j.2⟩

def structAccess? (I : IdCtx) (name : String) (ctor : TypeIdx → FieldIdx → Instr)
    (prove : ∀ {x y t f}, Text.Idx I.types x t → FieldIdxT I t y f →
      Plain I [K name, x, y] (ctor t f) [])
    (x y : SExp) (rest : List SExp) : Option (PlainHead I (K name :: x :: y :: rest)) := do
  let t ← index? I.types x
  let f ← index? ((I.fields[t.1.toNat]?).getD []) y
  pure ⟨[K name, x, y], rest, ctor t.1 f.1, rfl, prove t.2 f.2⟩

def concat? {α : Type} {R : SExp → List α → Prop}
    (f : (x : SExp) → Option {as : List α // R x as}) (xs : List SExp) :
    Option {as : List α // Concat R xs as} := do
  let ass ← mapCertified f xs
  if h : ass.1.flatten.length < 2 ^ 32 then
    some ⟨ass.1.flatten, ⟨ass.1, ass.2, rfl, h⟩⟩
  else none

def namedValues? (I : IdCtx) (keyword : String) (x : SExp) :
    Option (List (ValType × Option String)) := do
  let items ← toList? x
  match items with
  | [.atom (.sym name), .atom (.id id), tx] =>
      if name = keyword then do
        let t ← value? I tx
        pure [(t.1, some id)]
      else none
  | .atom (.sym name) :: txs =>
      if name = keyword then do
        let ts ← mapCertified (value? I) txs
        pure (ts.1.map (·, none))
      else none
  | _ => none

def param? (I : IdCtx) (x : SExp) :
    Option {ps : List (ValType × Option String) // ParamT I x ps} := do
  let items ← list? x
  match hi : items.1 with
  | [.atom (.sym "param"), .atom (.id name), tx] =>
      let t ← value? I tx
      pure ⟨[(t.1, some name)], .inl ⟨name, tx, t.1, by rw [items.2, hi], t.2, rfl⟩⟩
  | .atom (.sym "param") :: txs =>
      let ts ← mapCertified (value? I) txs
      pure ⟨ts.1.map (·, none), .inr ⟨txs, ts.1, by rw [items.2, hi], ts.2, rfl⟩⟩
  | _ => none

def local? (I : IdCtx) (x : SExp) :
    Option {ls : List (ValType × Option String) // LocalT I x ls} := do
  let items ← list? x
  match hi : items.1 with
  | [.atom (.sym "local"), .atom (.id name), tx] =>
      let t ← value? I tx
      pure ⟨[(t.1, some name)], .inl ⟨name, tx, t.1, by rw [items.2, hi], t.2, rfl⟩⟩
  | .atom (.sym "local") :: txs =>
      let ts ← mapCertified (value? I) txs
      pure ⟨ts.1.map (·, none), .inr ⟨txs, ts.1, by rw [items.2, hi], ts.2, rfl⟩⟩
  | _ => none

def result? (I : IdCtx) (x : SExp) :
    Option {ts : List ValType // ResultT I x ts} := do
  let items ← list? x
  match hi : items.1 with
  | .atom (.sym "result") :: txs =>
      let ts ← mapCertified (value? I) txs
      pure ⟨ts.1, ⟨txs, by rw [items.2, hi], ts.2⟩⟩
  | _ => none

def idSyntax : Option String → List SExp
  | none => []
  | some n => [.atom (.id n)]

theorem idSyntax_sound (n : Option String) : IdOpt (idSyntax n) n := by
  cases n with
  | none => exact .inl ⟨rfl, rfl⟩
  | some n => exact .inr ⟨n, rfl, rfl⟩

def stripId : List SExp → Option String × List SExp
  | .atom (.id n) :: rest => (some n, rest)
  | rest => (none, rest)

def headed (keyword : String) (x : SExp) : Bool :=
  match toList? x with
  | some (.atom (.sym s) :: _) => s == keyword
  | _ => false

structure Header where
  name : Option String
  exports : List SExp
  type : Option SExp
  params : List SExp
  results : List SExp
  locals : List SExp
  body : List SExp

def header? (keyword : String) (x : SExp) : Option Header := do
  let .atom (.sym kind) :: rest ← toList? x | none
  if kind ≠ keyword then none else do
    let (name, rest) := stripId rest
    let exports := rest.takeWhile (headed "export")
    let rest := rest.drop exports.length
    let (type, rest) := match rest with
      | x :: xs => if headed "type" x then (some x, xs) else (none, rest)
      | [] => (none, [])
    let params := rest.takeWhile (headed "param")
    let rest := rest.drop params.length
    let results := rest.takeWhile (headed "result")
    let rest := rest.drop results.length
    let locals := rest.takeWhile (headed "local")
    pure ⟨name, exports, type, params, results, locals, rest.drop locals.length⟩

def Header.typeSyntax (h : Header) : List SExp := h.type.toList ++ h.params ++ h.results

def exports? (xs : List SExp) : Option {ns : List String // ExportsT xs ns} :=
  mapCertified (fun x => do
    let items ← list? x
    match hi : items.1 with
    | [.atom (.sym "export"), .atom (.str bytes)] =>
        let name ← Unicode.utf8? bytes
        if hn : Unicode.utf8? bytes = some name then
          some ⟨name, ⟨.atom (.str bytes), by rw [items.2, hi], ⟨bytes, rfl, hn⟩⟩⟩
        else none
    | _ => none) xs

structure TypeUse (I : IdCtx) (xs : List SExp) where
  index : TypeIdx
  parameters : List (Option String)
  uses : List FuncType
  sound : TypeUseT I xs index parameters uses

def ensure (p : Prop) [Decidable p] : Option (PLift p) :=
  if h : p then some ⟨h⟩ else none

def typeUse? (I : IdCtx) (h : Header) : Option (TypeUse I h.typeSyntax) := do
  let ps ← concat? (param? I) h.params
  let rs ← concat? (result? I) h.results
  match ht : h.type with
  | some tx =>
      let items ← list? tx
      let [.atom (.sym "type"), x] := items.1 | none
      let hs ← ensure (tx = L [.atom (.sym "type"), x])
      let i ← index? I.types x
      let ft ← functionType? I i.1
      if hft : functionType? I i.1 = some ft then
        if hempty : ps.1 = [] ∧ rs.1 = [] then
          pure ⟨i.1, List.replicate ft.params.length none, [], by
            refine .inl ⟨x, h.params, h.results, ft, ?_, ?_, ?_, i.2,
              functionType?_sound hft, rfl, rfl⟩
            · simp [Header.typeSyntax, ht, hs.down]
            · simpa [hempty.1] using ps.2
            · simpa [hempty.2] using rs.2⟩
        else if heq : ft = ⟨ps.1.map Prod.fst, rs.1⟩ then
          if hok : ({ locals := ps.1.map Prod.snd } : IdCtx).Ok then
            pure ⟨i.1, ps.1.map Prod.snd, [], by
              refine .inr (.inl ⟨x, h.params, h.results, ft, ps.1, rs.1, ?_, i.2,
                functionType?_sound hft, ps.2, rs.2, heq, rfl, hok, rfl⟩)
              simp [Header.typeSyntax, ht, hs.down]⟩
          else none
        else none
      else none
  | none =>
      let ft : FuncType := ⟨ps.1.map Prod.fst, rs.1⟩
      let n ← I.typedefs.findIdx? (· == some (funcRec ft, 0))
      let i ← Wasm.Idx.ofNat? n
      if hmatch : I.typedefs[i.toNat]? = some (some (funcRec ft, 0)) then
        if hfirst : ∀ j : Fin i.toNat,
            I.typedefs[j.val]? ≠ some (some (funcRec ft, 0)) then
          if hok : ({ locals := ps.1.map Prod.snd } : IdCtx).Ok then
            pure ⟨i, ps.1.map Prod.snd, [ft], by
              refine .inr (.inr ⟨h.params, h.results, ps.1, rs.1, ?_, ps.2, rs.2,
                hmatch, (fun j hj => hfirst ⟨j, hj⟩), rfl, hok, rfl⟩)
              simp [Header.typeSyntax, ht]⟩
          else none
        else none
      else none

/-- Greedily discover an index prefix. Each original index token is certified
independently; folded operands and following instruction keywords remain. -/
structure IndexPrefix (k : IndexKind) (names : List (Option String)) (xs : List SExp) where
  consumed : List SExp
  rest : List SExp
  indices : List (Wasm.Idx k)
  split : xs = consumed ++ rest
  sound : List.Forall₂ (Text.Idx names) consumed indices

def indexPrefix? {k : IndexKind} (names : List (Option String)) :
    (xs : List SExp) → IndexPrefix k names xs
  | [] => ⟨[], [], [], rfl, .nil⟩
  | x :: xs =>
      match index? names x with
      | none => ⟨[], x :: xs, [], rfl, .nil⟩
      | some i =>
          let tail := indexPrefix? names xs
          ⟨x :: tail.consumed, tail.rest, i.1 :: tail.indices,
            congrArg (x :: ·) tail.split, .cons i.2 tail.sound⟩

def indirectCall? (I : IdCtx) (name : String) (ctor : TableIdx → TypeIdx → Instr)
    (prove : ∀ {tx tu tb t locals}, OptIdx I.tables tx tb → TypeUseT I tu t locals [] →
      (∀ l ∈ locals, l = none) → Plain I (K name :: (tx ++ tu)) (ctor tb t) [])
    (rest : List SExp) : Option (PlainHead I (K name :: rest)) := do
  let table := optionalIndex? I.tables rest
  let h ← header? name (L (K name :: table.rest))
  let tu ← typeUse? I h
  let hu ← ensure (tu.uses = [])
  let hn ← ensure (∀ l ∈ tu.parameters, l = none)
  if hs : K name :: rest = (K name :: (table.consumed ++ h.typeSyntax)) ++ h.body then
    some ⟨K name :: (table.consumed ++ h.typeSyntax), h.body,
      ctor table.index tu.index, hs, prove table.sound (by simpa [hu.down] using tu.sound) hn.down⟩
  else none

def tableUnary? (I : IdCtx) (name : String) (ctor : TableIdx → Instr)
    (prove : ∀ {tx t}, OptIdx I.tables tx t → Plain I (K name :: tx) (ctor t) [])
    (rest : List SExp) : PlainHead I (K name :: rest) :=
  let table := optionalIndex? I.tables rest
  ⟨K name :: table.consumed, table.rest, ctor table.index,
    congrArg (K name :: ·) table.split, prove table.sound⟩

/-- Each vector lane is checked in its original integer/float literal grammar;
only the fixed number selected by the shape is consumed. -/
def vectorConstant? (I : IdCtx) (shape : String) (width count : Nat)
    {R : SExp → BitVec width → Prop}
    (parse : (x : SExp) → Option {v : BitVec width // R x v})
    (prove : ∀ {xs vs}, List.Forall₂ R xs vs → vs.length = count →
      V128ConstT (K shape :: xs) (lanesToBits width (vs.map BitVec.toNat)))
    (rest : List SExp) : Option (PlainHead I (K "v128.const" :: K shape :: rest)) := do
  let xs := rest.take count
  let vs ← mapCertified parse xs
  let hl ← ensure (vs.1.length = count)
  if hs : K "v128.const" :: K shape :: rest =
      (K "v128.const" :: K shape :: xs) ++ rest.drop count then
    some ⟨K "v128.const" :: K shape :: xs, rest.drop count,
      .vecConst (lanesToBits width (vs.1.map BitVec.toNat)), hs, .v128Const (prove vs.2 hl.down)⟩
  else none

/-- Parse exactly the leading plain instruction; folded operands are left in
`rest`, so the formal folded rule determines their evaluation order. -/
def plain? (I : IdCtx) : (xs : List SExp) → Option (PlainHead I xs)
  | .atom (.sym "i32.const") :: x :: rest => do
      let b ← integer? 32 x
      pure ⟨[.atom (.sym "i32.const"), x], rest, .intConst .i32 b.1, rfl, .i32Const b.2⟩
  | .atom (.sym "i64.const") :: x :: rest => do
      let b ← integer? 64 x
      pure ⟨[.atom (.sym "i64.const"), x], rest, .intConst .i64 b.1, rfl, .i64Const b.2⟩
  | .atom (.sym "f32.const") :: x :: rest => do
      let b ← float? .f32 x
      pure ⟨[.atom (.sym "f32.const"), x], rest, .floatConst .f32 b.1, rfl, .f32Const b.2⟩
  | .atom (.sym "f64.const") :: x :: rest => do
      let b ← float? .f64 x
      pure ⟨[.atom (.sym "f64.const"), x], rest, .floatConst .f64 b.1, rfl, .f64Const b.2⟩
  | .atom (.sym "v128.const") :: .atom (.sym "i8x16") :: rest =>
      vectorConstant? I "i8x16" 8 16 (integer? 8)
        (fun h hl => .inl ⟨_, _, rfl, h, hl, rfl⟩) rest
  | .atom (.sym "v128.const") :: .atom (.sym "i16x8") :: rest =>
      vectorConstant? I "i16x8" 16 8 (integer? 16)
        (fun h hl => .inr (.inl ⟨_, _, rfl, h, hl, rfl⟩)) rest
  | .atom (.sym "v128.const") :: .atom (.sym "i32x4") :: rest =>
      vectorConstant? I "i32x4" 32 4 (integer? 32)
        (fun h hl => .inr (.inr (.inl ⟨_, _, rfl, h, hl, rfl⟩))) rest
  | .atom (.sym "v128.const") :: .atom (.sym "i64x2") :: rest =>
      vectorConstant? I "i64x2" 64 2 (integer? 64)
        (fun h hl => .inr (.inr (.inr (.inl ⟨_, _, rfl, h, hl, rfl⟩)))) rest
  | .atom (.sym "v128.const") :: .atom (.sym "f32x4") :: rest =>
      vectorConstant? I "f32x4" 32 4 (float? .f32)
        (fun h hl => .inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, h, hl, rfl⟩))))) rest
  | .atom (.sym "v128.const") :: .atom (.sym "f64x2") :: rest =>
      vectorConstant? I "f64x2" 64 2 (float? .f64)
        (fun h hl => .inr (.inr (.inr (.inr (.inr (⟨_, _, rfl, h, hl, rfl⟩)))))) rest
  | .atom (.sym "i8x16.shuffle") :: rest => do
      let xs := rest.take 16
      let lanes ← mapCertified (unsigned? 8) xs
      let hl ← ensure (lanes.1.length = 16)
      if hs : K "i8x16.shuffle" :: rest = (K "i8x16.shuffle" :: xs) ++ rest.drop 16 then
        some ⟨K "i8x16.shuffle" :: xs, rest.drop 16, .vecShuffle lanes.1,
          hs, .shuffle lanes.2 hl.down⟩
      else none
  | .atom (.sym "local.get") :: x :: rest => unaryIndex? I _ I.locals .localGet Plain.localGet x rest
  | .atom (.sym "local.set") :: x :: rest => unaryIndex? I _ I.locals .localSet Plain.localSet x rest
  | .atom (.sym "local.tee") :: x :: rest => unaryIndex? I _ I.locals .localTee Plain.localTee x rest
  | .atom (.sym "global.get") :: x :: rest => unaryIndex? I _ I.globals .globalGet Plain.globalGet x rest
  | .atom (.sym "global.set") :: x :: rest => unaryIndex? I _ I.globals .globalSet Plain.globalSet x rest
  | .atom (.sym "call") :: x :: rest => unaryIndex? I _ I.funcs .call Plain.call x rest
  | .atom (.sym "return_call") :: x :: rest => unaryIndex? I _ I.funcs .returnCall Plain.returnCall x rest
  | .atom (.sym "call_ref") :: x :: rest => unaryIndex? I _ I.types .callRef Plain.callRef x rest
  | .atom (.sym "return_call_ref") :: x :: rest => unaryIndex? I _ I.types .returnCallRef Plain.returnCallRef x rest
  | .atom (.sym "br") :: x :: rest => unaryIndex? I _ I.labels .br Plain.br x rest
  | .atom (.sym "br_if") :: x :: rest => unaryIndex? I _ I.labels .brIf Plain.brIf x rest
  | .atom (.sym "br_on_null") :: x :: rest => unaryIndex? I _ I.labels .brOnNull Plain.brOnNull x rest
  | .atom (.sym "br_on_non_null") :: x :: rest => unaryIndex? I _ I.labels .brOnNonNull Plain.brOnNonNull x rest
  | .atom (.sym "br_table") :: rest => do
      let labels := indexPrefix? (k := .label) I.labels rest
      let last ← labels.indices.getLast?
      let targets := labels.indices.dropLast
      if h : targets ++ [last] = labels.indices ∧ labels.indices.length < 2 ^ 32 then
        some ⟨K "br_table" :: labels.consumed, labels.rest, .brTable targets last,
          congrArg (K "br_table" :: ·) labels.split,
          .brTable (by simpa [h.1] using labels.sound) (by simpa [h.1] using h.2)⟩
      else none
  | .atom (.sym "br_on_cast") :: x :: source :: target :: rest => do
      let l ← index? I.labels x
      let a ← reference? I source
      let b ← reference? I target
      pure ⟨[K "br_on_cast", x, source, target], rest, .brOnCast l.1 a.1 b.1, rfl,
        .brOnCast l.2 a.2 b.2⟩
  | .atom (.sym "br_on_cast_fail") :: x :: source :: target :: rest => do
      let l ← index? I.labels x
      let a ← reference? I source
      let b ← reference? I target
      pure ⟨[K "br_on_cast_fail", x, source, target], rest, .brOnCastFail l.1 a.1 b.1, rfl,
        .brOnCastFail l.2 a.2 b.2⟩
  | .atom (.sym "call_indirect") :: rest => indirectCall? I _ .callIndirect Plain.callIndirect rest
  | .atom (.sym "return_call_indirect") :: rest => indirectCall? I _ .returnCallIndirect Plain.returnCallIndirect rest
  | .atom (.sym "throw") :: x :: rest => unaryIndex? I _ I.tags .throw Plain.throw x rest
  | .atom (.sym "table.get") :: rest => some (tableUnary? I _ .tableGet Plain.tableGet rest)
  | .atom (.sym "table.set") :: rest => some (tableUnary? I _ .tableSet Plain.tableSet rest)
  | .atom (.sym "table.size") :: rest => some (tableUnary? I _ .tableSize Plain.tableSize rest)
  | .atom (.sym "table.grow") :: rest => some (tableUnary? I _ .tableGrow Plain.tableGrow rest)
  | .atom (.sym "table.fill") :: rest => some (tableUnary? I _ .tableFill Plain.tableFill rest)
  | .atom (.sym "elem.drop") :: x :: rest => unaryIndex? I _ I.elems .elemDrop Plain.elemDrop x rest
  | .atom (.sym "table.copy") :: rest =>
      match rest with
      | x :: y :: tail =>
          match index? I.tables x, index? I.tables y with
          | some a, some b => some ⟨[K "table.copy", x, y], tail,
              .tableCopy a.1 b.1, rfl, .tableCopy a.2 b.2⟩
          | _, _ => some ⟨[K "table.copy"], x :: y :: tail, .tableCopy ⟨0⟩ ⟨0⟩, rfl, .tableCopy0⟩
      | tail => some ⟨[K "table.copy"], tail, .tableCopy ⟨0⟩ ⟨0⟩, rfl, .tableCopy0⟩
  | .atom (.sym "table.init") :: x :: rest =>
      match rest with
      | y :: tail =>
          match index? I.tables x, index? I.elems y with
          | some a, some b => some ⟨[K "table.init", x, y], tail,
              .tableInit a.1 b.1, rfl, .tableInit (.inr ⟨x, rfl, a.2⟩) b.2⟩
          | _, _ => do
              let e ← index? I.elems x
              pure ⟨[K "table.init", x], y :: tail, .tableInit ⟨0⟩ e.1, rfl,
                .tableInit (.inl ⟨rfl, rfl⟩) e.2⟩
      | [] => do
          let e ← index? I.elems x
          pure ⟨[K "table.init", x], [], .tableInit ⟨0⟩ e.1, rfl,
            .tableInit (.inl ⟨rfl, rfl⟩) e.2⟩
  | .atom (.sym "ref.func") :: x :: rest => unaryIndex? I _ I.funcs .refFunc Plain.refFunc x rest
  | .atom (.sym "ref.null") :: x :: rest => do
      let h ← heap? I x
      pure ⟨[K "ref.null", x], rest, .refNull h.1, rfl, .refNull h.2⟩
  | .atom (.sym "ref.test") :: x :: rest => do
      let r ← reference? I x
      pure ⟨[K "ref.test", x], rest, .refTest r.1, rfl, .refTest r.2⟩
  | .atom (.sym "ref.cast") :: x :: rest => do
      let r ← reference? I x
      pure ⟨[K "ref.cast", x], rest, .refCast r.1, rfl, .refCast r.2⟩
  | .atom (.sym "memory.size") :: rest =>
      let m := optionalIndex? I.mems rest
      some ⟨K "memory.size" :: m.consumed, m.rest, .memorySize m.index,
        congrArg (K "memory.size" :: ·) m.split, .memorySize m.sound⟩
  | .atom (.sym "memory.grow") :: rest =>
      let m := optionalIndex? I.mems rest
      some ⟨K "memory.grow" :: m.consumed, m.rest, .memoryGrow m.index,
        congrArg (K "memory.grow" :: ·) m.split, .memoryGrow m.sound⟩
  | .atom (.sym "memory.fill") :: rest =>
      let m := optionalIndex? I.mems rest
      some ⟨K "memory.fill" :: m.consumed, m.rest, .memoryFill m.index,
        congrArg (K "memory.fill" :: ·) m.split, .memoryFill m.sound⟩
  | .atom (.sym "data.drop") :: x :: rest => unaryIndex? I _ I.datas .dataDrop Plain.dataDrop x rest
  | .atom (.sym "memory.copy") :: rest =>
      match rest with
      | x :: y :: tail =>
          match index? I.mems x, index? I.mems y with
          | some m, some n => some ⟨[K "memory.copy", x, y], tail,
              .memoryCopy m.1 n.1, rfl, .memoryCopy m.2 n.2⟩
          | _, _ => some ⟨[K "memory.copy"], x :: y :: tail, .memoryCopy ⟨0⟩ ⟨0⟩, rfl, .memoryCopy0⟩
      | tail => some ⟨[K "memory.copy"], tail, .memoryCopy ⟨0⟩ ⟨0⟩, rfl, .memoryCopy0⟩
  | .atom (.sym "memory.init") :: x :: rest =>
      match rest with
      | y :: tail =>
          match index? I.mems x, index? I.datas y with
          | some m, some d => some ⟨[K "memory.init", x, y], tail,
              .memoryInit m.1 d.1, rfl, .memoryInit (.inr ⟨x, rfl, m.2⟩) d.2⟩
          | _, _ => do
              let d ← index? I.datas x
              pure ⟨[K "memory.init", x], y :: tail, .memoryInit ⟨0⟩ d.1, rfl,
                .memoryInit (.inl ⟨rfl, rfl⟩) d.2⟩
      | [] => do
          let d ← index? I.datas x
          pure ⟨[K "memory.init", x], [], .memoryInit ⟨0⟩ d.1, rfl,
            .memoryInit (.inl ⟨rfl, rfl⟩) d.2⟩
  | .atom (.sym "struct.new") :: x :: rest => unaryIndex? I _ I.types .structNew Plain.structNew x rest
  | .atom (.sym "struct.new_default") :: x :: rest => unaryIndex? I _ I.types .structNewDefault Plain.structNewDefault x rest
  | .atom (.sym "array.new") :: x :: rest => unaryIndex? I _ I.types .arrayNew Plain.arrayNew x rest
  | .atom (.sym "array.new_default") :: x :: rest => unaryIndex? I _ I.types .arrayNewDefault Plain.arrayNewDefault x rest
  | .atom (.sym "array.get") :: x :: rest => unaryIndex? I _ I.types (.arrayGet none) Plain.arrayGet x rest
  | .atom (.sym "array.get_s") :: x :: rest => unaryIndex? I _ I.types (.arrayGet (some .signed)) Plain.arrayGetS x rest
  | .atom (.sym "array.get_u") :: x :: rest => unaryIndex? I _ I.types (.arrayGet (some .unsigned)) Plain.arrayGetU x rest
  | .atom (.sym "array.set") :: x :: rest => unaryIndex? I _ I.types .arraySet Plain.arraySet x rest
  | .atom (.sym "array.fill") :: x :: rest => unaryIndex? I _ I.types .arrayFill Plain.arrayFill x rest
  | .atom (.sym "struct.get") :: x :: y :: rest => structAccess? I _ (.structGet none) Plain.structGet x y rest
  | .atom (.sym "struct.get_s") :: x :: y :: rest => structAccess? I _ (.structGet (some .signed)) Plain.structGetS x y rest
  | .atom (.sym "struct.get_u") :: x :: y :: rest => structAccess? I _ (.structGet (some .unsigned)) Plain.structGetU x y rest
  | .atom (.sym "struct.set") :: x :: y :: rest => structAccess? I _ .structSet Plain.structSet x y rest
  | .atom (.sym "array.new_data") :: x :: y :: rest => binaryIndex? I _ I.types I.datas .arrayNewData Plain.arrayNewData x y rest
  | .atom (.sym "array.new_elem") :: x :: y :: rest => binaryIndex? I _ I.types I.elems .arrayNewElem Plain.arrayNewElem x y rest
  | .atom (.sym "array.copy") :: x :: y :: rest => binaryIndex? I _ I.types I.types .arrayCopy Plain.arrayCopy x y rest
  | .atom (.sym "array.init_data") :: x :: y :: rest => binaryIndex? I _ I.types I.datas .arrayInitData Plain.arrayInitData x y rest
  | .atom (.sym "array.init_elem") :: x :: y :: rest => binaryIndex? I _ I.types I.elems .arrayInitElem Plain.arrayInitElem x y rest
  | .atom (.sym "array.new_fixed") :: x :: count :: rest => do
      let t ← index? I.types x
      let n ← unsigned? 32 count
      pure ⟨[K "array.new_fixed", x, count], rest, .arrayNewFixed t.1 n.1, rfl,
        .arrayNewFixed t.2 n.2⟩
  | .atom (.sym "select") :: rest => do
      let rxs := rest.takeWhile (headed "result")
      if hr : rxs = [] then
        some ⟨[K "select"], rest, .select none, rfl, .select⟩
      else do
        let ts ← concat? (result? I) rxs
        if hs : K "select" :: rest = (K "select" :: rxs) ++ rest.drop rxs.length then
          some ⟨K "select" :: rxs, rest.drop rxs.length, .select (some ts.1), hs,
            .selectTyped hr ts.2⟩
        else none
  | .atom (.sym name) :: rest =>
      match he : Text.Core.memOps.find? (fun entry => entry.1 == name) with
      | some entry => do
          let m := optionalIndex? I.mems rest
          let a ← memArg? entry.2.1 m.rest
          pure ⟨K name :: (m.consumed ++ a.consumed), a.rest,
            entry.2.2 m.index a.argument, by
              have hr := m.split.trans (congrArg (m.consumed ++ ·) a.split)
              simpa [List.append_assoc] using congrArg (K name :: ·) hr,
            by
              have hm := List.mem_of_find?_eq_some he
              have hn := List.find?_some he
              have hn : entry.1 = name := by simpa using hn
              simpa [hn] using Plain.memOp hm m.sound a.sound⟩
      | none =>
          match he : Text.Core.laneMemOps.find? (fun entry => entry.1 == name) with
          | some entry =>
              let parse (m : OptionalIndex .memory I.mems rest) :
                  Option (PlainHead I (K name :: rest)) := do
                let a ← memArg? entry.2.1 m.rest
                let lx :: tail := a.rest | none
                let lane ← unsigned? 8 lx
                if hs : K name :: rest = (K name :: (m.consumed ++ a.consumed ++ [lx])) ++ tail then
                  some ⟨K name :: (m.consumed ++ a.consumed ++ [lx]), tail,
                    entry.2.2 m.index a.argument lane.1, hs, by
                      have hm := List.mem_of_find?_eq_some he
                      have hn := List.find?_some he
                      have hn : entry.1 = name := by simpa using hn
                      simpa [hn] using Plain.laneMemOp hm m.sound a.sound lane.2⟩
                else none
              (parse (optionalIndex? I.mems rest)).orElse fun _ =>
                parse ⟨[], rest, ⟨0⟩, rfl, .inl ⟨rfl, rfl⟩⟩
          | none =>
              match he : Text.Core.laneOps.find? (fun entry => entry.1 == name) with
              | some entry => do
                  let lx :: tail := rest | none
                  let lane ← unsigned? 8 lx
                  if hs : K name :: rest = [K name, lx] ++ tail then
                    some ⟨[K name, lx], tail, entry.2 lane.1, hs, by
                      have hm := List.mem_of_find?_eq_some he
                      have hn := List.find?_some he
                      have hn : entry.1 = name := by simpa using hn
                      simpa [hn] using Plain.lane hm lane.2⟩
                  else none
              | none => do
                  let i ← Text.Core.NullaryDecode.decode name
                  if h : Text.Core.nullaryName i = some name then
                    some ⟨[K name], rest, i, rfl, .nullary h⟩
                  else none
  | _ => none

def label? (I : IdCtx) : (name : Option String) →
    Option {I' : IdCtx // LabelT I (idSyntax name) name I'}
  | none => pure ⟨{ I with labels := none :: I.labels }, .inl ⟨rfl, rfl, rfl⟩⟩
  | some n => do
      if hn : some n ∉ I.labels then
        some ⟨{ I with labels := some n :: I.labels }, .inr (.inl ⟨n, rfl, rfl, hn, rfl⟩)⟩
      else do
        let j ← I.labels.findIdx? (· == some n)
        if hj : I.labels[j]? = some (some n) then
          some ⟨{ I with labels := some n :: I.labels.set j none },
            .inr (.inr ⟨n, j, rfl, rfl, hj, rfl⟩)⟩
        else none

def blockSignature? (I : IdCtx) (h : Header) :
    Option {bt : BlockType // BlockTypeT I h.typeSyntax bt []} := do
  let ps ← concat? (param? I) h.params
  let rs ← concat? (result? I) h.results
  if ht : h.type = none then
    if hp : ps.1 = [] then
      let hv : ValueFormT I h.typeSyntax rs.1 :=
        ⟨h.params, h.results, by simp [Header.typeSyntax, ht], by simpa [hp] using ps.2, rs.2⟩
      match hr : rs.1 with
      | [] => pure ⟨.empty, .inl ⟨[], by simpa [hr] using hv, rfl, rfl, rfl⟩⟩
      | [t] => pure ⟨.value t, .inr (.inl ⟨[t], t, by simpa [hr] using hv, rfl, rfl, rfl⟩)⟩
      | _ => none
    else none
  else do
    let tx ← h.type
    let [.atom (.sym "type"), ix] ← toList? tx | none
    let hx ← ensure (tx = L [K "type", ix])
    let ht ← ensure (h.type = some tx)
    let tu ← typeUse? I h
    let hu ← ensure (tu.uses = [])
    if hl : ∀ p ∈ tu.parameters, p = none then
      some ⟨.typeIdx tu.index, .inr (.inr ⟨tu.index, tu.parameters,
        by simpa [hu.down] using tu.sound, hl, rfl, by
          intro ⟨ts, hv, _⟩
          have hv' : ValueFormT I (L [K "type", ix] :: (h.params ++ h.results)) ts := by
            simpa [Header.typeSyntax, ht.down, hx.down] using hv
          exact not_valueFormT_kw (by decide) (by decide) hv'⟩)⟩
    else none

theorem expr_transport {I : IdCtx} {xs ys : List SExp} {e : Expr}
    (h : xs = ys) (he : ExprT I ys e []) : ExprT I xs e [] := h ▸ he

theorem folded_transport {I : IdCtx} {x y : SExp} {e : Expr}
    (h : x = y) (he : Folded I y e []) : Folded I x e [] := h ▸ he

/-- Candidate delimiter discovery; source equality and BlockInstr constructors
independently check every accepted split. Folded subtrees are opaque here. -/
def splitControl (stopElse : Bool) (depth : Nat) : List SExp → List SExp × List SExp
  | [] => ([], [])
  | x :: xs =>
      let stop := match x with
        | .atom (.sym "end") => depth == 0
        | .atom (.sym "else") => stopElse && depth == 0
        | _ => false
      if stop then ([], x :: xs) else
        let depth' := match x with
          | .atom (.sym "block") | .atom (.sym "loop") | .atom (.sym "if") |
              .atom (.sym "try_table") => depth + 1
          | .atom (.sym "end") => depth - 1
          | _ => depth
        let (body, tail) := splitControl stopElse depth' xs
        (x :: body, tail)

structure EndName (name : Option String) where
  tokens : List SExp
  rest : List SExp
  sound : EndIdT tokens name

def endName? (name : Option String) (xs : List SExp) : Option (EndName name) :=
  match xs with
  | .atom (.id n) :: tail =>
      if h : name = some n then some ⟨[.atom (.id n)], tail, .inr ⟨n, rfl, h⟩⟩
      else none
  | tail => some ⟨[], tail, .inl rfl⟩

structure ControlHead (I : IdCtx) (xs : List SExp) where
  consumed : List SExp
  rest : List SExp
  instruction : Instr
  split : xs = consumed ++ rest
  sound : BlockInstr I consumed instruction []


def catch? (I : IdCtx) (x : SExp) : Option {c : Catch // CatchT I x c} := do
  let items ← list? x
  match hi : items.1 with
  | [.atom (.sym "catch"), tx, lx] =>
      let t ← index? I.tags tx
      let l ← index? I.labels lx
      pure ⟨.catch_ t.1 l.1, .inl ⟨tx, lx, t.1, l.1, by rw [items.2, hi], t.2, l.2, rfl⟩⟩
  | [.atom (.sym "catch_ref"), tx, lx] =>
      let t ← index? I.tags tx
      let l ← index? I.labels lx
      pure ⟨.catchRef t.1 l.1, .inr (.inl ⟨tx, lx, t.1, l.1, by rw [items.2, hi], t.2, l.2, rfl⟩)⟩
  | [.atom (.sym "catch_all"), lx] =>
      let l ← index? I.labels lx
      pure ⟨.catchAll l.1, .inr (.inr (.inl ⟨lx, l.1, by rw [items.2, hi], l.2, rfl⟩))⟩
  | [.atom (.sym "catch_all_ref"), lx] =>
      let l ← index? I.labels lx
      pure ⟨.catchAllRef l.1, .inr (.inr (.inr ⟨lx, l.1, by rw [items.2, hi], l.2, rfl⟩))⟩
  | _ => none

def isCatch (x : SExp) : Bool :=
  headed "catch" x || headed "catch_ref" x || headed "catch_all" x || headed "catch_all_ref" x


mutual
/-- Source tree fuel bounds flat traversal and nested folded operands. -/
def exprFuel? : Nat → (I : IdCtx) → (xs : List SExp) →
    Option {e : Expr // ExprT I xs e []}
  | 0, _, _ => none
  | _ + 1, _, [] => some ⟨[], .nil⟩
  | fuel + 1, I, x :: xs => do
      match x with
      | .atom _ =>
          let structured := match x with
            | .atom (.sym "block") | .atom (.sym "loop") | .atom (.sym "if") | .atom (.sym "try_table") => true
            | _ => false
          if structured then do
            let p ← controlFuel? fuel I (x :: xs)
            let tail ← exprFuel? fuel I p.rest
            pure ⟨p.instruction :: tail.1,
              expr_transport p.split (by simpa using Instrs.block p.sound tail.2)⟩
          else do
            let p ← plain? I (x :: xs)
            let tail ← exprFuel? fuel I p.rest
            pure ⟨p.instruction :: tail.1,
              expr_transport p.split (by simpa using Instrs.plain p.sound tail.2)⟩
      | _ =>
          let e ← foldedFuel? fuel I x
          let tail ← exprFuel? fuel I xs
          pure ⟨e.1 ++ tail.1, by simpa using Instrs.folded e.2 tail.2⟩

def controlFuel? : Nat → (I : IdCtx) → (xs : List SExp) → Option (ControlHead I xs)
  | 0, _, _ => none
  | fuel + 1, I, xs => do
      let .atom (.sym kind) :: rest := xs | none
      let h ← header? kind (L xs)
      let sig ← blockSignature? I h
      let I' ← label? I h.name
      let cxs := if kind = "try_table" then h.body.takeWhile isCatch else []
      let catches ← mapCertified (catch? I) cxs
      let (body, delim) := splitControl (kind == "if") 0 (h.body.drop cxs.length)
      let b ← exprFuel? fuel I'.1 body
      match _hk : kind, delim with
      | "block", .atom (.sym "end") :: tail =>
          let en ← endName? h.name tail
          let tokens := .atom (.sym "block") :: (idSyntax h.name ++ h.typeSyntax ++ body ++ .atom (.sym "end") :: en.tokens)
          if hs : xs = tokens ++ en.rest then
            some ⟨tokens, en.rest, .block sig.1 b.1, hs, by
              simpa [tokens] using BlockInstr.block I'.2 sig.2 b.2 en.sound⟩
          else none
      | "loop", .atom (.sym "end") :: tail =>
          let en ← endName? h.name tail
          let tokens := .atom (.sym "loop") :: (idSyntax h.name ++ h.typeSyntax ++ body ++ .atom (.sym "end") :: en.tokens)
          if hs : xs = tokens ++ en.rest then
            some ⟨tokens, en.rest, .loop sig.1 b.1, hs, by
              simpa [tokens] using BlockInstr.loop I'.2 sig.2 b.2 en.sound⟩
          else none
      | "if", .atom (.sym "end") :: tail =>
          let en ← endName? h.name tail
          let tokens := .atom (.sym "if") :: (idSyntax h.name ++ h.typeSyntax ++ body ++ .atom (.sym "end") :: en.tokens)
          if hs : xs = tokens ++ en.rest then
            some ⟨tokens, en.rest, .if_ sig.1 b.1 [], hs, by
              simpa [tokens] using BlockInstr.ifNoElse I'.2 sig.2 b.2 en.sound⟩
          else none
      | "if", .atom (.sym "else") :: tail =>
          let el ← endName? h.name tail
          let (elseBody, delim) := splitControl false 0 el.rest
          let .atom (.sym "end") :: tail := delim | none
          let en ← endName? h.name tail
          let e ← exprFuel? fuel I'.1 elseBody
          let tokens := .atom (.sym "if") :: (idSyntax h.name ++ h.typeSyntax ++ body ++
            .atom (.sym "else") :: (el.tokens ++ elseBody ++ .atom (.sym "end") :: en.tokens))
          if hs : xs = tokens ++ en.rest then
            some ⟨tokens, en.rest, .if_ sig.1 b.1 e.1, hs, by
              simpa [tokens] using BlockInstr.if_ I'.2 sig.2 b.2 el.sound e.2 en.sound⟩
          else none
      | "try_table", .atom (.sym "end") :: tail =>
          let en ← endName? h.name tail
          let tokens := K "try_table" :: (idSyntax h.name ++ h.typeSyntax ++ cxs ++ body ++ K "end" :: en.tokens)
          if hs : xs = tokens ++ en.rest then
            some ⟨tokens, en.rest, .tryTable sig.1 catches.1 b.1, hs, by
              simpa [tokens] using BlockInstr.tryTable I'.2 sig.2 catches.2 b.2 en.sound⟩
          else none
      | _, _ => none

def foldedSeqFuel? : Nat → (I : IdCtx) → (xs : List SExp) →
    Option {e : Expr // FoldedSeq I xs e []}
  | 0, _, _ => none
  | _ + 1, _, [] => some ⟨[], .nil⟩
  | fuel + 1, I, x :: xs => do
      let e ← foldedFuel? fuel I x
      let tail ← foldedSeqFuel? fuel I xs
      pure ⟨e.1 ++ tail.1, by simpa using FoldedSeq.cons e.2 tail.2⟩

def foldedFuel? : Nat → (I : IdCtx) → (x : SExp) →
    Option {e : Expr // Folded I x e []}
  | 0, _, _ => none
  | fuel + 1, I, x => do
      let items ← list? x
      match items.1 with
      | .atom (.sym "block") :: _ =>
          let h ← header? "block" x
          let sig ← blockSignature? I h
          let I' ← label? I h.name
          let body ← exprFuel? fuel I'.1 h.body
          if hx : x = L (.atom (.sym "block") :: (idSyntax h.name ++ h.typeSyntax ++ h.body)) then
            some ⟨[.block sig.1 body.1], folded_transport hx (by
              simpa using Folded.block I'.2 sig.2 body.2)⟩
          else none
      | .atom (.sym "loop") :: _ =>
          let h ← header? "loop" x
          let sig ← blockSignature? I h
          let I' ← label? I h.name
          let body ← exprFuel? fuel I'.1 h.body
          if hx : x = L (.atom (.sym "loop") :: (idSyntax h.name ++ h.typeSyntax ++ h.body)) then
            some ⟨[.loop sig.1 body.1], folded_transport hx (by
              simpa using Folded.loop I'.2 sig.2 body.2)⟩
          else none
      | .atom (.sym "try_table") :: _ =>
          let h ← header? "try_table" x
          let sig ← blockSignature? I h
          let I' ← label? I h.name
          let cxs := h.body.takeWhile isCatch
          let catches ← mapCertified (catch? I) cxs
          let body ← exprFuel? fuel I'.1 (h.body.drop cxs.length)
          if hx : x = L (K "try_table" :: (idSyntax h.name ++ h.typeSyntax ++ cxs ++ h.body.drop cxs.length)) then
            some ⟨[.tryTable sig.1 catches.1 body.1], folded_transport hx (by
              simpa using Folded.tryTable I'.2 sig.2 catches.2 body.2)⟩
          else none
      | .atom (.sym "if") :: _ =>
          let h ← header? "if" x
          let sig ← blockSignature? I h
          let I' ← label? I h.name
          let conds := h.body.takeWhile (fun x => !(headed "then" x))
          let c ← foldedSeqFuel? fuel I conds
          match h.body.drop conds.length with
          | [thn] =>
              let .atom (.sym "then") :: yes ← toList? thn | none
              let y ← exprFuel? fuel I'.1 yes
              if hx : x = L (.atom (.sym "if") :: (idSyntax h.name ++ h.typeSyntax ++ conds ++
                  [L (.atom (.sym "then") :: yes)])) then
                some ⟨c.1 ++ [.if_ sig.1 y.1 []], folded_transport hx (by
                  simpa using Folded.ifThen I'.2 sig.2 c.2 y.2)⟩
              else none
          | [thn, els] =>
              let .atom (.sym "then") :: yes ← toList? thn | none
              let .atom (.sym "else") :: no ← toList? els | none
              let y ← exprFuel? fuel I'.1 yes
              let n ← exprFuel? fuel I'.1 no
              if hx : x = L (.atom (.sym "if") :: (idSyntax h.name ++ h.typeSyntax ++ conds ++
                  [L (.atom (.sym "then") :: yes), L (.atom (.sym "else") :: no)])) then
                some ⟨c.1 ++ [.if_ sig.1 y.1 n.1], folded_transport hx (by
                  simpa using Folded.ifThenElse I'.2 sig.2 c.2 y.2 n.2)⟩
              else none
          | _ => none
      | _ =>
          let p ← plain? I items.1
          let operands ← exprFuel? fuel I p.rest
          match hp : p.consumed with
          | .atom (.sym name) :: imms =>
              pure ⟨operands.1 ++ [p.instruction], by
                apply folded_transport (y := L (.atom (.sym name) :: (imms ++ p.rest)))
                · calc
                    x = L items.1 := items.2
                    _ = L (p.consumed ++ p.rest) := congrArg L p.split
                    _ = L (.atom (.sym name) :: (imms ++ p.rest)) := by rw [hp]; rfl
                · simpa using Folded.plain (by simpa [hp] using p.sound) operands.2⟩
          | _ => none
end

def expr? (I : IdCtx) (xs : List SExp) : Option {e : Expr // ExprT I xs e []} :=
  exprFuel? (xs.foldl (fun n x => n + syntaxNodes x + 1) 1) I xs

def func? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let h ← header? "func" x
  let ns ← exports? h.exports
  let tu ← typeUse? I h
  let ls ← concat? (local? I) h.locals
  let I' := I ++ { locals := tu.parameters ++ ls.1.map Prod.snd }
  if hok : I'.Ok then do
    let e ← expr? I' h.body
    if hx : x = L (.atom (.sym "func") :: (idSyntax h.name ++ h.exports ++
        h.typeSyntax ++ h.locals ++ h.body)) then
      some ⟨(.func ⟨tu.index, ls.1.map Prod.fst, e.1⟩ :: selfExports ns.1,
        { funcs := [h.name] }, tu.uses), by
        rw [hx]
        simpa using DeclT.func (idSyntax_sound h.name) ns.2 tu.sound ls.2 hok e.2⟩
    else none
  else none


/-! General source elaboration keeps each implicit function-type contribution
in its grammar-prescribed order. The original no-contribution API remains
available above. -/
namespace WithUses

structure Derived (α : Type) (R : α → List FuncType → Prop) where
  value : α
  uses : List FuncType
  sound : R value uses

structure PlainHead (I : IdCtx) (xs : List SExp) where
  consumed : List SExp
  rest : List SExp
  instruction : Instr
  uses : List FuncType
  split : xs = consumed ++ rest
  sound : Plain I consumed instruction uses

def indirectCall? (I : IdCtx) (name : String) (ctor : TableIdx → TypeIdx → Instr)
    (prove : ∀ {tx tu tb t locals uses}, OptIdx I.tables tx tb →
      TypeUseT I tu t locals uses → (∀ l ∈ locals, l = none) →
      Plain I (K name :: (tx ++ tu)) (ctor tb t) uses)
    (rest : List SExp) : Option (PlainHead I (K name :: rest)) := do
  let table := optionalIndex? I.tables rest
  let h ← header? name (L (K name :: table.rest))
  let tu ← typeUse? I h
  let hn ← ensure (∀ l ∈ tu.parameters, l = none)
  if hs : K name :: rest = (K name :: (table.consumed ++ h.typeSyntax)) ++ h.body then
    some ⟨K name :: (table.consumed ++ h.typeSyntax), h.body,
      ctor table.index tu.index, tu.uses, hs, prove table.sound tu.sound hn.down⟩
  else none

def plain? (I : IdCtx) (xs : List SExp) : Option (PlainHead I xs) :=
  ((Source.plain? I xs).map fun p =>
    ⟨p.consumed, p.rest, p.instruction, [], p.split, p.sound⟩).orElse fun _ =>
      match xs with
      | .atom (.sym "call_indirect") :: rest =>
          indirectCall? I _ .callIndirect Plain.callIndirect rest
      | .atom (.sym "return_call_indirect") :: rest =>
          indirectCall? I _ .returnCallIndirect Plain.returnCallIndirect rest
      | _ => none

def blockSignature? (I : IdCtx) (h : Header) :
    Option (Derived BlockType (BlockTypeT I h.typeSyntax)) :=
  match Source.blockSignature? I h with
  | some bt => some ⟨bt.1, [], bt.2⟩
  | none => do
      let ht ← ensure (h.type = none)
      let hT ← ensure (Distinct I.types)
      let ps ← concat? (param? I) h.params
      let rs ← concat? (result? I) h.results
      let tu ← typeUse? I h
      let hn ← ensure (∀ l ∈ tu.parameters, l = none)
      let notValue : PLift (¬ ∃ ts, ValueFormT I h.typeSyntax ts ∧ ts.length ≤ 1) ←
        if hp : ps.1 = [] then
          if hl : 1 < rs.1.length then
            pure ⟨by
              intro ⟨ts, hv, hlen⟩
              have hv' : ValueFormT I h.typeSyntax rs.1 :=
                ⟨h.params, h.results, by simp [Header.typeSyntax, ht.down],
                  by simpa [hp] using ps.2, rs.2⟩
              have heq := valueFormT_functional hT.down hv' hv
              rw [← heq] at hlen
              omega⟩
          else none
        else
          pure ⟨by
            intro ⟨ts, ⟨pxs, rxs, heq, hp', hr'⟩, _⟩
            have heq' : h.params ++ h.results = pxs ++ rxs := by
              simpa [Header.typeSyntax, ht.down] using heq
            obtain ⟨ep, er⟩ := params_results_split ps.2 rs.2 hp' hr' heq'
            have hempty := concat_functional (R := ParamT I)
              (fun _ _ _ a b => paramT_functional hT.down a b) ps.2 (ep ▸ hp')
            exact hp hempty⟩
      pure ⟨.typeIdx tu.index, tu.uses,
        .inr (.inr ⟨tu.index, tu.parameters, tu.sound, hn.down, rfl, notValue.down⟩)⟩

theorem expr_transport {I : IdCtx} {xs ys : List SExp} {e : Expr} {u : List FuncType}
    (h : xs = ys) (he : ExprT I ys e u) : ExprT I xs e u := h ▸ he

theorem folded_transport {I : IdCtx} {x y : SExp} {e : Expr} {u : List FuncType}
    (h : x = y) (he : Folded I y e u) : Folded I x e u := h ▸ he

structure ControlHead (I : IdCtx) (xs : List SExp) where
  consumed : List SExp
  rest : List SExp
  instruction : Instr
  uses : List FuncType
  split : xs = consumed ++ rest
  sound : BlockInstr I consumed instruction uses

mutual
/-- Source tree fuel bounds flat traversal and nested folded operands. -/
def exprFuel? : Nat → (I : IdCtx) → (xs : List SExp) →
    Option (Derived Expr (ExprT I xs))
  | 0, _, _ => none
  | _ + 1, _, [] => some ⟨[], [], .nil⟩
  | fuel + 1, I, x :: xs => do
      match x with
      | .atom _ =>
          let structured := match x with
            | .atom (.sym "block") | .atom (.sym "loop") | .atom (.sym "if") | .atom (.sym "try_table") => true
            | _ => false
          if structured then do
            let p ← controlFuel? fuel I (x :: xs)
            let tail ← exprFuel? fuel I p.rest
            pure ⟨p.instruction :: tail.value, p.uses ++ tail.uses,
              expr_transport p.split (by simpa using Instrs.block p.sound tail.sound)⟩
          else do
            let p ← plain? I (x :: xs)
            let tail ← exprFuel? fuel I p.rest
            pure ⟨p.instruction :: tail.value, p.uses ++ tail.uses,
              expr_transport p.split (by simpa using Instrs.plain p.sound tail.sound)⟩
      | _ =>
          let e ← foldedFuel? fuel I x
          let tail ← exprFuel? fuel I xs
          pure ⟨e.value ++ tail.value, e.uses ++ tail.uses, by simpa using Instrs.folded e.sound tail.sound⟩

def controlFuel? : Nat → (I : IdCtx) → (xs : List SExp) → Option (ControlHead I xs)
  | 0, _, _ => none
  | fuel + 1, I, xs => do
      let .atom (.sym kind) :: rest := xs | none
      let h ← header? kind (L xs)
      let sig ← blockSignature? I h
      let I' ← label? I h.name
      let cxs := if kind = "try_table" then h.body.takeWhile isCatch else []
      let catches ← mapCertified (catch? I) cxs
      let (body, delim) := splitControl (kind == "if") 0 (h.body.drop cxs.length)
      let b ← exprFuel? fuel I'.1 body
      match _hk : kind, delim with
      | "block", .atom (.sym "end") :: tail =>
          let en ← endName? h.name tail
          let tokens := .atom (.sym "block") :: (idSyntax h.name ++ h.typeSyntax ++ body ++ .atom (.sym "end") :: en.tokens)
          if hs : xs = tokens ++ en.rest then
            some ⟨tokens, en.rest, .block sig.value b.value, sig.uses ++ b.uses, hs, by
              simpa [tokens] using BlockInstr.block I'.2 sig.sound b.sound en.sound⟩
          else none
      | "loop", .atom (.sym "end") :: tail =>
          let en ← endName? h.name tail
          let tokens := .atom (.sym "loop") :: (idSyntax h.name ++ h.typeSyntax ++ body ++ .atom (.sym "end") :: en.tokens)
          if hs : xs = tokens ++ en.rest then
            some ⟨tokens, en.rest, .loop sig.value b.value, sig.uses ++ b.uses, hs, by
              simpa [tokens] using BlockInstr.loop I'.2 sig.sound b.sound en.sound⟩
          else none
      | "if", .atom (.sym "end") :: tail =>
          let en ← endName? h.name tail
          let tokens := .atom (.sym "if") :: (idSyntax h.name ++ h.typeSyntax ++ body ++ .atom (.sym "end") :: en.tokens)
          if hs : xs = tokens ++ en.rest then
            some ⟨tokens, en.rest, .if_ sig.value b.value [], sig.uses ++ b.uses, hs, by
              simpa [tokens] using BlockInstr.ifNoElse I'.2 sig.sound b.sound en.sound⟩
          else none
      | "if", .atom (.sym "else") :: tail =>
          let el ← endName? h.name tail
          let (elseBody, delim) := splitControl false 0 el.rest
          let .atom (.sym "end") :: tail := delim | none
          let en ← endName? h.name tail
          let e ← exprFuel? fuel I'.1 elseBody
          let tokens := .atom (.sym "if") :: (idSyntax h.name ++ h.typeSyntax ++ body ++
            .atom (.sym "else") :: (el.tokens ++ elseBody ++ .atom (.sym "end") :: en.tokens))
          if hs : xs = tokens ++ en.rest then
            some ⟨tokens, en.rest, .if_ sig.value b.value e.value, sig.uses ++ b.uses ++ e.uses, hs, by
              simpa [tokens] using BlockInstr.if_ I'.2 sig.sound b.sound el.sound e.sound en.sound⟩
          else none
      | "try_table", .atom (.sym "end") :: tail =>
          let en ← endName? h.name tail
          let tokens := K "try_table" :: (idSyntax h.name ++ h.typeSyntax ++ cxs ++ body ++ K "end" :: en.tokens)
          if hs : xs = tokens ++ en.rest then
            some ⟨tokens, en.rest, .tryTable sig.value catches.1 b.value, sig.uses ++ b.uses, hs, by
              simpa [tokens] using BlockInstr.tryTable I'.2 sig.sound catches.2 b.sound en.sound⟩
          else none
      | _, _ => none

def foldedSeqFuel? : Nat → (I : IdCtx) → (xs : List SExp) →
    Option (Derived Expr (FoldedSeq I xs))
  | 0, _, _ => none
  | _ + 1, _, [] => some ⟨[], [], .nil⟩
  | fuel + 1, I, x :: xs => do
      let e ← foldedFuel? fuel I x
      let tail ← foldedSeqFuel? fuel I xs
      pure ⟨e.value ++ tail.value, e.uses ++ tail.uses, by simpa using FoldedSeq.cons e.sound tail.sound⟩

def foldedFuel? : Nat → (I : IdCtx) → (x : SExp) →
    Option (Derived Expr (Folded I x))
  | 0, _, _ => none
  | fuel + 1, I, x => do
      let items ← list? x
      match items.1 with
      | .atom (.sym "block") :: _ =>
          let h ← header? "block" x
          let sig ← blockSignature? I h
          let I' ← label? I h.name
          let body ← exprFuel? fuel I'.1 h.body
          if hx : x = L (.atom (.sym "block") :: (idSyntax h.name ++ h.typeSyntax ++ h.body)) then
            some ⟨[.block sig.value body.value], sig.uses ++ body.uses, folded_transport hx (by
              simpa using Folded.block I'.2 sig.sound body.sound)⟩
          else none
      | .atom (.sym "loop") :: _ =>
          let h ← header? "loop" x
          let sig ← blockSignature? I h
          let I' ← label? I h.name
          let body ← exprFuel? fuel I'.1 h.body
          if hx : x = L (.atom (.sym "loop") :: (idSyntax h.name ++ h.typeSyntax ++ h.body)) then
            some ⟨[.loop sig.value body.value], sig.uses ++ body.uses, folded_transport hx (by
              simpa using Folded.loop I'.2 sig.sound body.sound)⟩
          else none
      | .atom (.sym "try_table") :: _ =>
          let h ← header? "try_table" x
          let sig ← blockSignature? I h
          let I' ← label? I h.name
          let cxs := h.body.takeWhile isCatch
          let catches ← mapCertified (catch? I) cxs
          let body ← exprFuel? fuel I'.1 (h.body.drop cxs.length)
          if hx : x = L (K "try_table" :: (idSyntax h.name ++ h.typeSyntax ++ cxs ++ h.body.drop cxs.length)) then
            some ⟨[.tryTable sig.value catches.1 body.value], sig.uses ++ body.uses, folded_transport hx (by
              simpa using Folded.tryTable I'.2 sig.sound catches.2 body.sound)⟩
          else none
      | .atom (.sym "if") :: _ =>
          let h ← header? "if" x
          let sig ← blockSignature? I h
          let I' ← label? I h.name
          let conds := h.body.takeWhile (fun x => !(headed "then" x))
          let c ← foldedSeqFuel? fuel I conds
          match h.body.drop conds.length with
          | [thn] =>
              let .atom (.sym "then") :: yes ← toList? thn | none
              let y ← exprFuel? fuel I'.1 yes
              if hx : x = L (.atom (.sym "if") :: (idSyntax h.name ++ h.typeSyntax ++ conds ++
                  [L (.atom (.sym "then") :: yes)])) then
                some ⟨c.value ++ [.if_ sig.value y.value []], sig.uses ++ c.uses ++ y.uses, folded_transport hx (by
                  simpa using Folded.ifThen I'.2 sig.sound c.sound y.sound)⟩
              else none
          | [thn, els] =>
              let .atom (.sym "then") :: yes ← toList? thn | none
              let .atom (.sym "else") :: no ← toList? els | none
              let y ← exprFuel? fuel I'.1 yes
              let n ← exprFuel? fuel I'.1 no
              if hx : x = L (.atom (.sym "if") :: (idSyntax h.name ++ h.typeSyntax ++ conds ++
                  [L (.atom (.sym "then") :: yes), L (.atom (.sym "else") :: no)])) then
                some ⟨c.value ++ [.if_ sig.value y.value n.value], sig.uses ++ c.uses ++ y.uses ++ n.uses, folded_transport hx (by
                  simpa using Folded.ifThenElse I'.2 sig.sound c.sound y.sound n.sound)⟩
              else none
          | _ => none
      | _ =>
          let p ← plain? I items.1
          let operands ← exprFuel? fuel I p.rest
          match hp : p.consumed with
          | .atom (.sym name) :: imms =>
              pure ⟨operands.value ++ [p.instruction], operands.uses ++ p.uses, by
                apply folded_transport (y := L (.atom (.sym name) :: (imms ++ p.rest)))
                · calc
                    x = L items.1 := items.2
                    _ = L (p.consumed ++ p.rest) := congrArg L p.split
                    _ = L (.atom (.sym name) :: (imms ++ p.rest)) := by rw [hp]; rfl
                · simpa using Folded.plain (by simpa [hp] using p.sound) operands.sound⟩
          | _ => none
end

def expr? (I : IdCtx) (xs : List SExp) : Option (Derived Expr (ExprT I xs)) :=
  exprFuel? (xs.foldl (fun n x => n + syntaxNodes x + 1) 1) I xs

def func? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let h ← header? "func" x
  let ns ← exports? h.exports
  let tu ← typeUse? I h
  let ls ← concat? (local? I) h.locals
  let I' := I ++ { locals := tu.parameters ++ ls.1.map Prod.snd }
  if hok : I'.Ok then do
    let e ← expr? I' h.body
    if hx : x = L (.atom (.sym "func") :: (idSyntax h.name ++ h.exports ++
        h.typeSyntax ++ h.locals ++ h.body)) then
      some ⟨(.func ⟨tu.index, ls.1.map Prod.fst, e.value⟩ :: selfExports ns.1,
        { funcs := [h.name] }, tu.uses ++ e.uses), by
        rw [hx]
        simpa using DeclT.func (idSyntax_sound h.name) ns.2 tu.sound ls.2 hok e.sound⟩
    else none
  else none


end WithUses


def storage? (I : IdCtx) (x : SExp) : Option {z : StorageType // StorageTypeT I x z} := do
  match hx : x with
  | .atom (.sym "i8") => pure ⟨.packed .i8, .inr (.inl ⟨hx, rfl⟩)⟩
  | .atom (.sym "i16") => pure ⟨.packed .i16, .inr (.inr ⟨hx, rfl⟩)⟩
  | _ =>
      let t ← value? I x
      pure ⟨.val t.1, .inl ⟨t.1, t.2, rfl⟩⟩

def fieldType? (I : IdCtx) (x : SExp) : Option {f : FieldType // FieldTypeT I x f} := do
  match toList? x with
  | some [.atom (.sym "mut"), zx] =>
      let z ← storage? I zx
      if hx : x = L [.atom (.sym "mut"), zx] then
        some ⟨⟨.var, z.1⟩, .inr ⟨zx, z.1, hx, z.2, rfl⟩⟩
      else none
  | _ =>
      let z ← storage? I x
      pure ⟨⟨.const, z.1⟩, .inl ⟨z.1, z.2, rfl⟩⟩

def structField? (I : IdCtx) (x : SExp) :
    Option {fs : List (FieldType × Option String) // FieldT I x fs} := do
  let items ← list? x
  match hi : items.1 with
  | [.atom (.sym "field"), .atom (.id name), fx] =>
      let f ← fieldType? I fx
      pure ⟨[(f.1, some name)], .inl ⟨name, fx, f.1,
        by rw [items.2, hi], f.2, rfl⟩⟩
  | .atom (.sym "field") :: fxs =>
      let fs ← mapCertified (fieldType? I) fxs
      pure ⟨fs.1.map (·, none), .inr ⟨fxs, fs.1,
        by rw [items.2, hi], fs.2, rfl⟩⟩
  | _ => none

structure Composite (I : IdCtx) (x : SExp) where
  type : CompositeType
  fields : List (Option String)
  sound : CompTypeT I x type fields

def composite? (I : IdCtx) (x : SExp) : Option (Composite I x) := do
  let .atom (.sym kind) :: body ← toList? x | none
  match _hk : kind with
  | "struct" =>
      let fs ← concat? (structField? I) body
      if hx : x = L (.atom (.sym "struct") :: body) then
        some ⟨.struct (fs.1.map Prod.fst), fs.1.map Prod.snd,
          .inl ⟨body, fs.1, hx, fs.2, rfl, rfl⟩⟩
      else none
  | "array" =>
      let [fx] := body | none
      let f ← fieldType? I fx
      if hx : x = L [.atom (.sym "array"), fx] then
        some ⟨.array f.1, [], .inr (.inl ⟨fx, f.1, hx, f.2, rfl, rfl⟩)⟩
      else none
  | "func" =>
      let h ← header? "func" x
      let ps ← concat? (param? I) h.params
      let rs ← concat? (result? I) h.results
      if hx : x = L (.atom (.sym "func") :: (h.params ++ h.results)) then
        some ⟨.func ⟨ps.1.map Prod.fst, rs.1⟩, [], .inr (.inr
          ⟨h.params, h.results, ps.1, rs.1, hx, ps.2, rs.2, rfl, rfl⟩)⟩
      else none
  | _ => none

structure Sub (I : IdCtx) (x : SExp) where
  type : SubType
  fields : List (Option String)
  sound : SubTypeT I x type fields

def subtype? (I : IdCtx) (x : SExp) : Option (Sub I x) := do
  match toList? x with
  | some (.atom (.sym "sub") :: body) =>
      let (fin, body) : List SExp × List SExp := match body with
        | .atom (.sym "final") :: rest => ([.atom (.sym "final")], rest)
        | rest => ([], rest)
      let cx ← body.getLast?
      let supers := body.dropLast
      let is ← mapCertified (index? I.types) supers
      let c ← composite? I cx
      if hx : x = L (.atom (.sym "sub") :: (fin ++ supers ++ [cx])) then
        if hf : fin = [] ∨ fin = [.atom (.sym "final")] then
          if hl : is.1.length < 2 ^ 32 then
            some ⟨⟨decide (fin ≠ []), is.1, c.type⟩, c.fields,
              .inl ⟨fin, supers, cx, is.1, c.type, hx, hf, is.2, hl, c.sound, rfl⟩⟩
          else none
        else none
      else none
  | _ =>
      let c ← composite? I x
      pure ⟨⟨true, [], c.type⟩, c.fields, .inr ⟨c.type, c.sound, rfl⟩⟩

def typeDefinition? (I : IdCtx) (x : SExp) : Option
    {d : SubType × Option String × List (Option String) // TypeDefT I x d.1 d.2.1 d.2.2} := do
  let .atom (.sym "type") :: body ← toList? x | none
  let (name, body) := stripId body
  let [sx] := body | none
  let s ← subtype? I sx
  if hx : x = L (.atom (.sym "type") :: (idSyntax name ++ [sx])) then
    some ⟨(s.type, name, s.fields), ⟨idSyntax name, sx, hx, idSyntax_sound name, s.sound⟩⟩
  else none

def recursiveType? (I : IdCtx) (x : SExp) : Option
    {p : RecType × IdCtx // RecTypeT I x p.1 p.2} := do
  match toList? x with
  | some (.atom (.sym "rec") :: dxs) =>
      let defs ← mapCertified (typeDefinition? I) dxs
      if hl : defs.1.length < 2 ^ 32 then
        if hx : x = L (.atom (.sym "rec") :: dxs) then
          some ⟨(⟨defs.1.map Prod.fst⟩, recCtx defs.1),
            .inl ⟨dxs, defs.1, hx, defs.2, hl, rfl, rfl⟩⟩
        else none
      else none
  | _ =>
      let d ← typeDefinition? I x
      pure ⟨(⟨[d.1.1]⟩, recCtx [d.1]), .inr ⟨d.1.1, d.1.2.1, d.1.2.2, d.2, rfl, rfl⟩⟩

def typeField? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let p ← recursiveType? I x
  pure ⟨([.type p.1.1], { p.1.2 with
    typedefs := (List.range p.1.1.types.length).map fun i => some (p.1.1, i) }, []),
    .type p.2⟩

/-- Raw type names are only a resolution hint. The final module context is
still checked against the contexts of the independently certified type fields. -/
def rawTypeNames (x : SExp) : List (Option String) :=
  match toList? x with
  | some (.atom (.sym "type") :: body) => [(stripId body).1]
  | some (.atom (.sym "rec") :: dxs) => dxs.map fun dx =>
      match toList? dx with
      | some (.atom (.sym "type") :: body) => (stripId body).1
      | _ => none
  | _ => []

def exportField? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let [.atom (.sym "export"), .atom (.str bytes), target] ← toList? x | none
  let name ← Unicode.utf8? bytes
  let hn ← ensure (Unicode.utf8? bytes = some name)
  let [.atom (.sym kind), ix] ← toList? target | none
  let hp ← ensure (x = L [.atom (.sym "export"), .atom (.str bytes),
      L [.atom (.sym kind), ix]])
  match hk : kind with
  | "func" =>
      let i ← index? I.funcs ix
      some ⟨([.export_ ⟨name, .func i.1⟩], {}, []), by
        rw [hp.down, hk]
        exact .export_ ⟨bytes, rfl, hn.down⟩ (.inr (.inr (.inr (.inr ⟨ix, i.1, rfl, i.2, rfl⟩))))⟩
  | "global" =>
      let i ← index? I.globals ix
      some ⟨([.export_ ⟨name, .global i.1⟩], {}, []), by
        rw [hp.down, hk]
        exact .export_ ⟨bytes, rfl, hn.down⟩ (.inr (.inl ⟨ix, i.1, rfl, i.2, rfl⟩))⟩
  | "memory" =>
      let i ← index? I.mems ix
      some ⟨([.export_ ⟨name, .memory i.1⟩], {}, []), by
        rw [hp.down, hk]
        exact .export_ ⟨bytes, rfl, hn.down⟩ (.inr (.inr (.inl ⟨ix, i.1, rfl, i.2, rfl⟩)))⟩
  | "table" =>
      let i ← index? I.tables ix
      some ⟨([.export_ ⟨name, .table i.1⟩], {}, []), by
        rw [hp.down, hk]
        exact .export_ ⟨bytes, rfl, hn.down⟩ (.inr (.inr (.inr (.inl ⟨ix, i.1, rfl, i.2, rfl⟩))))⟩
  | "tag" =>
      let i ← index? I.tags ix
      some ⟨([.export_ ⟨name, .tag i.1⟩], {}, []), by
        rw [hp.down, hk]
        exact .export_ ⟨bytes, rfl, hn.down⟩ (.inl ⟨ix, i.1, rfl, i.2, rfl⟩)⟩
  | _ => none

def startField? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let [.atom (.sym "start"), ix] ← toList? x | none
  let i ← index? I.funcs ix
  if hx : x = L [.atom (.sym "start"), ix] then
    some ⟨([.start i.1], {}, []), by rw [hx]; exact .start i.2⟩
  else none

def limits? (xs : List SExp) : Option {l : Limits // LimitsT xs l} := do
  match hx : xs with
  | [nx] =>
      let n ← unsigned? 64 nx
      pure ⟨⟨n.1, none⟩, .inl ⟨nx, n.1, hx, n.2, rfl⟩⟩
  | [nx, mx] =>
      let n ← unsigned? 64 nx
      let m ← unsigned? 64 mx
      pure ⟨⟨n.1, some m.1⟩, .inr ⟨nx, mx, n.1, m.1, hx, n.2, m.2, rfl⟩⟩
  | _ => none

def memoryType? (xs : List SExp) : Option {m : MemoryType // MemTypeT xs m} := do
  match hx : xs with
  | .atom (.sym "i64") :: rest =>
      let l ← limits? rest
      pure ⟨⟨.i64, l.1⟩, ⟨[.atom (.sym "i64")], rest, .i64, l.1, hx,
        .inr (.inr ⟨rfl, rfl⟩), l.2, rfl⟩⟩
  | .atom (.sym "i32") :: rest =>
      let l ← limits? rest
      pure ⟨⟨.i32, l.1⟩, ⟨[.atom (.sym "i32")], rest, .i32, l.1, hx,
        .inr (.inl ⟨rfl, rfl⟩), l.2, rfl⟩⟩
  | rest =>
      let l ← limits? rest
      pure ⟨⟨.i32, l.1⟩, ⟨[], rest, .i32, l.1, hx,
        .inl ⟨rfl, rfl⟩, l.2, rfl⟩⟩

def memoryField? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let h ← header? "memory" x
  let ns ← exports? h.exports
  let m ← memoryType? h.body
  if hx : x = L (.atom (.sym "memory") :: (idSyntax h.name ++ h.exports ++ h.body)) then
    some ⟨(.mem m.1 :: selfExports ns.1, { mems := [h.name] }, []), by
      rw [hx]
      exact .mem (idSyntax_sound h.name) ns.2 m.2⟩
  else none

def globalType? (I : IdCtx) (x : SExp) : Option {g : GlobalType // GlobalTypeT I x g} := do
  match toList? x with
  | some [.atom (.sym "mut"), tx] =>
      let t ← value? I tx
      if hx : x = L [.atom (.sym "mut"), tx] then
        some ⟨⟨.var, t.1⟩, .inr ⟨tx, t.1, hx, t.2, rfl⟩⟩
      else none
  | _ =>
      let t ← value? I x
      pure ⟨⟨.const, t.1⟩, .inl ⟨t.1, t.2, rfl⟩⟩

def globalField? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let h ← header? "global" x
  let ns ← exports? h.exports
  let gx :: body := h.body | none
  let g ← globalType? I gx
  let e ← expr? I body
  if hx : x = L (.atom (.sym "global") :: (idSyntax h.name ++ h.exports ++ gx :: body)) then
    some ⟨(.global ⟨g.1, e.1⟩ :: selfExports ns.1, { globals := [h.name] }, []), by
      rw [hx]
      exact .global (idSyntax_sound h.name) ns.2 g.2 e.2⟩
  else none

structure External (I : IdCtx) (x : SExp) where
  type : ExternType
  context : IdCtx
  uses : List FuncType
  sound : ExternTypeT I x type context uses

def external? (I : IdCtx) (x : SExp) : Option (External I x) := do
  let .atom (.sym kind) :: rest ← toList? x | none
  let (name, body) := stripId rest
  match _hk : kind with
  | "func" =>
      let h ← header? "func" x
      let tu ← typeUse? I h
      if hx : x = L (.atom (.sym "func") :: (idSyntax h.name ++ h.typeSyntax)) then
        some ⟨.func tu.index, { funcs := [h.name] }, tu.uses,
          .inr (.inr (.inr (.inr ⟨idSyntax h.name, h.typeSyntax, h.name, tu.index,
            tu.parameters, hx, idSyntax_sound h.name, tu.sound, rfl, rfl⟩)))⟩
      else none
  | "memory" =>
      let m ← memoryType? body
      if hx : x = L (.atom (.sym "memory") :: (idSyntax name ++ body)) then
        some ⟨.memory m.1, { mems := [name] }, [],
          .inr (.inr (.inl ⟨idSyntax name, body, name, m.1, hx,
            idSyntax_sound name, m.2, rfl, rfl, rfl⟩))⟩
      else none
  | "global" =>
      let [gx] := body | none
      let g ← globalType? I gx
      if hx : x = L (.atom (.sym "global") :: (idSyntax name ++ [gx])) then
        some ⟨.global g.1, { globals := [name] }, [],
          .inr (.inl ⟨idSyntax name, gx, name, g.1, hx,
            idSyntax_sound name, g.2, rfl, rfl, rfl⟩)⟩
      else none
  | _ => none

def importField? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let [.atom (.sym "import"), .atom (.str source), .atom (.str field), target] ← toList? x | none
  let moduleName ← Unicode.utf8? source
  let name ← Unicode.utf8? field
  let hs ← ensure (Unicode.utf8? source = some moduleName)
  let hn ← ensure (Unicode.utf8? field = some name)
  let e ← external? I target
  if hx : x = L [.atom (.sym "import"), .atom (.str source), .atom (.str field), target] then
    some ⟨([.import_ ⟨moduleName, name, e.type⟩], e.context, e.uses), by
      rw [hx]
      exact .import_ ⟨source, rfl, hs.down⟩ ⟨field, rfl, hn.down⟩ e.sound⟩
  else none

def stringBytes? (x : SExp) : Option {bs : List UInt8 // x = .atom (.str bs)} :=
  match x with
  | .atom (.str bs) => some ⟨bs, rfl⟩
  | _ => none

def strings? (xs : List SExp) : Option {bs : List UInt8 // DataStringT xs bs} := do
  let bss ← mapCertified stringBytes? xs
  pure ⟨bss.1.flatten, ⟨bss.1, bss.2, rfl⟩⟩

def offset? (I : IdCtx) (x : SExp) : Option {e : Expr // OffsetT I x e []} := do
  match toList? x with
  | some (.atom (.sym "offset") :: body) =>
      let e ← expr? I body
      if hx : x = L (.atom (.sym "offset") :: body) then
        some ⟨e.1, .inl ⟨body, hx, e.2⟩⟩
      else none
  | _ =>
      let e ← foldedFuel? (syntaxNodes x + 1) I x
      pure ⟨e.1, .inr e.2⟩

def memoryUse? (I : IdCtx) (xs : List SExp) : Option {m : MemIdx // MemUseT I xs m} := do
  match hx : xs with
  | [] => pure ⟨⟨0⟩, .inl ⟨hx, rfl⟩⟩
  | [item] =>
      let [.atom (.sym "memory"), ix] ← toList? item | none
      let i ← index? I.mems ix
      if hi : xs = [L [.atom (.sym "memory"), ix]] then
        some ⟨i.1, .inr ⟨ix, hi, i.2⟩⟩
      else none
  | _ => none

def dataField? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let .atom (.sym "data") :: rest ← toList? x | none
  let (name, body) := stripId rest
  match strings? body with
  | some bytes =>
      if hx : x = L (.atom (.sym "data") :: (idSyntax name ++ body)) then
        some ⟨([.data ⟨⟨bytes.1.toArray⟩, .passive⟩], { datas := [name] }, []), by
          rw [hx]
          exact .dataPassive (idSyntax_sound name) bytes.2⟩
      else none
  | none =>
      let mu := body.takeWhile (headed "memory")
      let m ← memoryUse? I mu
      let ox :: strs := body.drop mu.length | none
      let offset ← offset? I ox
      let bytes ← strings? strs
      if hx : x = L (.atom (.sym "data") :: (idSyntax name ++ mu ++ ox :: strs)) then
        some ⟨([.data ⟨⟨bytes.1.toArray⟩, .active m.1 offset.1⟩], { datas := [name] }, []), by
          rw [hx]
          exact .dataActive (idSyntax_sound name) m.2 offset.2 bytes.2⟩
      else none


/-- A complete table type; address and limits reuse the memory-type checker. -/
def tableType? (I : IdCtx) (xs : List SExp) :
    Option {t : TableType // TableTypeT I xs t} := do
  let rx :: rev := xs.reverse | none
  let leading := rev.reverse
  let m ← memoryType? leading
  let r ← reference? I rx
  if hx : xs = leading ++ [rx] then
    some ⟨⟨m.1.address, m.1.limits, r.1⟩, by
      obtain ⟨ax, lx, a, l, hs, ha, hl, hm⟩ := m.2
      exact ⟨ax, lx, rx, a, l, r.1, by simpa [hs, List.append_assoc] using hx,
        ha, hl, r.2, by simp [hm]⟩⟩
  else none

structure TableTypeHead (I : IdCtx) (xs : List SExp) where
  consumed : List SExp
  rest : List SExp
  type : TableType
  split : xs = consumed ++ rest
  sound : TableTypeT I consumed type

def tableTypeHead? (I : IdCtx) (xs : List SExp) : Option (TableTypeHead I xs) := do
  let n ← [4, 3, 2].find? (fun n => (tableType? I (xs.take n)).isSome)
  let t ← tableType? I (xs.take n)
  if hs : xs = xs.take n ++ xs.drop n then
    some ⟨xs.take n, xs.drop n, t.1, hs, t.2⟩
  else none

def elementExpr? (I : IdCtx) (x : SExp) : Option {e : Expr // ElemExprT I x e []} := do
  match toList? x with
  | some (.atom (.sym "item") :: body) =>
      let e ← expr? I body
      if hx : x = L (.atom (.sym "item") :: body) then
        some ⟨e.1, .inl ⟨body, hx, e.2⟩⟩
      else none
  | _ =>
      let e ← foldedFuel? (syntaxNodes x + 1) I x
      pure ⟨e.1, .inr e.2⟩

theorem withEmptyUses {α β : Type} {R : α → β × List FuncType → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ (fun x y => R x (y, [])) xs ys) :
    List.Forall₂ R xs (ys.zip (ys.map fun _ => [])) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih

structure ElementList (I : IdCtx) (xs : List SExp) where
  type : RefType
  init : List Expr
  sound : ElemListT I xs type init []

def elementList? (I : IdCtx) (xs : List SExp) : Option (ElementList I xs) := do
  match hx : xs with
  | .atom (.sym "func") :: rest =>
      let fs ← mapCertified (index? I.funcs) rest
      let hl ← ensure (fs.1.length < 2 ^ 32)
      pure ⟨⟨false, .abstract .func⟩, fs.1.map (fun f => [.refFunc f]),
        .inr ⟨rest, fs.1, hx, fs.2, hl.down, rfl, rfl, rfl⟩⟩
  | rx :: rest =>
      let r ← reference? I rx
      let es ← mapCertified (elementExpr? I) rest
      let hl ← ensure (es.1.length < 2 ^ 32)
      pure ⟨r.1, es.1, .inl ⟨rx, rest, es.1.map (fun _ => []), hx, r.2,
        withEmptyUses es.2, by simp, hl.down, by simp⟩⟩
  | _ => none

def tableUse? (I : IdCtx) (xs : List SExp) : Option {t : TableIdx // TableUseT I xs t} := do
  match hx : xs with
  | [] => pure ⟨⟨0⟩, .inl ⟨hx, rfl⟩⟩
  | [item] =>
      let [.atom (.sym "table"), ix] ← toList? item | none
      let i ← index? I.tables ix
      if hi : xs = [L [.atom (.sym "table"), ix]] then
        some ⟨i.1, .inr ⟨ix, hi, i.2⟩⟩
      else none
  | _ => none

/-- Passive, declared, and active element fields, including the original
single-table offset/function-index abbreviation. -/
def elemField? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let .atom (.sym "elem") :: rest ← toList? x | none
  let (name, body) := stripId rest
  match body with
  | .atom (.sym "declare") :: el =>
      let e ← elementList? I el
      if hx : x = L (.atom (.sym "elem") :: (idSyntax name ++ .atom (.sym "declare") :: el)) then
        some ⟨([.elem ⟨e.type, e.init, .declarative⟩], { elems := [name] }, []), by
          rw [hx]
          exact .elemDeclare (idSyntax_sound name) e.sound⟩
      else none
  | _ =>
      match elementList? I body with
      | some e =>
          if hx : x = L (.atom (.sym "elem") :: (idSyntax name ++ body)) then
            some ⟨([.elem ⟨e.type, e.init, .passive⟩], { elems := [name] }, []), by
              rw [hx]
              exact .elemPassive (idSyntax_sound name) e.sound⟩
          else none
      | none =>
          let tu := body.takeWhile (headed "table")
          let t ← tableUse? I tu
          let ox :: el := body.drop tu.length | none
          let offset ← offset? I ox
          match elementList? I el with
          | some e =>
              if hx : x = L (.atom (.sym "elem") :: (idSyntax name ++ tu ++ ox :: el)) then
                some ⟨([.elem ⟨e.type, e.init, .active t.1 offset.1⟩],
                    { elems := [name] }, []), by
                  rw [hx]
                  simpa using DeclT.elemActive (idSyntax_sound name) t.2 offset.2 e.sound⟩
              else none
          | none =>
              let fs ← mapCertified (index? I.funcs) el
              let hl ← ensure (fs.1.length < 2 ^ 32)
              if hx : x = L (.atom (.sym "elem") :: (idSyntax name ++ ox :: el)) then
                some ⟨([.elem ⟨⟨false, .abstract .func⟩,
                    fs.1.map (fun f => [.refFunc f]), .active ⟨0⟩ offset.1⟩],
                    { elems := [name] }, []), by
                  rw [hx]
                  exact .elemFuncs (idSyntax_sound name) offset.2 fs.2 hl.down⟩
              else none

def addressType? (xs : List SExp) : Option {a : AddrType // AddrTypeT xs a} :=
  match xs with
  | [] => some ⟨.i32, .inl ⟨rfl, rfl⟩⟩
  | [.atom (.sym "i32")] => some ⟨.i32, .inr (.inl ⟨rfl, rfl⟩)⟩
  | [.atom (.sym "i64")] => some ⟨.i64, .inr (.inr ⟨rfl, rfl⟩)⟩
  | _ => none

/-- Inline data memories contribute both their memory and anonymous active
segment to the independently checked context. -/
def inlineDataMemory? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let h ← header? "memory" x
  let ns ← exports? h.exports
  let (ax, tail) := match h.body with
    | .atom (.sym "i64") :: tail => ([K "i64"], tail)
    | .atom (.sym "i32") :: tail => ([K "i32"], tail)
    | tail => ([], tail)
  let a ← addressType? ax
  let [data] := tail | none
  let .atom (.sym "data") :: strs ← toList? data | none
  let bs ← strings? strs
  if hx : x = L (K "memory" ::
      (idSyntax h.name ++ h.exports ++ ax ++ [L (K "data" :: strs)])) then
    some ⟨(.mem ⟨a.1, exactLimits (pagesFor bs.1.length)⟩ ::
        .dataSelf a.1 bs.1 :: selfExports ns.1,
      { mems := [h.name], datas := [none] }, []), by
      rw [hx]; exact .memData (idSyntax_sound h.name) ns.2 a.2 bs.2⟩
  else none

/-- Inline element tables bind both a table and its active segment. -/
def inlineElemTable? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let h ← header? "table" x
  let ns ← exports? h.exports
  let (ax, tail) := match h.body with
    | .atom (.sym "i64") :: tail => ([.atom (.sym "i64")], tail)
    | .atom (.sym "i32") :: tail => ([.atom (.sym "i32")], tail)
    | tail => ([], tail)
  let ha ← addressType? ax
  let addr := ha.1
  let [rx, ex] := tail | none
  let r ← reference? I rx
  let .atom (.sym "elem") :: items ← toList? ex | none
  match mapCertified (index? I.funcs) items with
  | some fs =>
      let hl ← ensure (fs.1.length < 2 ^ 32)
      if hx : x = L (.atom (.sym "table") :: (idSyntax h.name ++ h.exports ++ ax ++ [rx, L (.atom (.sym "elem") :: items)])) then
        some ⟨(.table ⟨⟨addr, exactLimits fs.1.length, r.1⟩, [.refNull r.1.heap]⟩ ::
            .elemSelf addr r.1 (fs.1.map (fun f => [.refFunc f])) :: selfExports ns.1,
            { tables := [h.name], elems := [none] }, []), by
          rw [hx]
          exact .tableElemFuncs (idSyntax_sound h.name) ns.2 ha.2 r.2 fs.2 hl.down⟩
      else none
  | none =>
      let es ← mapCertified (elementExpr? I) items
      let hl ← ensure (es.1.length < 2 ^ 32)
      let hn ← ensure (items ≠ [])
      if hx : x = L (.atom (.sym "table") :: (idSyntax h.name ++ h.exports ++ ax ++ [rx, L (.atom (.sym "elem") :: items)])) then
        some ⟨(.table ⟨⟨addr, exactLimits es.1.length, r.1⟩, [.refNull r.1.heap]⟩ ::
            .elemSelf addr r.1 es.1 :: selfExports ns.1,
            { tables := [h.name], elems := [none] }, []), by
          rw [hx]
          simpa using DeclT.tableElemExprs (idSyntax_sound h.name) ns.2 ha.2 r.2 hn.down
            (withEmptyUses es.2) (by simp) hl.down⟩
      else none

def tableField? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let h ← header? "table" x
  let ns ← exports? h.exports
  match tableTypeHead? I h.body with
  | none => inlineElemTable? I x
  | some t =>
      if hx : x = L (.atom (.sym "table") :: (idSyntax h.name ++ h.exports ++ t.consumed ++ t.rest)) then
        if he : t.rest = [] then
          some ⟨(.table ⟨t.type, [.refNull t.type.element.heap]⟩ :: selfExports ns.1,
              { tables := [h.name] }, []), by
            rw [hx, he, List.append_nil]
            exact .tableNull (idSyntax_sound h.name) ns.2 t.sound⟩
        else
          let e ← expr? I t.rest
          some ⟨(.table ⟨t.type, e.1⟩ :: selfExports ns.1, { tables := [h.name] }, []), by
            rw [hx]
            exact .table (idSyntax_sound h.name) ns.2 t.sound he e.2⟩
      else none

def tagField? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let h ← header? "tag" x
  let ns ← exports? h.exports
  let t ← typeUse? I h
  if hx : x = L (.atom (.sym "tag") :: (idSyntax h.name ++ h.exports ++ h.typeSyntax)) then
    some ⟨(.tag t.index :: selfExports ns.1, { tags := [h.name] }, t.uses), by
      rw [hx]
      exact .tag (idSyntax_sound h.name) ns.2 ⟨t.parameters, t.sound⟩⟩
  else none

/-- Keep the original external-kind parser available, adding tables and tags. -/
def externalExtended? (I : IdCtx) (x : SExp) : Option (External I x) := do
  let .atom (.sym kind) :: rest ← toList? x | none
  let (name, body) := stripId rest
  match kind with
  | "table" =>
      let t ← tableType? I body
      if hx : x = L (.atom (.sym "table") :: (idSyntax name ++ body)) then
        some ⟨.table t.1, { tables := [name] }, [],
          .inr (.inr (.inr (.inl ⟨idSyntax name, body, name, t.1, hx,
            idSyntax_sound name, t.2, rfl, rfl, rfl⟩)))⟩
      else none
  | "tag" =>
      let h ← header? "tag" x
      let t ← typeUse? I h
      if hx : x = L (.atom (.sym "tag") :: (idSyntax h.name ++ h.typeSyntax)) then
        some ⟨.tag t.index, { tags := [h.name] }, t.uses,
          .inl ⟨idSyntax h.name, h.typeSyntax, h.name, t.index, hx,
            idSyntax_sound h.name, ⟨t.parameters, t.sound⟩, rfl, rfl⟩⟩
      else none
  | _ => external? I x

def importExtendedField? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let [.atom (.sym "import"), .atom (.str source), .atom (.str field), target] ← toList? x | none
  let moduleName ← Unicode.utf8? source
  let name ← Unicode.utf8? field
  let hs ← ensure (Unicode.utf8? source = some moduleName)
  let hn ← ensure (Unicode.utf8? field = some name)
  let e ← externalExtended? I target
  if hx : x = L [.atom (.sym "import"), .atom (.str source), .atom (.str field), target] then
    some ⟨([.import_ ⟨moduleName, name, e.type⟩], e.context, e.uses), by
      rw [hx]
      exact .import_ ⟨source, rfl, hs.down⟩ ⟨field, rfl, hn.down⟩ e.sound⟩
  else none


structure InlineImport (x : SExp) where
  moduleName : String
  name : String
  sound : InlineImportT x moduleName name

def inlineImport? (x : SExp) : Option (InlineImport x) := do
  let [.atom (.sym "import"), .atom (.str moduleBytes), .atom (.str nameBytes)] ← toList? x | none
  let moduleName ← Unicode.utf8? moduleBytes
  let name ← Unicode.utf8? nameBytes
  let hm ← ensure (Unicode.utf8? moduleBytes = some moduleName)
  let hn ← ensure (Unicode.utf8? nameBytes = some name)
  if hx : x = L [K "import", .atom (.str moduleBytes), .atom (.str nameBytes)] then
    some ⟨moduleName, name, ⟨_, _, hx, ⟨moduleBytes, rfl, hm.down⟩, ⟨nameBytes, rfl, hn.down⟩⟩⟩
  else none

/-- Inline imports preserve their original names, exports and type syntax. -/
def inlineImportField? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let .atom (.sym kind) :: _ ← toList? x | none
  let h ← header? kind x
  let ns ← exports? h.exports
  let imp :: body := h.body | none
  let im ← inlineImport? imp
  match kind with
  | "func" =>
      let inner ← header? "func" (L (K "func" :: body))
      let tu ← typeUse? I inner
      if hx : x = L (K "func" :: (idSyntax h.name ++ h.exports ++ imp :: inner.typeSyntax)) then
        some ⟨(.import_ ⟨im.moduleName, im.name, .func tu.index⟩ :: selfExports ns.1,
          { funcs := [h.name] }, tu.uses), by
          rw [hx]; exact .funcImport (idSyntax_sound h.name) ns.2 im.sound tu.sound⟩
      else none
  | "tag" =>
      let inner ← header? "tag" (L (K "tag" :: body))
      let tu ← typeUse? I inner
      if hx : x = L (K "tag" :: (idSyntax h.name ++ h.exports ++ imp :: inner.typeSyntax)) then
        some ⟨(.import_ ⟨im.moduleName, im.name, .tag tu.index⟩ :: selfExports ns.1,
          { tags := [h.name] }, tu.uses), by
          rw [hx]; exact .tagImport (idSyntax_sound h.name) ns.2 im.sound ⟨tu.parameters, tu.sound⟩⟩
      else none
  | "memory" =>
      let mt ← memoryType? body
      if hx : x = L (K "memory" :: (idSyntax h.name ++ h.exports ++ imp :: body)) then
        some ⟨(.import_ ⟨im.moduleName, im.name, .memory mt.1⟩ :: selfExports ns.1,
          { mems := [h.name] }, []), by
          rw [hx]; exact .memImport (idSyntax_sound h.name) ns.2 im.sound mt.2⟩
      else none
  | "table" =>
      let tt ← tableType? I body
      if hx : x = L (K "table" :: (idSyntax h.name ++ h.exports ++ imp :: body)) then
        some ⟨(.import_ ⟨im.moduleName, im.name, .table tt.1⟩ :: selfExports ns.1,
          { tables := [h.name] }, []), by
          rw [hx]; exact .tableImport (idSyntax_sound h.name) ns.2 im.sound tt.2⟩
      else none
  | "global" =>
      let [gx] := body | none
      let gt ← globalType? I gx
      if hx : x = L (K "global" :: (idSyntax h.name ++ h.exports ++ [imp, gx])) then
        some ⟨(.import_ ⟨im.moduleName, im.name, .global gt.1⟩ :: selfExports ns.1,
          { globals := [h.name] }, []), by
          rw [hx]; exact .globalImport (idSyntax_sound h.name) ns.2 im.sound gt.2⟩
      else none
  | _ => none

/-- Untrusted type hints include inline imports; final contributions are still
checked by the module's fixed-point equation. -/
def signatureHeader (kind : String) (h : Header) : Header :=
  match h.body with
  | imp :: body => if headed "import" imp then
      (header? kind (L (K kind :: body))).getD h else h
  | [] => h

/-- Discover candidate implicit instruction signatures without trusting their
order or relevance. Certified elaboration below computes the actual uses and
rebuilds the context before the final independent fixed-point check. -/
def syntaxTypeHintsFuel : Nat → IdCtx → List SExp → List FuncType
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, R, x :: xs =>
      let here := match x with
        | .atom (.sym kind) =>
            let indirect := kind == "call_indirect" || kind == "return_call_indirect"
            let block := kind == "block" || kind == "loop" || kind == "if" || kind == "try_table"
            if indirect || block then
              let tail := if indirect then
                match xs with
                | .atom (.id _) :: tail => tail
                | y :: tail => if (index? (k := .table) [] y).isSome then tail else xs
                | [] => []
              else xs
              match header? kind (L (K kind :: tail)) with
              | some h =>
                  if h.type.isSome then [] else
                    match concat? (param? R) h.params, concat? (result? R) h.results with
                    | some ps, some rs =>
                        if indirect || !(ps.1.isEmpty && rs.1.length ≤ 1) then
                          [⟨ps.1.map Prod.fst, rs.1⟩]
                        else []
                    | _, _ => []
              | none => []
            else []
        | _ => []
      let nested := match toList? x with
        | some children => syntaxTypeHintsFuel fuel R children
        | none => []
      here ++ nested ++ syntaxTypeHintsFuel fuel R xs

def syntaxTypeHints (R : IdCtx) (xs : List SExp) : List FuncType :=
  syntaxTypeHintsFuel (xs.foldl (fun n x => n + syntaxNodes x + 1) 1) R xs

/-- Context hints may reject an otherwise supported source when incomplete;
acceptance always checks the final fixed-point equation independently. -/
def fieldHintAt (R : IdCtx) (x : SExp) : IdCtx × List FuncType :=
  match toList? x with
  | some (.atom (.sym "type") :: _) | some (.atom (.sym "rec") :: _) =>
      match typeField? R x with
      | some o => (o.1.2.1, [])
      | none => ({}, [])
  | some (.atom (.sym "func") :: _) =>
      match header? "func" x with
      | none => ({}, [])
      | some h =>
          let signature := signatureHeader "func" h
          let uses := if signature.type.isNone then
            match concat? (param? R) signature.params, concat? (result? R) signature.results with
            | some ps, some rs => [⟨ps.1.map Prod.fst, rs.1⟩]
            | _, _ => []
          else []
          ({ funcs := [h.name] }, uses ++ syntaxTypeHints R signature.body)
  | some (.atom (.sym "memory") :: rest) =>
      let datas := match header? "memory" x with
        | some h => if h.body.any (headed "data") then [none] else []
        | none => []
      ({ mems := [(stripId rest).1], datas := datas }, [])
  | some (.atom (.sym "global") :: rest) => ({ globals := [(stripId rest).1] }, [])
  | some (.atom (.sym "data") :: rest) => ({ datas := [(stripId rest).1] }, [])
  | some (.atom (.sym "table") :: rest) =>
      let elems := match header? "table" x with
        | some h => if h.body.any (headed "elem") then [none] else []
        | none => []
      ({ tables := [(stripId rest).1], elems := elems }, [])
  | some (.atom (.sym "elem") :: rest) => ({ elems := [(stripId rest).1] }, [])
  | some (.atom (.sym "tag") :: _) =>
      match header? "tag" x with
      | none => ({}, [])
      | some h =>
          let signature := signatureHeader "tag" h
          let uses := if signature.type.isNone then
            match concat? (param? R) signature.params, concat? (result? R) signature.results with
            | some ps, some rs => [⟨ps.1.map Prod.fst, rs.1⟩]
            | _, _ => []
          else []
          ({ tags := [h.name] }, uses)
  | some [.atom (.sym "import"), _, _, target] =>
      match toList? target with
      | some (.atom (.sym "func") :: _) =>
          match header? "func" target with
          | some h =>
              let uses := if h.type.isNone then
                match concat? (param? R) h.params, concat? (result? R) h.results with
                | some ps, some rs => [⟨ps.1.map Prod.fst, rs.1⟩]
                | _, _ => []
              else []
              ({ funcs := [h.name] }, uses)
          | none => ({}, [])
      | some (.atom (.sym "memory") :: rest) => ({ mems := [(stripId rest).1] }, [])
      | some (.atom (.sym "global") :: rest) => ({ globals := [(stripId rest).1] }, [])
      | some (.atom (.sym "table") :: rest) => ({ tables := [(stripId rest).1] }, [])
      | some (.atom (.sym "tag") :: _) =>
          match header? "tag" target with
          | none => ({}, [])
          | some h =>
              let uses := if h.type.isNone then
                match concat? (param? R) h.params, concat? (result? R) h.results with
                | some ps, some rs => [⟨ps.1.map Prod.fst, rs.1⟩]
                | _, _ => []
              else []
              ({ tags := [h.name] }, uses)
      | _ => ({}, [])
  | _ => ({}, [])

def fieldHint (x : SExp) : IdCtx × List FuncType := fieldHintAt {} x

def field? (I : IdCtx) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} :=
  (inlineImportField? I x).orElse fun _ => match toList? x with
  | some (.atom (.sym "type") :: _) | some (.atom (.sym "rec") :: _) => typeField? I x
  | some (.atom (.sym "func") :: _) =>
      (func? I x).orElse fun _ => WithUses.func? I x
  | some (.atom (.sym "export") :: _) => exportField? I x
  | some (.atom (.sym "start") :: _) => startField? I x
  | some (.atom (.sym "memory") :: _) =>
      (inlineDataMemory? I x).orElse fun _ => memoryField? I x
  | some (.atom (.sym "global") :: _) => globalField? I x
  | some (.atom (.sym "import") :: _) => importExtendedField? I x
  | some (.atom (.sym "data") :: _) => dataField? I x
  | some (.atom (.sym "table") :: _) => tableField? I x
  | some (.atom (.sym "elem") :: _) => elemField? I x
  | some (.atom (.sym "tag") :: _) => tagField? I x
  | _ => none

deriving instance DecidableEq for IdCtx

def orderedFinite (ds : List Decl) : Prop :=
  ∀ i j : Fin ds.length, i.val < j.val →
    ds[j.val].isImport = true → ds[i.val].isDefinition = false

instance (ds : List Decl) : Decidable (orderedFinite ds) := by
  unfold orderedFinite
  infer_instance

theorem orderedFinite_sound {ds : List Decl} (h : orderedFinite ds) : Ordered ds :=
  fun i j hi hj hij hjImport => h ⟨i, hi⟩ ⟨j, hj⟩ hij hjImport

/-- Linear import-order check. Once a definition has appeared, later imports
are rejected; neutral declarations (types, data, exports) keep the state. -/
def orderedAfter (seenDefinition : Bool) : List Decl → Bool
  | [] => true
  | d :: ds =>
      if seenDefinition && d.isImport then false
      else orderedAfter (seenDefinition || d.isDefinition) ds

theorem orderedAfter_sound {ds : List Decl} {seen : Bool}
    (h : orderedAfter seen ds = true) :
    Ordered ds ∧ (seen = true → ∀ d ∈ ds, d.isImport = false) := by
  induction ds generalizing seen with
  | nil =>
      constructor
      · intro i j hi; simp at hi
      · simp
  | cons d ds ih =>
      simp only [orderedAfter] at h
      split at h
      · cases h
      · rename_i hbad
        obtain ⟨ho, hs⟩ := ih h
        constructor
        · intro i j hi hj hij hjImport
          cases i with
          | zero =>
              cases j with
              | zero => omega
              | succ j =>
                  by_cases hd : d.isDefinition = true
                  · have hseen : seen || d.isDefinition = true := by simp [hd]
                    have hj' : j < ds.length := by simpa using hj
                    have hn := hs hseen ds[j] (List.getElem_mem hj')
                    simp only [List.getElem_cons_succ] at hjImport
                    rw [hn] at hjImport
                    cases hjImport
                  · simpa using Bool.eq_false_iff.mpr hd
          | succ i =>
              cases j with
              | zero => omega
              | succ j =>
                  exact ho i j (by simpa using hi) (by simpa using hj)
                    (by omega) (by simpa using hjImport)
        · intro hseen e he
          rcases List.mem_cons.mp he with rfl | he
          · cases hd : e.isImport <;> simp_all
          · exact hs (by simp [hseen]) e he


/-- Recover either the explicit module envelope or the standard bare-field
abbreviation, keeping an exact source equality in both cases. -/
def moduleFields? (x : SExp) : Option {fields : List SExp //
    (∃ ix id, x = doc [L (K "module" :: (ix ++ fields))] ∧ IdOpt ix id) ∨
      x = doc fields} := do
  let all ← toList? x
  match all with
  | [top] =>
      match toList? top with
      | some (.atom (.sym "module") :: body) =>
          let (name, fields) := stripId body
          if hx : x = doc [L (K "module" :: (idSyntax name ++ fields))] then
            some ⟨fields, .inl ⟨idSyntax name, name, hx, idSyntax_sound name⟩⟩
          else none
      | _ =>
          if hx : x = doc all then some ⟨all, .inr hx⟩ else none
  | _ =>
      if hx : x = doc all then some ⟨all, .inr hx⟩ else none

/-- Elaborate a complete original module document. Unlike canonical
reification this retains names, source field order, folded operands and type
abbreviations in its certificate. All contexts and implicit types are checked
against the actual derived declarations before returning an artifact. -/
def module? (x : SExp) : Option {m : Wasm.Module // ModuleT x m} := do
  let source ← moduleFields? x
  let fields := source.1
  let names : IdCtx := { types := fields.flatMap rawTypeNames }
  let hints := fields.map (fieldHintAt names)
  let J := IdCtx.concat (hints.map Prod.fst)
  let implicit := implicitTypes J.typedefs (hints.flatMap Prod.snd)
  let provisional := J ++ implicitCtx implicit
  let first ← mapCertified (field? provisional) fields
  let refined := IdCtx.concat (first.1.map (·.2.1))
  let actualUses := first.1.flatMap (·.2.2)
  let I := refined ++ implicitCtx (implicitTypes refined.typedefs actualUses)
  let outs ← mapCertified (field? I) fields
  let J' := IdCtx.concat (outs.1.map (·.2.1))
  let ds := outs.1.flatMap (·.1)
  let implicit' := implicitTypes J'.typedefs (outs.1.flatMap (·.2.2))
  if hI : I = J' ++ implicitCtx implicit' then
    if hok : I.Ok then
      if ho : orderedAfter false ds = true then
        if hs : startCount ds ≤ 1 then
          some ⟨build (resolve ds) implicit', by
            exact ⟨fields, outs.1, I, source.2, outs.2,
              hI, hok, (orderedAfter_sound ho).1, hs, rfl⟩⟩
        else none
      else none
    else none
  else none

end Silmaril.Wasm.Binaryen.Toolkit.Wat.Source

namespace Silmaril.Wasm.Binaryen.Toolkit.Wat

/-- Retain the original canonical fast path, with source-directed certified
elaboration for ordinary named and abbreviated WAT. -/
def parseSupported? (x : Text.SExp) : Option Wasm.Module :=
  match parseCanonical? x with
  | some m => some m
  | none => (Source.module? x).map Subtype.val

theorem parseSupported?_sound {x : Text.SExp} {m : Wasm.Module}
    (h : parseSupported? x = some m) : Text.Core.ModuleT x m := by
  unfold parseSupported? at h
  split at h
  · cases h; exact parseCanonical?_sound (by assumption)
  · obtain ⟨source, _, h⟩ := Option.map_eq_some_iff.mp h
    subst m
    exact source.2

end Silmaril.Wasm.Binaryen.Toolkit.Wat
