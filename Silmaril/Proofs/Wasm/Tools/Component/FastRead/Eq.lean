module

public import Silmaril.Wasm.Tools.Component.FastRead.Defs
public import Silmaril.Wasm.Component.Wat.Sexp.Thms

/-!
# The tail-recursive reader is the reader

`lexA_eq`, `parseStk_sound`, `readF_eq : readF = Sexp.read`, `readXF_eq`,
`parseTextF_eq : parseTextF = Wat.parseText`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.FastRead

open Silmaril.Wasm.Component.Wat (Sexp Tok)
open Silmaril.Wasm.Component.Wat.Sexp (lex lexStr toks parseTop)

/-- **The accumulating lexer is the lexer.** -/
theorem lexA_eq (acc : List Tok) (cs : List Char) :
    lexA acc cs = (lex cs).map (acc.reverse ++ ·) := by
  fun_induction lexA acc cs <;> rw [lex.eq_def] <;> simp_all [lexStrA_eq, Option.map_map,
    Function.comp_def]
  all_goals (split <;> simp_all [Option.map_map, Function.comp_def])

/-- The tokens of the open lists of a stack (outermost first; each list after its `(`). -/
def pre : List (List Sexp) → List Tok
  | [] => []
  | c :: s => (match s with | [] => [] | _ :: _ => pre s ++ [.lp]) ++ toks.toksL c.reverse

theorem toksL_append (a b : List Sexp) : toks.toksL (a ++ b) = toks.toksL a ++ toks.toksL b := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [toks.toksL, ih]

theorem pre_cons_ne {c : List Sexp} {s : List (List Sexp)} (h : s ≠ []) :
    pre (c :: s) = pre s ++ .lp :: toks.toksL c.reverse := by
  cases s with
  | nil => exact absurd rfl h
  | cons p s => simp [pre]

/-- **Soundness of the stack parser**: a result has exactly the tokens read, after those of
the open lists. -/
theorem parseStk_sound : ∀ (ts : List Tok) (stk : List (List Sexp)) (xs : List Sexp),
    stk ≠ [] → parseStk ts stk = some xs → toks.toksL xs = pre stk ++ ts
  | [], stk, xs, _, h => by
    match stk, h with
    | [cur], h => simp only [parseStk, Option.some.injEq] at h; subst h; simp [pre]
  | .lp :: ts, stk, xs, hne, h => by
    rw [parseStk] at h
    rw [parseStk_sound ts _ xs (by simp) h, pre_cons_ne hne]
    simp [toks.toksL]
  | .rp :: ts, stk, xs, _, h => by
    match stk, h with
    | cur :: parent :: s, h =>
      rw [parseStk] at h
      rw [parseStk_sound ts _ xs (by simp) h]
      cases s with
      | nil => simp [pre, toksL_append, toks, toks.toksL]
      | cons q s => simp [pre, toksL_append, toks, toks.toksL]
  | .atom a :: ts, stk, xs, _, h => by
    match stk, h with
    | cur :: s, h =>
      rw [parseStk] at h
      rw [parseStk_sound ts _ xs (by simp) h]
      cases s <;> simp [pre, toksL_append, toks, toks.toksL]
  | .str b :: ts, stk, xs, _, h => by
    match stk, h with
    | cur :: s, h =>
      rw [parseStk] at h
      rw [parseStk_sound ts _ xs (by simp) h]
      cases s <;> simp [pre, toksL_append, toks, toks.toksL]

/-- **The fast reader is the reader.** -/
theorem readF_eq : readF = Sexp.read := by
  funext s
  unfold readF Sexp.read
  rw [lexA_eq]
  cases hl : lex s.toList with
  | none => rfl
  | some ts =>
    simp only [Option.map_some, List.reverse_nil, List.nil_append, Option.bind_eq_bind,
      Option.bind_some]
    split
    · next xs hp =>
      have := parseStk_sound ts [[]] xs (by simp) hp
      simp only [pre, List.reverse_nil, toks.toksL, List.append_nil, List.nil_append] at this
      rw [← this, Sexp.parseTop_toksL]
    · rfl

theorem readXF_eq : readXF = Wat.readX := by
  funext s
  simp only [readXF, Wat.readX, Wat.read, readF_eq]
  split
  · next x hx => cases h : Wat.ofSexp x <;> simp [hx, h]
  · next hx => split <;> simp_all

/-! ## The fast encoder -/

open Silmaril.Wasm.Component.BinaryP3 (Section Ast)

theorem mk_append_mk (a b : List UInt8) :
    ByteArray.mk a.toArray ++ ByteArray.mk b.toArray = ByteArray.mk (a ++ b).toArray :=
  ByteArray.ext (by simp)

theorem mk_append_bytes (a : List UInt8) (m : ByteArray) :
    ByteArray.mk a.toArray ++ m = ByteArray.mk (a ++ m.data.toList).toArray :=
  ByteArray.ext (by simp)

/-- One section: `secF` is the encoder's section. -/
theorem secF_eq (s : Section) :
    secF s = (Silmaril.Wasm.Component.BinaryP3.Encode.section_ s).map fun l => ByteArray.mk l.toArray := by
  cases s with
  | coreModule m =>
    simp only [secF, Silmaril.Wasm.Component.BinaryP3.Encode.section_, Silmaril.Parse.ByteParse.Enc.sized]
    have hl : m.data.toList.length = m.size := by simp
    rw [hl]
    cases Silmaril.Parse.ByteParse.Enc.u32 m.size <;> simp [mk_append_bytes]
  | custom n d =>
    simp only [secF, Silmaril.Wasm.Component.BinaryP3.Encode.section_, Silmaril.Parse.ByteParse.Enc.sized]
    simp only [Silmaril.Wasm.Component.Binary.Encode.name]
    cases Silmaril.Parse.ByteParse.Enc.name n with
    | none => rfl
    | some a =>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.map_bind, mk_append_bytes]
      have hl : (a ++ d.data.toList).length = a.length + d.size := by simp
      rw [hl]
      cases Silmaril.Parse.ByteParse.Enc.u32 (a.length + d.size) <;> simp
  | _ => rfl

theorem secsF_eq (acc : ByteArray) (ss : List Section) :
    secsF acc ss = (Silmaril.Wasm.Component.BinaryP3.Encode.sections ss).map
      fun l => acc ++ ByteArray.mk l.toArray := by
  induction ss generalizing acc with
  | nil => simp [secsF, Silmaril.Wasm.Component.BinaryP3.Encode.sections, ByteArray.ext_iff]
  | cons s ss ih =>
    simp only [secsF, Silmaril.Wasm.Component.BinaryP3.Encode.sections, secF_eq]
    cases Silmaril.Wasm.Component.BinaryP3.Encode.section_ s with
    | none => rfl
    | some a =>
      simp only [Option.map_some, ih, Option.bind_eq_bind, Option.bind_some]
      cases Silmaril.Wasm.Component.BinaryP3.Encode.sections ss <;>
        simp [ByteArray.append_assoc, mk_append_mk]

/-- **The fast encoder is the encoder.** -/
theorem encodeF_eq : encodeF = Silmaril.Wasm.Component.BinaryP3.encode := by
  funext c
  cases c with
  | mk ss =>
    simp only [encodeF, secsF_eq, Silmaril.Wasm.Component.BinaryP3.encode,
      Silmaril.Wasm.Component.BinaryP3.Encode.ast]
    cases Silmaril.Wasm.Component.BinaryP3.Encode.sections ss <;> simp [mk_append_mk]

/-- **The fast `parse` is `parse`.** -/
theorem parseTextF_eq : parseTextF = Wat.parseText := by
  funext t
  simp only [parseTextF, readXF_eq, encodeF_eq]
  rfl

end Silmaril.Wasm.Tools.Component.FastRead
