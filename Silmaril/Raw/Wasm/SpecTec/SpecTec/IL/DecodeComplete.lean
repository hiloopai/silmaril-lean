module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Decode
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.EscapeFacts

/-!
# The decoder accepts nothing but printed forms

`Silmaril/SpecTec/IL/Decode.lean` defines a total `decodeDef? : SExp → Option
IL.Def`.  This file proves that it is *sound* for the encoding relation
`fun s d => defS d = s`: whenever `decodeDef? s = some d`, the S-expression `s`
is literally what `Silmaril/SpecTec/IL/Print.lean` prints for `d`.

```
theorem defS_of_decodeDef? : decodeDef? s = some d → defS d = s
theorem scriptS_of_decodeScript? : decodeScript? ss = some s → scriptS s = ss
```

The corollaries `decodeDef?_eq_none_of_ne` and `decodeScript?_eq_none_of_ne`
restate this as a rejection property: anything outside the image of `defS`
(resp. `scriptS`) is turned down.  The companion file `DecodeSound.lean` proves
the converse, `decodeDef? (defS d) = some d`; the two together say the
decoder's domain is *exactly* that image.

## Shape of the proof

There is one theorem per decoder.  The eight leaf decoders, `decodeText?`
through `decodeOpTyp?`, are not recursive and come first; the remaining 37 form
a single `mutual` block in which every theorem recurses *structurally on its
`SExp` or `List SExp` argument* — exactly as the decoders do, so Lean accepts
the group with no termination measure.  Each proof unfolds its decoder with the
`eq_def` lemma, `split`s on the resulting `match`, inverts the `Option`
plumbing of the surviving branch and rewrites with the induction hypotheses;
the branches `Decode.lean` sends to `none` are discharged by `none ≠ some _`.

The two load-bearing statements are `decodeArgsRest?_sound` and
`decodeParamsRest?_sound`, which cover the concatenated `param`/`arg` prefixes
that `print.ml` emits with no separators.  Neither claims the split they find
is *canonical*: all that is needed here — and all that holds without the
disjointness argument in `Decode.lean`'s docstring — is that re-printing the
pieces concatenates back to the original child list.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL

open Silmaril.SpecTec (SExp)

/-- Invert the `Option` plumbing of a decoder branch: turn a chain of binds,
maps, `if`/`dite` guards and `pure`s equated to `some _` into nested
existentials and plain equations, reducing any `match` on a tuple on the way.
The simp set is deliberately a superset of what a single branch needs. -/
local macro "inv " h:ident : tactic =>
  `(tactic| try simp only [bind, pure, Option.bind_eq_some_iff, Option.map_eq_some_iff,
      Option.pure_def, Option.some.injEq, Option.ite_none_right_eq_some,
      Option.dite_none_right_eq_some, Prod.mk.injEq, List.isEmpty_iff] at $h:ident)

/-- Right-associate `++` in the goal, so that the conclusions of
`decodeArgsRest?_sound` and `decodeParamsRest?_sound` match it syntactically. -/
local macro "flattenGoal" : tactic =>
  `(tactic| try simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil])

/-- Right-associate `++` in a hypothesis, discarding the `argsS []` and
`paramsS []` that an empty prefix contributes. -/
local macro "flattenAt " h:ident : tactic =>
  `(tactic| try simp only [argsS, paramsS, List.append_assoc, List.cons_append,
      List.nil_append, List.append_nil] at $h:ident)

/-! ## Leaves

`print.ml:11-20,25-69` renders booleans, identifiers, numerals, operators and
operator types as single atoms or shallow nodes; these are the base cases of
the recursion below. -/

/-- `decodeText?` accepts only the atoms `textS` produces (`print.ml:12`). -/
theorem textS_of_decodeText? {s : SExp} {v : String} (h : decodeText? s = some v) :
    textS v = s := by
  rw [decodeText?.eq_def] at h
  split at h
  · exact congrArg SExp.atom (Escape.quote_of_unquote? h)
  · exact absurd h (by simp)

/-- `decodeBool?` accepts only the atoms `boolS` produces (`print.ml:11`). -/
theorem boolS_of_decodeBool? {s : SExp} {b : Bool} (h : decodeBool? s = some b) :
    boolS b = s := by
  rw [decodeBool?.eq_def] at h
  split at h
  case h_1 => obtain rfl := Option.some.inj h; rfl
  case h_2 => obtain rfl := Option.some.inj h; rfl
  all_goals exact absurd h (by simp)

/-- `decodeNum?` accepts only the nodes `numS` produces (`print.ml:16`).  In
the `rat` branch the decoder rebuilds a `Rat` from the parsed numerator and
denominator, whose `num` and `den` projections are that pair definitionally. -/
theorem numS_of_decodeNum? {s : SExp} {n : Num} (h : decodeNum? s = some n) :
    numS n = s := by
  rw [decodeNum?.eq_def] at h
  split at h
  case h_1 d =>
    inv h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [numS, Digits.decString_of_parseDecString? hv]
  case h_2 d =>
    inv h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [numS, Digits.signedString_of_parseSignedString? hv]
  case h_3 d =>
    inv h
    obtain ⟨⟨num, den⟩, hp, h⟩ := h
    inv h
    obtain ⟨_, rfl⟩ := h
    show SExp.node "rat" [SExp.atom (Digits.ratString num den)] = _
    rw [Digits.ratString_of_parseRatString? hp]
  case h_4 d => obtain rfl := Option.some.inj h; rfl
  all_goals exact absurd h (by simp)

/-- `decodeUnOp?` accepts only the atoms `unOpS` produces (`print.ml:25`). -/
theorem unOpS_of_decodeUnOp? {s : SExp} {op : UnOp} (h : decodeUnOp? s = some op) :
    unOpS op = s := by
  rw [decodeUnOp?.eq_def] at h
  split at h
  case h_1 => obtain rfl := Option.some.inj h; rfl
  case h_2 => obtain rfl := Option.some.inj h; rfl
  case h_3 => obtain rfl := Option.some.inj h; rfl
  all_goals exact absurd h (by simp)

/-- `decodeBinOp?` accepts only the atoms `binOpS` produces (`print.ml:32`). -/
theorem binOpS_of_decodeBinOp? {s : SExp} {op : BinOp} (h : decodeBinOp? s = some op) :
    binOpS op = s := by
  rw [decodeBinOp?.eq_def] at h
  split at h
  case h_1 => obtain rfl := Option.some.inj h; rfl
  case h_2 => obtain rfl := Option.some.inj h; rfl
  case h_3 => obtain rfl := Option.some.inj h; rfl
  case h_4 => obtain rfl := Option.some.inj h; rfl
  case h_5 => obtain rfl := Option.some.inj h; rfl
  case h_6 => obtain rfl := Option.some.inj h; rfl
  case h_7 => obtain rfl := Option.some.inj h; rfl
  case h_8 => obtain rfl := Option.some.inj h; rfl
  case h_9 => obtain rfl := Option.some.inj h; rfl
  case h_10 => obtain rfl := Option.some.inj h; rfl
  all_goals exact absurd h (by simp)

/-- `decodeCmpOp?` accepts only the atoms `cmpOpS` produces (`print.ml:44`). -/
theorem cmpOpS_of_decodeCmpOp? {s : SExp} {op : CmpOp} (h : decodeCmpOp? s = some op) :
    cmpOpS op = s := by
  rw [decodeCmpOp?.eq_def] at h
  split at h
  case h_1 => obtain rfl := Option.some.inj h; rfl
  case h_2 => obtain rfl := Option.some.inj h; rfl
  case h_3 => obtain rfl := Option.some.inj h; rfl
  case h_4 => obtain rfl := Option.some.inj h; rfl
  case h_5 => obtain rfl := Option.some.inj h; rfl
  case h_6 => obtain rfl := Option.some.inj h; rfl
  all_goals exact absurd h (by simp)

/-- `decodeNumTyp?` accepts only the atoms `numTypS` produces
(`print.ml:65`). -/
theorem numTypS_of_decodeNumTyp? {s : SExp} {t : NumTyp} (h : decodeNumTyp? s = some t) :
    numTypS t = s := by
  rw [decodeNumTyp?.eq_def] at h
  split at h
  case h_1 => obtain rfl := Option.some.inj h; rfl
  case h_2 => obtain rfl := Option.some.inj h; rfl
  case h_3 => obtain rfl := Option.some.inj h; rfl
  case h_4 => obtain rfl := Option.some.inj h; rfl
  all_goals exact absurd h (by simp)

/-- `decodeOpTyp?` accepts only the atoms `opTypS` produces (`print.ml:67`). -/
theorem opTypS_of_decodeOpTyp? {s : SExp} {t : OpTyp} (h : decodeOpTyp? s = some t) :
    opTypS t = s := by
  rw [decodeOpTyp?.eq_def] at h
  split at h
  case h_1 => obtain rfl := Option.some.inj h; rfl
  all_goals
    inv h
    obtain ⟨t', ht, rfl⟩ := h
    simp only [opTypS, numTypS_of_decodeNumTyp? ht]

/-! ## The recursive group

Every theorem below recurses structurally on its `SExp` or `List SExp`
argument, mirroring the decoder it inverts. -/

-- The group below is a single declaration for the termination checker, so its
-- elaboration budget is shared by all 37 proofs; `expS_of_decodeExp?` alone has
-- thirty cases.
set_option maxHeartbeats 600000 in
mutual

/-- `decodeIter?` accepts only what `iterS` prints (`print.ml:55`). -/
theorem iterS_of_decodeIter? : ∀ {s : SExp} {it : Iter},
    decodeIter? s = some it → iterS it = s := by
  intro s it h
  rw [decodeIter?.eq_def] at h
  split at h
  case h_1 => obtain rfl := Option.some.inj h; rfl
  case h_2 => obtain rfl := Option.some.inj h; rfl
  case h_3 => obtain rfl := Option.some.inj h; rfl
  case h_4 e =>
    inv h
    obtain ⟨e', he, rfl⟩ := h
    simp only [iterS, expS_of_decodeExp? he]
  case h_5 e x =>
    inv h
    obtain ⟨e', he, x', hx, rfl⟩ := h
    simp only [iterS, expS_of_decodeExp? he, textS_of_decodeText? hx]
  all_goals exact absurd h (by simp)

/-- `decodeIterExp?` accepts only what `iterExpS` prints (`print.ml:140`). -/
theorem iterExpS_of_decodeIterExp? : ∀ {ks : List SExp} {ie : IterExp},
    decodeIterExp? ks = some ie → iterExpS ie = ks := by
  intro ks ie h
  rw [decodeIterExp?.eq_def] at h
  split at h
  · exact absurd h (by simp)
  · rename_i it ds
    inv h
    obtain ⟨it', hit, ds', hds, rfl⟩ := h
    simp only [iterExpS, iterS_of_decodeIter? hit, domsS_of_decodeDoms? hds]

/-- `decodeDoms?` accepts only what `domsS` prints (`print.ml:141`). -/
theorem domsS_of_decodeDoms? : ∀ {ks : List SExp} {ds : List Dom},
    decodeDoms? ks = some ds → domsS ds = ks := by
  intro ks ds h
  rw [decodeDoms?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i d ks'
    inv h
    obtain ⟨d', hd, ds', hds, rfl⟩ := h
    simp only [domsS, domS_of_decodeDom? hd, domsS_of_decodeDoms? hds]

/-- `decodeDom?` accepts only what `domS` prints (`print.ml:141`). -/
theorem domS_of_decodeDom? : ∀ {s : SExp} {d : Dom},
    decodeDom? s = some d → domS d = s := by
  intro s d h
  rw [decodeDom?.eq_def] at h
  split at h
  case h_1 x e =>
    inv h
    obtain ⟨x', hx, e', he, rfl⟩ := h
    simp only [domS, textS_of_decodeText? hx, expS_of_decodeExp? he]
  all_goals exact absurd h (by simp)

/-- `decodeTyp?` accepts only what `typS` prints (`print.ml:71`). -/
theorem typS_of_decodeTyp? : ∀ {s : SExp} {t : Typ},
    decodeTyp? s = some t → typS t = s := by
  intro s t h
  rw [decodeTyp?.eq_def] at h
  split at h
  case h_1 => obtain rfl := Option.some.inj h; rfl
  case h_2 => obtain rfl := Option.some.inj h; rfl
  case h_3 => obtain rfl := Option.some.inj h; rfl
  case h_4 => obtain rfl := Option.some.inj h; rfl
  case h_5 => obtain rfl := Option.some.inj h; rfl
  case h_6 => obtain rfl := Option.some.inj h; rfl
  case h_7 x args =>
    inv h
    obtain ⟨x', hx, args', hargs, rfl⟩ := h
    simp only [typS, textS_of_decodeText? hx, argsS_of_decodeArgs? hargs]
  case h_8 binds =>
    inv h
    obtain ⟨bs, hbs, rfl⟩ := h
    simp only [typS, typBindsS_of_decodeTypBinds? hbs]
  case h_9 t' it =>
    inv h
    obtain ⟨t'', ht, it', hit, rfl⟩ := h
    simp only [typS, typS_of_decodeTyp? ht, iterS_of_decodeIter? hit]
  all_goals exact absurd h (by simp)

/-- `decodeTypBinds?` accepts only what `typBindsS` prints (`print.ml:77`). -/
theorem typBindsS_of_decodeTypBinds? : ∀ {ks : List SExp} {bs : List TypBind},
    decodeTypBinds? ks = some bs → typBindsS bs = ks := by
  intro ks bs h
  rw [decodeTypBinds?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i b ks'
    inv h
    obtain ⟨b', hb, bs', hbs, rfl⟩ := h
    simp only [typBindsS, typBindS_of_decodeTypBind? hb, typBindsS_of_decodeTypBinds? hbs]

/-- `decodeTypBind?` accepts only what `typBindS` prints (`print.ml:86`). -/
theorem typBindS_of_decodeTypBind? : ∀ {s : SExp} {b : TypBind},
    decodeTypBind? s = some b → typBindS b = s := by
  intro s b h
  rw [decodeTypBind?.eq_def] at h
  split at h
  case h_1 x t =>
    inv h
    obtain ⟨x', hx, t', ht, rfl⟩ := h
    simp only [typBindS, textS_of_decodeText? hx, typS_of_decodeTyp? ht]
  all_goals exact absurd h (by simp)

/-- `decodeDefTyp?` accepts only what `defTypS` prints (`print.ml:80`). -/
theorem defTypS_of_decodeDefTyp? : ∀ {s : SExp} {dt : DefTyp},
    decodeDefTyp? s = some dt → defTypS dt = s := by
  intro s dt h
  rw [decodeDefTyp?.eq_def] at h
  split at h
  case h_1 t =>
    inv h
    obtain ⟨t', ht, rfl⟩ := h
    simp only [defTypS, typS_of_decodeTyp? ht]
  case h_2 fs =>
    inv h
    obtain ⟨fs', hfs, rfl⟩ := h
    simp only [defTypS, typFieldsS_of_decodeTypFields? hfs]
  case h_3 cs =>
    inv h
    obtain ⟨cs', hcs, rfl⟩ := h
    simp only [defTypS, typCasesS_of_decodeTypCases? hcs]
  all_goals exact absurd h (by simp)

/-- `decodeTypFields?` accepts only what `typFieldsS` prints (`print.ml:83`). -/
theorem typFieldsS_of_decodeTypFields? : ∀ {ks : List SExp} {fs : List TypField},
    decodeTypFields? ks = some fs → typFieldsS fs = ks := by
  intro ks fs h
  rw [decodeTypFields?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i f ks'
    inv h
    obtain ⟨f', hf, fs', hfs, rfl⟩ := h
    simp only [typFieldsS, typFieldS_of_decodeTypField? hf,
      typFieldsS_of_decodeTypFields? hfs]

/-- `decodeTypField?` accepts only what `typFieldS` prints (`print.ml:89`). -/
theorem typFieldS_of_decodeTypField? : ∀ {s : SExp} {f : TypField},
    decodeTypField? s = some f → typFieldS f = s := by
  intro s f h
  rw [decodeTypField?.eq_def] at h
  split at h
  case h_1 a t rest =>
    inv h
    obtain ⟨a', ha, t', ht, ⟨quants, args, tail⟩, hp, h⟩ := h
    inv h
    obtain ⟨rfl, prems, hpr, rfl⟩ := h
    have hps := decodeParamsRest?_sound hp
    flattenAt hps
    simp only [typFieldS, textS_of_decodeText? ha, typS_of_decodeTyp? ht,
      premsS_of_decodePrems? hpr, hps]
  all_goals exact absurd h (by simp)

/-- `decodeTypCases?` accepts only what `typCasesS` prints (`print.ml:84`). -/
theorem typCasesS_of_decodeTypCases? : ∀ {ks : List SExp} {cs : List TypCase},
    decodeTypCases? ks = some cs → typCasesS cs = ks := by
  intro ks cs h
  rw [decodeTypCases?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i c ks'
    inv h
    obtain ⟨c', hc, cs', hcs, rfl⟩ := h
    simp only [typCasesS, typCaseS_of_decodeTypCase? hc, typCasesS_of_decodeTypCases? hcs]

/-- `decodeTypCase?` accepts only what `typCaseS` prints (`print.ml:92`). -/
theorem typCaseS_of_decodeTypCase? : ∀ {s : SExp} {c : TypCase},
    decodeTypCase? s = some c → typCaseS c = s := by
  intro s c h
  rw [decodeTypCase?.eq_def] at h
  split at h
  case h_1 op t rest =>
    inv h
    obtain ⟨op', hop, t', ht, ⟨quants, args, tail⟩, hp, h⟩ := h
    inv h
    obtain ⟨rfl, prems, hpr, rfl⟩ := h
    have hps := decodeParamsRest?_sound hp
    flattenAt hps
    simp only [typCaseS, textS_of_decodeText? hop, typS_of_decodeTyp? ht,
      premsS_of_decodePrems? hpr, hps]
  all_goals exact absurd h (by simp)

/-- `decodeExp?` accepts only what `expS` prints (`print.ml:98`). -/
theorem expS_of_decodeExp? : ∀ {s : SExp} {e : Exp},
    decodeExp? s = some e → expS e = s := by
  intro s e h
  rw [decodeExp?.eq_def] at h
  split at h
  case h_1 x =>
    inv h
    obtain ⟨x', hx, rfl⟩ := h
    simp only [expS, textS_of_decodeText? hx]
  case h_2 b =>
    inv h
    obtain ⟨b', hb, rfl⟩ := h
    simp only [expS, boolS_of_decodeBool? hb]
  case h_3 n =>
    inv h
    obtain ⟨n', hn, rfl⟩ := h
    simp only [expS, numS_of_decodeNum? hn]
  case h_4 t =>
    inv h
    obtain ⟨t', ht, rfl⟩ := h
    simp only [expS, textS_of_decodeText? ht]
  case h_5 op t e₁ =>
    inv h
    obtain ⟨op', hop, t', ht, e', he, rfl⟩ := h
    simp only [expS, unOpS_of_decodeUnOp? hop, opTypS_of_decodeOpTyp? ht,
      expS_of_decodeExp? he]
  case h_6 op t e₁ e₂ =>
    inv h
    obtain ⟨op', hop, t', ht, e₁', h₁, e₂', h₂, rfl⟩ := h
    simp only [expS, binOpS_of_decodeBinOp? hop, opTypS_of_decodeOpTyp? ht,
      expS_of_decodeExp? h₁, expS_of_decodeExp? h₂]
  case h_7 op t e₁ e₂ =>
    inv h
    obtain ⟨op', hop, t', ht, e₁', h₁, e₂', h₂, rfl⟩ := h
    simp only [expS, cmpOpS_of_decodeCmpOp? hop, opTypS_of_decodeOpTyp? ht,
      expS_of_decodeExp? h₁, expS_of_decodeExp? h₂]
  case h_8 e₁ e₂ =>
    inv h
    obtain ⟨e₁', h₁, e₂', h₂, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁, expS_of_decodeExp? h₂]
  case h_9 e₁ e₂ e₃ =>
    inv h
    obtain ⟨e₁', h₁, e₂', h₂, e₃', h₃, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁, expS_of_decodeExp? h₂, expS_of_decodeExp? h₃]
  case h_10 e₁ p e₂ =>
    inv h
    obtain ⟨e₁', h₁, p', hp, e₂', h₂, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁, pathS_of_decodePath? hp, expS_of_decodeExp? h₂]
  case h_11 e₁ p e₂ =>
    inv h
    obtain ⟨e₁', h₁, p', hp, e₂', h₂, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁, pathS_of_decodePath? hp, expS_of_decodeExp? h₂]
  case h_12 fs =>
    inv h
    obtain ⟨fs', hfs, rfl⟩ := h
    simp only [expS, expFieldsS_of_decodeExpFields? hfs]
  case h_13 e₁ a =>
    inv h
    obtain ⟨e₁', h₁, a', ha, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁, textS_of_decodeText? ha]
  case h_14 e₁ e₂ =>
    inv h
    obtain ⟨e₁', h₁, e₂', h₂, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁, expS_of_decodeExp? h₂]
  case h_15 e₁ e₂ =>
    inv h
    obtain ⟨e₁', h₁, e₂', h₂, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁, expS_of_decodeExp? h₂]
  case h_16 e₁ =>
    inv h
    obtain ⟨e₁', h₁, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁]
  case h_17 es =>
    inv h
    obtain ⟨es', hes, rfl⟩ := h
    simp only [expS, expsS_of_decodeExps? hes]
  case h_18 x args =>
    inv h
    obtain ⟨x', hx, args', hargs, rfl⟩ := h
    simp only [expS, textS_of_decodeText? hx, argsS_of_decodeArgs? hargs]
  case h_19 e₁ rest =>
    inv h
    obtain ⟨e₁', h₁, it, hit, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁, iterExpS_of_decodeIterExp? hit]
  case h_20 e₁ i =>
    inv h
    obtain ⟨e₁', h₁, i', hi, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁, Digits.intString_of_parseIntString? hi]
  case h_21 op e₁ =>
    inv h
    obtain ⟨op', hop, e₁', h₁, rfl⟩ := h
    simp only [expS, textS_of_decodeText? hop, expS_of_decodeExp? h₁]
  case h_22 e₁ op =>
    inv h
    obtain ⟨e₁', h₁, op', hop, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁, textS_of_decodeText? hop]
  case h_23 => obtain rfl := Option.some.inj h; rfl
  case h_24 e₁ =>
    inv h
    obtain ⟨e₁', h₁, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁]
  case h_25 e₁ =>
    inv h
    obtain ⟨e₁', h₁, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁]
  case h_26 es =>
    inv h
    obtain ⟨es', hes, rfl⟩ := h
    simp only [expS, expsS_of_decodeExps? hes]
  case h_27 e₁ =>
    inv h
    obtain ⟨e₁', h₁, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁]
  case h_28 e₁ e₂ =>
    inv h
    obtain ⟨e₁', h₁, e₂', h₂, rfl⟩ := h
    simp only [expS, expS_of_decodeExp? h₁, expS_of_decodeExp? h₂]
  case h_29 t₁ t₂ e₁ =>
    inv h
    obtain ⟨t₁', ht₁, t₂', ht₂, e₁', h₁, rfl⟩ := h
    simp only [expS, numTypS_of_decodeNumTyp? ht₁, numTypS_of_decodeNumTyp? ht₂,
      expS_of_decodeExp? h₁]
  case h_30 t₁ t₂ e₁ =>
    inv h
    obtain ⟨t₁', ht₁, t₂', ht₂, e₁', h₁, rfl⟩ := h
    simp only [expS, typS_of_decodeTyp? ht₁, typS_of_decodeTyp? ht₂, expS_of_decodeExp? h₁]
  all_goals exact absurd h (by simp)

/-- `decodeExps?` accepts only what `expsS` prints (`print.ml:116`). -/
theorem expsS_of_decodeExps? : ∀ {ks : List SExp} {es : List Exp},
    decodeExps? ks = some es → expsS es = ks := by
  intro ks es h
  rw [decodeExps?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i e ks'
    inv h
    obtain ⟨e', he, es', hes, rfl⟩ := h
    simp only [expsS, expS_of_decodeExp? he, expsS_of_decodeExps? hes]

/-- `decodeExpFields?` accepts only what `expFieldsS` prints
(`print.ml:111`). -/
theorem expFieldsS_of_decodeExpFields? : ∀ {ks : List SExp} {fs : List ExpField},
    decodeExpFields? ks = some fs → expFieldsS fs = ks := by
  intro ks fs h
  rw [decodeExpFields?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i f ks'
    inv h
    obtain ⟨f', hf, fs', hfs, rfl⟩ := h
    simp only [expFieldsS, expFieldS_of_decodeExpField? hf,
      expFieldsS_of_decodeExpFields? hfs]

/-- `decodeExpField?` accepts only what `expFieldS` prints (`print.ml:130`). -/
theorem expFieldS_of_decodeExpField? : ∀ {s : SExp} {f : ExpField},
    decodeExpField? s = some f → expFieldS f = s := by
  intro s f h
  rw [decodeExpField?.eq_def] at h
  split at h
  case h_1 a e =>
    inv h
    obtain ⟨a', ha, e', he, rfl⟩ := h
    simp only [expFieldS, textS_of_decodeText? ha, expS_of_decodeExp? he]
  all_goals exact absurd h (by simp)

/-- `decodePath?` accepts only what `pathS` prints (`print.ml:133`). -/
theorem pathS_of_decodePath? : ∀ {s : SExp} {p : Path},
    decodePath? s = some p → pathS p = s := by
  intro s p h
  rw [decodePath?.eq_def] at h
  split at h
  case h_1 => obtain rfl := Option.some.inj h; rfl
  case h_2 p₁ e =>
    inv h
    obtain ⟨p', hp, e', he, rfl⟩ := h
    simp only [pathS, pathS_of_decodePath? hp, expS_of_decodeExp? he]
  case h_3 p₁ e₁ e₂ =>
    inv h
    obtain ⟨p', hp, e₁', h₁, e₂', h₂, rfl⟩ := h
    simp only [pathS, pathS_of_decodePath? hp, expS_of_decodeExp? h₁, expS_of_decodeExp? h₂]
  case h_4 p₁ a =>
    inv h
    obtain ⟨p', hp, a', ha, rfl⟩ := h
    simp only [pathS, pathS_of_decodePath? hp, textS_of_decodeText? ha]
  all_goals exact absurd h (by simp)

/-- `decodeSym?` accepts only what `symS` prints (`print.ml:146`). -/
theorem symS_of_decodeSym? : ∀ {s : SExp} {g : Sym},
    decodeSym? s = some g → symS g = s := by
  intro s g h
  rw [decodeSym?.eq_def] at h
  split at h
  case h_1 => obtain rfl := Option.some.inj h; rfl
  case h_2 x args =>
    inv h
    obtain ⟨x', hx, args', hargs, rfl⟩ := h
    simp only [symS, textS_of_decodeText? hx, argsS_of_decodeArgs? hargs]
  case h_3 n =>
    inv h
    obtain ⟨n', hn, rfl⟩ := h
    simp only [symS, Digits.hexByteString_of_parseHexByteString? hn]
  case h_4 t =>
    inv h
    obtain ⟨t', ht, rfl⟩ := h
    simp only [symS, textS_of_decodeText? ht]
  case h_5 gs =>
    inv h
    obtain ⟨gs', hgs, rfl⟩ := h
    simp only [symS, symsS_of_decodeSyms? hgs]
  case h_6 gs =>
    inv h
    obtain ⟨gs', hgs, rfl⟩ := h
    simp only [symS, symsS_of_decodeSyms? hgs]
  case h_7 g₁ g₂ =>
    inv h
    obtain ⟨g₁', h₁, g₂', h₂, rfl⟩ := h
    simp only [symS, symS_of_decodeSym? h₁, symS_of_decodeSym? h₂]
  case h_8 g₁ rest =>
    inv h
    obtain ⟨g₁', h₁, it, hit, rfl⟩ := h
    simp only [symS, symS_of_decodeSym? h₁, iterExpS_of_decodeIterExp? hit]
  case h_9 e g₁ =>
    inv h
    obtain ⟨e', he, g₁', h₁, rfl⟩ := h
    simp only [symS, expS_of_decodeExp? he, symS_of_decodeSym? h₁]
  all_goals exact absurd h (by simp)

/-- `decodeSyms?` accepts only what `symsS` prints (`print.ml:152`). -/
theorem symsS_of_decodeSyms? : ∀ {ks : List SExp} {gs : List Sym},
    decodeSyms? ks = some gs → symsS gs = ks := by
  intro ks gs h
  rw [decodeSyms?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i g ks'
    inv h
    obtain ⟨g', hg, gs', hgs, rfl⟩ := h
    simp only [symsS, symS_of_decodeSym? hg, symsS_of_decodeSyms? hgs]

/-- `decodePrem?` accepts only what `premS` prints (`print.ml:161`). -/
theorem premS_of_decodePrem? : ∀ {s : SExp} {p : Prem},
    decodePrem? s = some p → premS p = s := by
  intro s p h
  rw [decodePrem?.eq_def] at h
  split at h
  case h_1 => obtain rfl := Option.some.inj h; rfl
  case h_2 x rest =>
    inv h
    obtain ⟨x', hx, ⟨args, tail⟩, har, h⟩ := h
    inv h
    split at h
    case h_1 op e =>
      inv h
      obtain ⟨op', hop, e', he, rfl⟩ := h
      simp only [premS, textS_of_decodeText? hx, textS_of_decodeText? hop,
        expS_of_decodeExp? he, decodeArgsRest?_sound har]
    all_goals exact absurd h (by simp)
  case h_3 e =>
    inv h
    obtain ⟨e', he, rfl⟩ := h
    simp only [premS, expS_of_decodeExp? he]
  case h_4 e₁ e₂ =>
    inv h
    obtain ⟨e₁', h₁, e₂', h₂, rfl⟩ := h
    simp only [premS, expS_of_decodeExp? h₁, expS_of_decodeExp? h₂]
  case h_5 p₁ rest =>
    inv h
    obtain ⟨p₁', h₁, it, hit, rfl⟩ := h
    simp only [premS, premS_of_decodePrem? h₁, iterExpS_of_decodeIterExp? hit]
  all_goals exact absurd h (by simp)

/-- `decodePrems?` accepts only what `premsS` prints (`print.ml:90`). -/
theorem premsS_of_decodePrems? : ∀ {ks : List SExp} {ps : List Prem},
    decodePrems? ks = some ps → premsS ps = ks := by
  intro ks ps h
  rw [decodePrems?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i p ks'
    inv h
    obtain ⟨p', hp, ps', hps, rfl⟩ := h
    simp only [premsS, premS_of_decodePrem? hp, premsS_of_decodePrems? hps]

/-- `decodeArg?` accepts only what `argS` prints (`print.ml:172`). -/
theorem argS_of_decodeArg? : ∀ {s : SExp} {a : Arg},
    decodeArg? s = some a → argS a = s := by
  intro s a h
  rw [decodeArg?.eq_def] at h
  split at h
  case h_1 e =>
    inv h
    obtain ⟨e', he, rfl⟩ := h
    simp only [argS, expS_of_decodeExp? he]
  case h_2 t =>
    inv h
    obtain ⟨t', ht, rfl⟩ := h
    simp only [argS, typS_of_decodeTyp? ht]
  case h_3 x =>
    inv h
    obtain ⟨x', hx, rfl⟩ := h
    simp only [argS, textS_of_decodeText? hx]
  case h_4 g =>
    inv h
    obtain ⟨g', hg, rfl⟩ := h
    simp only [argS, symS_of_decodeSym? hg]
  all_goals exact absurd h (by simp)

/-- `decodeArgs?` accepts only what `argsS` prints (`print.ml:173`). -/
theorem argsS_of_decodeArgs? : ∀ {ks : List SExp} {as : List Arg},
    decodeArgs? ks = some as → argsS as = ks := by
  intro ks as h
  rw [decodeArgs?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i a ks'
    inv h
    obtain ⟨a', ha, as', has, rfl⟩ := h
    simp only [argsS, argS_of_decodeArg? ha, argsS_of_decodeArgs? has]

/-- Whatever prefix `decodeArgsRest?` reads, re-printing the arguments and
appending the remainder recovers the original children. -/
theorem decodeArgsRest?_sound : ∀ {ks : List SExp} {as : List Arg} {rest : List SExp},
    decodeArgsRest? ks = some (as, rest) → argsS as ++ rest = ks := by
  intro ks as rest h
  rw [decodeArgsRest?.eq_def] at h
  split at h
  · inv h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · rename_i k ks'
    split at h
    · inv h
      obtain ⟨a', ha, ⟨as', rest'⟩, har, h⟩ := h
      inv h
      obtain ⟨rfl, rfl⟩ := h
      simp only [argsS, List.cons_append, argS_of_decodeArg? ha, decodeArgsRest?_sound har]
    · inv h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-- Whatever prefix `decodeParamsRest?` reads, re-printing the parameters and
arguments and appending the remainder recovers the original children. -/
theorem decodeParamsRest?_sound : ∀ {ks : List SExp} {ps : List Param} {as : List Arg}
    {rest : List SExp}, decodeParamsRest? ks = some (ps, as, rest) →
    paramsS ps ++ argsS as ++ rest = ks := by
  intro ks ps as rest h
  rw [decodeParamsRest?.eq_def] at h
  split at h
  · inv h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · rename_i k ks'
    split at h
    · inv h
      obtain ⟨p', hp, ⟨ps', as', rest'⟩, hr, h⟩ := h
      inv h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [paramsS, List.cons_append, paramS_of_decodeParam? hp,
        decodeParamsRest?_sound hr]
    · split at h
      · inv h
        obtain ⟨a', ha, ⟨as', rest'⟩, har, h⟩ := h
        inv h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [paramsS, argsS, List.nil_append, List.cons_append,
          argS_of_decodeArg? ha, decodeArgsRest?_sound har]
      · inv h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl

/-- `decodeParam?` accepts only what `paramS` prints (`print.ml:179`). -/
theorem paramS_of_decodeParam? : ∀ {s : SExp} {p : Param},
    decodeParam? s = some p → paramS p = s := by
  intro s p h
  rw [decodeParam?.eq_def] at h
  split at h
  case h_1 x t =>
    inv h
    obtain ⟨x', hx, t', ht, rfl⟩ := h
    simp only [paramS, textS_of_decodeText? hx, typS_of_decodeTyp? ht]
  case h_2 x =>
    inv h
    obtain ⟨x', hx, rfl⟩ := h
    simp only [paramS, textS_of_decodeText? hx]
  case h_3 x rest =>
    inv h
    obtain ⟨x', hx, ⟨ps', args, tail⟩, hp, h⟩ := h
    inv h
    split at h
    case h_1 t =>
      inv h
      obtain ⟨t', ht, rfl⟩ := h
      have hps := decodeParamsRest?_sound hp
      flattenAt hps
      simp only [paramS, textS_of_decodeText? hx, typS_of_decodeTyp? ht, hps]
    all_goals exact absurd h (by simp)
  case h_4 x rest =>
    inv h
    obtain ⟨x', hx, ⟨ps', args, tail⟩, hp, h⟩ := h
    inv h
    split at h
    case h_1 t =>
      inv h
      obtain ⟨t', ht, rfl⟩ := h
      have hps := decodeParamsRest?_sound hp
      flattenAt hps
      simp only [paramS, textS_of_decodeText? hx, typS_of_decodeTyp? ht, hps]
    all_goals exact absurd h (by simp)
  all_goals exact absurd h (by simp)

/-- `decodeParams?` accepts only what `paramsS` prints (`print.ml:183`). -/
theorem paramsS_of_decodeParams? : ∀ {ks : List SExp} {ps : List Param},
    decodeParams? ks = some ps → paramsS ps = ks := by
  intro ks ps h
  rw [decodeParams?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i p ks'
    inv h
    obtain ⟨p', hp, ps', hps, rfl⟩ := h
    simp only [paramsS, paramS_of_decodeParam? hp, paramsS_of_decodeParams? hps]

/-- `decodeInst?` accepts only what `instS` prints (`print.ml:186`). -/
theorem instS_of_decodeInst? : ∀ {s : SExp} {i : Inst},
    decodeInst? s = some i → instS i = s := by
  intro s i h
  rw [decodeInst?.eq_def] at h
  split at h
  case h_1 ks =>
    inv h
    obtain ⟨⟨quants, args, tail⟩, hp, h⟩ := h
    inv h
    split at h
    case h_1 dt =>
      inv h
      obtain ⟨dt', hdt, rfl⟩ := h
      have hps := decodeParamsRest?_sound hp
      flattenAt hps
      simp only [instS, defTypS_of_decodeDefTyp? hdt]
      flattenGoal
      rw [hps]
    all_goals exact absurd h (by simp)
  all_goals exact absurd h (by simp)

/-- `decodeInsts?` accepts only what `instsS` prints (`print.ml:209`). -/
theorem instsS_of_decodeInsts? : ∀ {ks : List SExp} {is : List Inst},
    decodeInsts? ks = some is → instsS is = ks := by
  intro ks is h
  rw [decodeInsts?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i i ks'
    inv h
    obtain ⟨i', hi, is', his, rfl⟩ := h
    simp only [instsS, instS_of_decodeInst? hi, instsS_of_decodeInsts? his]

/-- `decodeRule?` accepts only what `ruleS` prints (`print.ml:191`). -/
theorem ruleS_of_decodeRule? : ∀ {s : SExp} {r : Rule},
    decodeRule? s = some r → ruleS r = s := by
  intro s r h
  rw [decodeRule?.eq_def] at h
  split at h
  case h_1 x ks =>
    inv h
    obtain ⟨x', hx, ⟨quants, args, tail⟩, hp, h⟩ := h
    inv h
    obtain ⟨rfl, h⟩ := h
    split at h
    case h_1 op e prems =>
      inv h
      obtain ⟨op', hop, e', he, prems', hpr, rfl⟩ := h
      have hps := decodeParamsRest?_sound hp
      flattenAt hps
      simp only [ruleS, textS_of_decodeText? hx, textS_of_decodeText? hop,
        expS_of_decodeExp? he, premsS_of_decodePrems? hpr]
      flattenGoal
      rw [hps]
    all_goals exact absurd h (by simp)
  all_goals exact absurd h (by simp)

/-- `decodeRules?` accepts only what `rulesS` prints (`print.ml:211`). -/
theorem rulesS_of_decodeRules? : ∀ {ks : List SExp} {rs : List Rule},
    decodeRules? ks = some rs → rulesS rs = ks := by
  intro ks rs h
  rw [decodeRules?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i r ks'
    inv h
    obtain ⟨r', hr, rs', hrs, rfl⟩ := h
    simp only [rulesS, ruleS_of_decodeRule? hr, rulesS_of_decodeRules? hrs]

/-- `decodeClause?` accepts only what `clauseS` prints (`print.ml:196`). -/
theorem clauseS_of_decodeClause? : ∀ {s : SExp} {c : Clause},
    decodeClause? s = some c → clauseS c = s := by
  intro s c h
  rw [decodeClause?.eq_def] at h
  split at h
  case h_1 ks =>
    inv h
    obtain ⟨⟨quants, args, tail⟩, hp, h⟩ := h
    inv h
    split at h
    case h_1 e prems =>
      inv h
      obtain ⟨e', he, prems', hpr, rfl⟩ := h
      have hps := decodeParamsRest?_sound hp
      flattenAt hps
      simp only [clauseS, expS_of_decodeExp? he, premsS_of_decodePrems? hpr]
      flattenGoal
      rw [hps]
    all_goals exact absurd h (by simp)
  all_goals exact absurd h (by simp)

/-- `decodeClauses?` accepts only what `clausesS` prints (`print.ml:213`). -/
theorem clausesS_of_decodeClauses? : ∀ {ks : List SExp} {cs : List Clause},
    decodeClauses? ks = some cs → clausesS cs = ks := by
  intro ks cs h
  rw [decodeClauses?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i c ks'
    inv h
    obtain ⟨c', hc, cs', hcs, rfl⟩ := h
    simp only [clausesS, clauseS_of_decodeClause? hc, clausesS_of_decodeClauses? hcs]

/-- `decodeProd?` accepts only what `prodS` prints (`print.ml:201`). -/
theorem prodS_of_decodeProd? : ∀ {s : SExp} {p : Prod},
    decodeProd? s = some p → prodS p = s := by
  intro s p h
  rw [decodeProd?.eq_def] at h
  split at h
  case h_1 ks =>
    inv h
    obtain ⟨⟨quants, args, tail⟩, hp, h⟩ := h
    inv h
    obtain ⟨rfl, h⟩ := h
    split at h
    case h_1 g e prems =>
      inv h
      obtain ⟨g', hg, e', he, prems', hpr, rfl⟩ := h
      have hps := decodeParamsRest?_sound hp
      flattenAt hps
      simp only [prodS, symS_of_decodeSym? hg, expS_of_decodeExp? he,
        premsS_of_decodePrems? hpr]
      flattenGoal
      rw [hps]
    all_goals exact absurd h (by simp)
  all_goals exact absurd h (by simp)

/-- `decodeProds?` accepts only what `prodsS` prints (`print.ml:215`). -/
theorem prodsS_of_decodeProds? : ∀ {ks : List SExp} {ps : List Prod},
    decodeProds? ks = some ps → prodsS ps = ks := by
  intro ks ps h
  rw [decodeProds?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i p ks'
    inv h
    obtain ⟨p', hp, ps', hps, rfl⟩ := h
    simp only [prodsS, prodS_of_decodeProd? hp, prodsS_of_decodeProds? hps]

/-- `decodeDef?` accepts only what `defS` prints (`print.ml:206`). -/
theorem defS_of_decodeDef? : ∀ {s : SExp} {d : Def},
    decodeDef? s = some d → defS d = s := by
  intro s d h
  rw [decodeDef?.eq_def] at h
  split at h
  case h_1 x ks =>
    inv h
    obtain ⟨x', hx, ⟨ps, args, tail⟩, hp, h⟩ := h
    inv h
    obtain ⟨rfl, insts, hi, rfl⟩ := h
    have hps := decodeParamsRest?_sound hp
    flattenAt hps
    simp only [defS, textS_of_decodeText? hx, instsS_of_decodeInsts? hi, hps]
  case h_2 x ks =>
    inv h
    obtain ⟨x', hx, ⟨ps, args, tail⟩, hp, h⟩ := h
    inv h
    obtain ⟨rfl, h⟩ := h
    split at h
    case h_1 op t rules =>
      inv h
      obtain ⟨op', hop, t', ht, rules', hr, rfl⟩ := h
      have hps := decodeParamsRest?_sound hp
      flattenAt hps
      simp only [defS, textS_of_decodeText? hx, textS_of_decodeText? hop,
        typS_of_decodeTyp? ht, rulesS_of_decodeRules? hr]
      flattenGoal
      rw [hps]
    all_goals exact absurd h (by simp)
  case h_3 x ks =>
    inv h
    obtain ⟨x', hx, ⟨ps, args, tail⟩, hp, h⟩ := h
    inv h
    obtain ⟨rfl, h⟩ := h
    split at h
    case h_1 t clauses =>
      inv h
      obtain ⟨t', ht, clauses', hc, rfl⟩ := h
      have hps := decodeParamsRest?_sound hp
      flattenAt hps
      simp only [defS, textS_of_decodeText? hx, typS_of_decodeTyp? ht,
        clausesS_of_decodeClauses? hc]
      flattenGoal
      rw [hps]
    all_goals exact absurd h (by simp)
  case h_4 x ks =>
    inv h
    obtain ⟨x', hx, ⟨ps, args, tail⟩, hp, h⟩ := h
    inv h
    obtain ⟨rfl, h⟩ := h
    split at h
    case h_1 t prods =>
      inv h
      obtain ⟨t', ht, prods', hpd, rfl⟩ := h
      have hps := decodeParamsRest?_sound hp
      flattenAt hps
      simp only [defS, textS_of_decodeText? hx, typS_of_decodeTyp? ht,
        prodsS_of_decodeProds? hpd]
      flattenGoal
      rw [hps]
    all_goals exact absurd h (by simp)
  case h_5 ds =>
    inv h
    obtain ⟨ds', hd, rfl⟩ := h
    simp only [defS, defsS_of_decodeDefs? hd]
  all_goals exact absurd h (by simp)

/-- `decodeDefs?` accepts only what `defsS` prints (`print.ml:217`). -/
theorem defsS_of_decodeDefs? : ∀ {ks : List SExp} {ds : List Def},
    decodeDefs? ks = some ds → defsS ds = ks := by
  intro ks ds h
  rw [decodeDefs?.eq_def] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · rename_i d ks'
    inv h
    obtain ⟨d', hd, ds', hds, rfl⟩ := h
    simp only [defsS, defS_of_decodeDef? hd, defsS_of_decodeDefs? hds]

end

/-! ## Consequences -/

/-- `decodeScript?` accepts only what `scriptS` prints (`print.ml:224`). -/
theorem scriptS_of_decodeScript? {ss : List SExp} {s : Script}
    (h : decodeScript? ss = some s) : scriptS s = ss :=
  defsS_of_decodeDefs? h

/-- The decoder's domain is contained in the image of `defS`: an
S-expression that is not a printed definition is rejected. -/
theorem decodeDef?_eq_none_of_ne (s : SExp) (h : ∀ d, defS d ≠ s) :
    decodeDef? s = none := by
  cases hd : decodeDef? s with
  | none => rfl
  | some d => exact absurd (defS_of_decodeDef? hd) (h d)

/-- Everything the decoder accepts is a printed definition.  This is the half
of "`decodeDef?` succeeds exactly on the image of `defS`" that does not need
`DecodeSound.lean`. -/
theorem decodeDef?_isSome_imp {s : SExp} (h : (decodeDef? s).isSome) :
    ∃ d, defS d = s := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
  exact ⟨d, defS_of_decodeDef? hd⟩

/-- Likewise for whole scripts: nothing outside the image of `scriptS` is
accepted. -/
theorem decodeScript?_eq_none_of_ne (ss : List SExp) (h : ∀ s : Script, scriptS s ≠ ss) :
    decodeScript? ss = none := by
  cases hd : decodeScript? ss with
  | none => rfl
  | some s => exact absurd (scriptS_of_decodeScript? hd) (h s)

end Silmaril.SpecTec.IL
