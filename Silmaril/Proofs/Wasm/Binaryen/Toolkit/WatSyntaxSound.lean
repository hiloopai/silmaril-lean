module

public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntax

@[expose] public section

namespace Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat

open Silmaril Silmaril.Wasm Silmaril.Wasm.Text
open Silmaril.Wasm.Binaryen.Toolkit.Wat
open Silmaril.Formats.SExpEncoding (doc)

private theorem mapM_sound {α β : Type} {f : α → Option β} {R : β → α → Prop}
    (hf : ∀ a b, f a = some b → R b a) :
    ∀ {as bs}, as.mapM f = some bs → List.Forall₂ R bs as := by
  intro as
  induction as with
  | nil => intro bs h; cases h; exact .nil
  | cons a as ih =>
    intro bs h
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs', hbs, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .cons (hf a b hb) (ih hbs)

theorem unsignedSyntax?_sound {width n : Nat} {x : SExp}
    (h : unsignedSyntax? width n = some x) : AtomU width x n := by
  unfold unsignedSyntax? at h
  dsimp only at h
  split at h
  · next hn => cases h; exact ⟨_, rfl, ValuesExamples.un_iff.mpr hn⟩
  · cases h

theorem bitsSyntax?_sound {width : Nat} {bits : BitVec width} {x : SExp}
    (h : bitsSyntax? bits = some x) : AtomI width x bits := by
  unfold bitsSyntax? at h
  dsimp only at h
  split at h
  · next hn => cases h; exact ⟨_, rfl, ValuesExamples.in_iff.mpr hn⟩
  · cases h

theorem floatBitsSyntax?_sound {t : FloatType} {bits : BitVec t.width} {x : SExp}
    (h : floatBitsSyntax? t bits = some x) : AtomF t x bits := by
  cases t <;> simp only [floatBitsSyntax?] at h
  all_goals
    split at h
    · next hn => cases h; exact ⟨_, rfl, ValuesExamples.fn_iff.mpr hn⟩
    · cases h

theorem indexSyntax?_sound {k : IndexKind} {i : Wasm.Idx k} {x : SExp}
    (h : indexSyntax? i = some x) (names : List (Option String)) : Text.Idx names x i :=
  .inl (unsignedSyntax?_sound h)

theorem heapSyntax?_sound {t : HeapType} {x : SExp}
    (h : heapSyntax? t = some x) (I : Text.Core.IdCtx) : Text.Core.HeapTypeT I x t := by
  cases t with
  | abstract a =>
    cases a <;> cases h <;> exact .inl ⟨_, _, rfl, rfl, rfl⟩
  | typeIdx i => exact .inr ⟨i, indexSyntax?_sound h _, rfl⟩

theorem refSyntax?_sound {r : RefType} {x : SExp}
    (h : refSyntax? r = some x) (I : Text.Core.IdCtx) : Text.Core.RefTypeT I x r := by
  unfold refSyntax? at h
  obtain ⟨heap, hh, h⟩ := Option.bind_eq_some_iff.mp h
  cases r with
  | mk nullable ht =>
    cases nullable <;> cases h
    · exact .inl ⟨heap, ht, rfl, heapSyntax?_sound hh I, rfl⟩
    · exact .inr (.inl ⟨heap, ht, rfl, heapSyntax?_sound hh I, rfl⟩)

theorem valueSyntax?_sound {t : ValType} {x : SExp} (h : valueSyntax? t = some x)
    (I : Text.Core.IdCtx) : Text.Core.ValTypeT I x t := by
  cases t with
  | num n =>
    cases n with
    | int i =>
      cases i <;> cases h
      · exact .inl ⟨"i32", .int .i32, rfl, rfl, rfl⟩
      · exact .inl ⟨"i64", .int .i64, rfl, rfl, rfl⟩
    | float f =>
      cases f <;> cases h
      · exact .inl ⟨"f32", .float .f32, rfl, rfl, rfl⟩
      · exact .inl ⟨"f64", .float .f64, rfl, rfl, rfl⟩
  | vec v => cases v; cases h; exact .inr (.inl ⟨rfl, rfl⟩)
  | ref r => exact .inr (.inr ⟨r, refSyntax?_sound h I, rfl⟩)

private theorem concat_one {α : Type} {R : SExp → List α → Prop}
    {x : SExp} {as : List α} (h : R x as) (hl : as.length < 2 ^ 32) :
    Text.Core.Concat R [x] as := ⟨[as], .cons h .nil, by simp, hl⟩

theorem functionType?_sound {I : Text.Core.IdCtx} {i : TypeIdx} {ft : FuncType}
    (h : functionType? I i = some ft) : Text.Core.TypeDefIsFunc I i ft := by
  unfold functionType? at h
  split at h
  · next rt n he =>
    split at h
    · next final supers ft' hs =>
      cases h
      exact ⟨rt, n, final, supers, he, hs⟩
    · cases h
  · cases h

theorem storageSyntax?_sound {t : StorageType} {x : SExp}
    (h : storageSyntax? t = some x) (I : Text.Core.IdCtx) : Text.Core.StorageTypeT I x t := by
  cases t with
  | val t => exact .inl ⟨t, valueSyntax?_sound h I, rfl⟩
  | packed p =>
    cases p <;> cases h
    · exact .inr (.inl ⟨rfl, rfl⟩)
    · exact .inr (.inr ⟨rfl, rfl⟩)

theorem fieldTypeSyntax?_sound {f : FieldType} {x : SExp}
    (h : fieldTypeSyntax? f = some x) (I : Text.Core.IdCtx) : Text.Core.FieldTypeT I x f := by
  unfold fieldTypeSyntax? at h
  obtain ⟨storage, hs, h⟩ := Option.bind_eq_some_iff.mp h
  cases f with
  | mk mutability t =>
    cases mutability <;> cases h
    · exact .inl ⟨t, storageSyntax?_sound hs I, rfl⟩
    · exact .inr ⟨storage, t, rfl, storageSyntax?_sound hs I, rfl⟩

theorem compositeSyntax?_sound {ct : CompositeType} {x : SExp}
    (h : compositeSyntax? ct = some x) (I : Text.Core.IdCtx) :
    Text.Core.CompTypeT I x ct (compositeNames ct) := by
  cases ct with
  | func ft =>
    simp only [compositeSyntax?] at h
    split at h
    · cases h
    · next hbound =>
      have hlen : ft.params.length < 2 ^ 32 ∧ ft.results.length < 2 ^ 32 := by
        simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] using hbound
      obtain ⟨ps, hps, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rs, hrs, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      refine .inr (.inr ⟨[L (K "param" :: ps)], [L (K "result" :: rs)],
        ft.params.map (·, none), ft.results, rfl, ?_, ?_, ?_, rfl⟩)
      · exact concat_one (.inr ⟨ps, ft.params, rfl,
          mapM_sound (fun t x hx => valueSyntax?_sound hx I) hps, rfl⟩)
          (by simpa using hlen.1)
      · exact concat_one ⟨rs, rfl, mapM_sound (fun t x hx => valueSyntax?_sound hx I) hrs⟩ hlen.2
      · cases ft; simp [Function.comp_def]
  | struct fs =>
    simp only [compositeSyntax?] at h
    split at h
    · cases h
    · next hlen =>
      obtain ⟨fields, hf, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      refine .inl ⟨[L (K "field" :: fields)], fs.map (·, none), rfl, ?_, ?_, ?_⟩
      · exact concat_one (.inr ⟨fields, fs, rfl,
          mapM_sound (fun f x hx => fieldTypeSyntax?_sound hx I) hf, rfl⟩)
          (by simpa using hlen)
      · simp [Function.comp_def]
      · simp [compositeNames, Function.comp_def]
  | array f =>
    simp only [compositeSyntax?] at h
    obtain ⟨field, hf, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .inr (.inl ⟨field, f, rfl, fieldTypeSyntax?_sound hf I, rfl, rfl⟩)

theorem subTypeSyntax?_sound {st : SubType} {x : SExp}
    (h : subTypeSyntax? st = some x) (I : Text.Core.IdCtx) :
    Text.Core.SubTypeT I x st (compositeNames st.body) := by
  unfold subTypeSyntax? at h
  split at h
  · cases h
  · next hlen =>
    obtain ⟨supers, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨body, hb, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    refine .inl ⟨(if st.final_ then [K "final"] else []), supers, body, st.supertypes,
      st.body, rfl, ?_, mapM_sound (fun i x hx => indexSyntax?_sound hx _) hs,
      by simpa using hlen, compositeSyntax?_sound hb I, ?_⟩
    · cases st.final_ <;> simp
    · cases st with
      | mk final supers body => cases final <;> rfl

theorem recTypeSyntax?_sound {rt : RecType} {x : SExp}
    (h : recTypeSyntax? rt = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.type rt] (typeContext rt) [] := by
  unfold recTypeSyntax? at h
  split at h
  · cases h
  · next hlen =>
    obtain ⟨bodies, hb, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    let defs := rt.types.map fun st => (st, (none : Option String), compositeNames st.body)
    have hf : List.Forall₂ (fun dx (d : SubType × Option String × List (Option String)) =>
        Text.Core.TypeDefT I dx d.1 d.2.1 d.2.2)
        (bodies.map fun b => L [K "type", b]) defs := by
      have hs := mapM_sound (fun st x hx => subTypeSyntax?_sound hx I) hb
      simpa only [defs, List.forall₂_map_left_iff, List.forall₂_map_right_iff] using
        hs.imp (fun _ _ h => ⟨[], _, rfl, .inl ⟨rfl, rfl⟩, h⟩)
    have hr : Text.Core.RecTypeT I
        (L (K "rec" :: bodies.map fun b => L [K "type", b])) rt (Text.Core.recCtx defs) := by
      refine .inl ⟨_, defs, rfl, hf, by simpa [defs] using hlen, ?_, rfl⟩
      cases rt; simp [defs, Function.comp_def]
    simpa [typeContext, Text.Core.recCtx, defs, List.map_map, Function.comp_def] using
      Text.Core.DeclT.type hr

theorem typeSyntax?_sound {rt : RecType} {x : SExp} (h : typeSyntax? rt = some x)
    (I : Text.Core.IdCtx) : Text.Core.DeclT I x [.type rt] (typeContext rt) [] := by
  unfold typeSyntax? at h
  split at h
  · next ft =>
    split at h
    · cases h
    · next hbound =>
      have hlen : ft.params.length < 2 ^ 32 ∧ ft.results.length < 2 ^ 32 := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hbound
        exact hbound
      obtain ⟨ps, hps, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rs, hrs, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hp := mapM_sound (fun t x h => valueSyntax?_sound h I) hps
      have hr := mapM_sound (fun t x h => valueSyntax?_sound h I) hrs
      apply (by
        simpa [typeContext, compositeNames, Text.Core.recCtx] using
          (Text.Core.DeclT.type (I := I)
            (x := L [K "type", L [K "func", L (K "param" :: ps), L (K "result" :: rs)]])
            (J := { types := [none], fields := [[]] })
            (rt := ⟨[⟨true, [], .func ft⟩]⟩)))
      refine .inr ⟨⟨true, [], .func ft⟩, none, [], ?_, rfl, rfl⟩
      refine ⟨[], _, rfl, .inl ⟨rfl, rfl⟩, .inr ⟨.func ft, ?_, rfl⟩⟩
      refine .inr (.inr ⟨[L (K "param" :: ps)], [L (K "result" :: rs)],
        ft.params.map (·, none), ft.results, rfl, ?_, ?_, ?_, rfl⟩)
      · exact concat_one (.inr ⟨ps, ft.params, rfl, hp, rfl⟩) (by simpa using hlen.1)
      · exact concat_one ⟨rs, rfl, hr⟩ hlen.2
      · cases ft
        simp [Function.comp_def]
  · exact recTypeSyntax?_sound h I

theorem memoryArgSyntax?_sound {a : MemArg} {xs : List SExp}
    (h : memoryArgSyntax? a = some xs) (N : Nat) : Text.Core.MemArgT N xs a := by
  unfold memoryArgSyntax? at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · next hn =>
      cases h
      exact ⟨[K ("offset=" ++ toString a.offset.val)],
        [K ("align=" ++ toString (2 ^ a.align.val))], rfl,
        .inr ⟨_, _, rfl, by simp, ValuesExamples.un_iff.mpr hn.1⟩,
        .inr ⟨_, _, _, rfl, by simp, ValuesExamples.un_iff.mpr hn.2, rfl⟩⟩
    · cases h

theorem integerMemoryEq_sound {i j : Instr} (h : integerMemoryEq i j = true) : i = j := by
  unfold integerMemoryEq at h
  split at h <;> try cases h
  all_goals
    simp only [decide_eq_true_eq] at h
    simp_all

theorem memoryOpSyntax?_sound {i : Instr} {m : MemIdx} {a : MemArg} {xs : List SExp}
    (h : memoryOpSyntax? i m a = some xs) (I : Text.Core.IdCtx) :
    Text.Core.Plain I xs i [] := by
  unfold memoryOpSyntax? at h
  obtain ⟨entry, he, h⟩ := Option.bind_eq_some_iff.mp h
  rcases entry with ⟨name, N, k⟩
  have hm := List.mem_of_find?_eq_some he
  have hp := List.find?_some he
  have hi : k m a = i := integerMemoryEq_sound hp
  dsimp only at h
  obtain ⟨index, hx, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨args, ha, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  simpa [hi] using (Text.Core.Plain.memOp (mx := [index]) hm
    (.inr ⟨index, rfl, indexSyntax?_sound hx _⟩) (memoryArgSyntax?_sound ha N))

theorem laneInstructionEq_sound {i j : Instr} (h : laneInstructionEq i j = true) : i = j := by
  unfold laneInstructionEq at h
  split at h <;> try cases h
  all_goals simp only [decide_eq_true_eq] at h; simp_all

theorem laneMemorySyntax?_sound {i : Instr} {m : MemIdx} {a : MemArg} {l : LaneIdx}
    {xs : List SExp} (h : laneMemorySyntax? i m a l = some xs) (I : Text.Core.IdCtx) :
    Text.Core.Plain I xs i [] := by
  unfold laneMemorySyntax? at h
  obtain ⟨entry, he, h⟩ := Option.bind_eq_some_iff.mp h
  rcases entry with ⟨name, N, k⟩
  have hm := List.mem_of_find?_eq_some he
  have hp := List.find?_some he
  have hi : k m a l = i := laneInstructionEq_sound hp
  dsimp only at h
  obtain ⟨memory, hmidx, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨args, ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨lane, hl, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  simpa [hi] using (Text.Core.Plain.laneMemOp (mx := [memory]) hm
    (.inr ⟨memory, rfl, indexSyntax?_sound hmidx _⟩) (memoryArgSyntax?_sound ha N)
    (unsignedSyntax?_sound hl))

theorem laneSyntax?_sound {i : Instr} {l : LaneIdx} {xs : List SExp}
    (h : laneSyntax? i l = some xs) (I : Text.Core.IdCtx) : Text.Core.Plain I xs i [] := by
  unfold laneSyntax? at h
  obtain ⟨entry, he, h⟩ := Option.bind_eq_some_iff.mp h
  rcases entry with ⟨name, k⟩
  have hm := List.mem_of_find?_eq_some he
  have hp := List.find?_some he
  have hi : k l = i := laneInstructionEq_sound hp
  dsimp only at h
  obtain ⟨lane, hl, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  simpa [hi] using Text.Core.Plain.lane hm (unsignedSyntax?_sound hl)

set_option maxHeartbeats 1000000 in
theorem vectorConstSyntax?_sound {bits : BitVec 128} {xs : List SExp}
    (h : vectorConstSyntax? bits = some xs) : Text.Core.V128ConstT xs bits := by
  unfold vectorConstSyntax? at h
  dsimp only at h
  split at h
  · next heq =>
    obtain ⟨xs, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .inr (.inr (.inr (.inl ⟨xs, _, rfl,
      mapM_sound (fun (b : BitVec 64) (x : SExp) hx =>
        bitsSyntax?_sound (width := 64) (bits := b) (x := x) hx) hx, rfl, heq.symm⟩)))
  · cases h

set_option maxHeartbeats 1000000 in
theorem instructionSyntax?_sound {i : Instr} {xs : List SExp}
    (h : instructionSyntax? i = some xs) (I : Text.Core.IdCtx) : Text.Core.Plain I xs i [] := by
  unfold instructionSyntax? at h
  split at h <;> try { cases h }
  · next bits =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .i32Const (bitsSyntax?_sound hx)
  · next bits =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .i64Const (bitsSyntax?_sound hx)
  · next bits =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .f32Const (floatBitsSyntax?_sound hx)
  · next bits =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .f64Const (floatBitsSyntax?_sound hx)
  · next i =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .localGet (indexSyntax?_sound hx _)
  · next i =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .localSet (indexSyntax?_sound hx _)
  · next i =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .localTee (indexSyntax?_sound hx _)
  · next i =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .globalGet (indexSyntax?_sound hx _)
  · next i =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .globalSet (indexSyntax?_sound hx _)
  · next i =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .call (indexSyntax?_sound hx _)
  · next i =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .br (indexSyntax?_sound hx _)
  · next i =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .brIf (indexSyntax?_sound hx _)
  · exact memoryOpSyntax?_sound h I
  · exact memoryOpSyntax?_sound h I
  · exact memoryOpSyntax?_sound h I
  · exact memoryOpSyntax?_sound h I
  · exact memoryOpSyntax?_sound h I
  · exact memoryOpSyntax?_sound h I
  · next i =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .memorySize (.inr ⟨x, rfl, indexSyntax?_sound hx _⟩)
  · next i =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .memoryGrow (.inr ⟨x, rfl, indexSyntax?_sound hx _⟩)
  · next m d =>
    obtain ⟨memory, hm, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨data, hd, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .memoryInit (.inr ⟨memory, rfl, indexSyntax?_sound hm _⟩)
      (indexSyntax?_sound hd _)
  · next d =>
    obtain ⟨data, hd, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .dataDrop (indexSyntax?_sound hd _)
  · cases h; exact .select
  · next ts =>
    split at h
    · cases h
    · next hlen =>
      obtain ⟨txs, ht, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact .selectTyped (by simp)
        (concat_one ⟨txs, rfl, mapM_sound (fun t x hx => valueSyntax?_sound hx I) ht⟩
          (by simpa using hlen))
  · next ls l =>
    split at h
    · cases h
    · next hlen =>
      obtain ⟨xs, hx, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact .brTable (mapM_sound (fun i x hi => indexSyntax?_sound hi _) hx)
        (by simp only [List.length_append, List.length_singleton] at *; omega)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .brOnNull (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .brOnNonNull (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .callRef (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .returnCall (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .returnCallRef (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .throw (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .elemDrop (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .refFunc (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .structNew (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .structNewDefault (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .arrayNew (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .arrayNewDefault (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .arraySet (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .arrayFill (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .memoryFill (.inr ⟨x, rfl, indexSyntax?_sound hx _⟩)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .tableGet (.inr ⟨x, rfl, indexSyntax?_sound hx _⟩)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .tableSet (.inr ⟨x, rfl, indexSyntax?_sound hx _⟩)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .tableSize (.inr ⟨x, rfl, indexSyntax?_sound hx _⟩)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .tableGrow (.inr ⟨x, rfl, indexSyntax?_sound hx _⟩)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .tableFill (.inr ⟨x, rfl, indexSyntax?_sound hx _⟩)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .memoryCopy (indexSyntax?_sound hx _) (indexSyntax?_sound hy _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .tableCopy (indexSyntax?_sound hx _) (indexSyntax?_sound hy _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .tableInit (.inr ⟨x, rfl, indexSyntax?_sound hx _⟩) (indexSyntax?_sound hy _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .structSet (indexSyntax?_sound hx _) (indexSyntax?_sound hy _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .arrayNewData (indexSyntax?_sound hx _) (indexSyntax?_sound hy _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .arrayNewElem (indexSyntax?_sound hx _) (indexSyntax?_sound hy _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .arrayCopy (indexSyntax?_sound hx _) (indexSyntax?_sound hy _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .arrayInitData (indexSyntax?_sound hx _) (indexSyntax?_sound hy _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .arrayInitElem (indexSyntax?_sound hx _) (indexSyntax?_sound hy _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .refNull (heapSyntax?_sound hx I)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .refTest (refSyntax?_sound hx I)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .refCast (refSyntax?_sound hx I)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .arrayGet (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .arrayGetS (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .arrayGetU (indexSyntax?_sound hx _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .structGet (indexSyntax?_sound hx _) (indexSyntax?_sound hy _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .structGetS (indexSyntax?_sound hx _) (indexSyntax?_sound hy _)
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .structGetU (indexSyntax?_sound hx _) (indexSyntax?_sound hy _)
  · obtain ⟨label, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨source, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨target, ht, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .brOnCast (indexSyntax?_sound hl _) (refSyntax?_sound hs I) (refSyntax?_sound ht I)
  · obtain ⟨label, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨source, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨target, ht, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .brOnCastFail (indexSyntax?_sound hl _) (refSyntax?_sound hs I) (refSyntax?_sound ht I)
  · obtain ⟨type, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨count, hc, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .arrayNewFixed (indexSyntax?_sound ht _) (unsignedSyntax?_sound hc)
  · exact laneMemorySyntax?_sound h I
  · exact laneMemorySyntax?_sound h I
  · exact laneSyntax?_sound h I
  · exact laneSyntax?_sound h I
  · obtain ⟨xs, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .v128Const (vectorConstSyntax?_sound hx)
  · split at h
    · next hlen =>
      obtain ⟨xs, hx, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact .shuffle (mapM_sound (fun (l : LaneIdx) (x : SExp) hl =>
        unsignedSyntax?_sound (width := 8) (n := l.val) (x := x) hl) hx) hlen
    · cases h
  all_goals
    obtain ⟨name, hn, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .nullary hn

private theorem instructionsSyntax_sound {is : List Instr} {xss : List (List SExp)}
    (h : is.mapM instructionSyntax? = some xss) (I : Text.Core.IdCtx) :
    Text.Core.Instrs I xss.flatten is [] := by
  have hrel := mapM_sound (fun i xs hi => instructionSyntax?_sound hi I) h
  clear h
  induction hrel with
  | nil => exact .nil
  | cons hp _ ih => simpa using Text.Core.Instrs.plain hp ih

/-- Explicit canonical scalar block headers derive the existing block-type
relation without adding an implicit function type. -/
theorem blockTypeSyntax?_sound {bt : BlockType} {xs : List SExp}
    (h : blockTypeSyntax? bt = some xs) (I : Text.Core.IdCtx) :
    Text.Core.BlockTypeT I xs bt [] := by
  cases bt with
  | empty =>
    cases h
    exact .inl ⟨[], Text.Core.valueFormT_of_results
      (concat_one ⟨[], rfl, .nil⟩ (by decide)), rfl, rfl, rfl⟩
  | value t =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .inr (.inl ⟨[t], t, Text.Core.valueFormT_of_results
      (concat_one ⟨[x], rfl, .cons (valueSyntax?_sound hx I) .nil⟩ (by simp)),
      rfl, rfl, rfl⟩)
  | typeIdx _ => cases h

private def InstructionSyntaxT (I : Text.Core.IdCtx) (xs : List SExp) (i : Instr) : Prop :=
  Text.Core.Plain I xs i [] ∨
    ∃ x, xs = [x] ∧ Text.Core.Folded I x [i] []

private theorem syntaxSeq_sound {I : Text.Core.IdCtx} {is : List Instr}
    {xss : List (List SExp)} (h : List.Forall₂ (InstructionSyntaxT I) xss is) :
    Text.Core.Instrs I xss.flatten is [] := by
  induction h with
  | nil => exact .nil
  | cons hp _ ih =>
    rcases hp with hp | ⟨x, rfl, hp⟩
    · simpa using Text.Core.Instrs.plain hp ih
    · simpa using Text.Core.Instrs.folded hp ih

private theorem instructionTreeFuel?_syntax (fuel : Nat) {i : Instr} {xs : List SExp}
    (h : instructionTreeFuel? fuel i = some xs) (I : Text.Core.IdCtx) :
    InstructionSyntaxT I xs i := by
  induction fuel generalizing i xs I with
  | zero => cases h
  | succ fuel ih =>
    unfold instructionTreeFuel? at h
    split at h
    · cases h
    · next fuel' bt body heq =>
      have heq : fuel' = fuel := by omega
      subst fuel'
      obtain ⟨header, hh, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨parts, hp, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hb := syntaxSeq_sound (mapM_sound (fun _ _ hx => ih hx
        { I with labels := none :: I.labels }) hp)
      refine .inr ⟨_, rfl, ?_⟩
      simpa using (Text.Core.Folded.block (lx := [])
        (.inl ⟨rfl, rfl, rfl⟩) (blockTypeSyntax?_sound hh I) hb)
    · next fuel' bt body heq =>
      have heq : fuel' = fuel := by omega
      subst fuel'
      obtain ⟨header, hh, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨parts, hp, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hb := syntaxSeq_sound (mapM_sound (fun _ _ hx => ih hx
        { I with labels := none :: I.labels }) hp)
      refine .inr ⟨_, rfl, ?_⟩
      simpa using (Text.Core.Folded.loop (lx := [])
        (.inl ⟨rfl, rfl, rfl⟩) (blockTypeSyntax?_sound hh I) hb)
    · next fuel' bt left right heq =>
      have heq : fuel' = fuel := by omega
      subst fuel'
      obtain ⟨header, hh, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ls, hl, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rs, hr, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hleft := syntaxSeq_sound (mapM_sound (fun _ _ hx => ih hx
        { I with labels := none :: I.labels }) hl)
      have hright := syntaxSeq_sound (mapM_sound (fun _ _ hx => ih hx
        { I with labels := none :: I.labels }) hr)
      refine .inr ⟨_, rfl, ?_⟩
      simpa using (Text.Core.Folded.ifThenElse (lx := [])
        (.inl ⟨rfl, rfl, rfl⟩) (blockTypeSyntax?_sound hh I)
        Text.Core.FoldedSeq.nil hleft hright)
    · exact .inl (instructionSyntax?_sound h I)

theorem instructionTree?_sound {i : Instr} {xs : List SExp}
    (h : instructionTree? i = some xs) (I : Text.Core.IdCtx) :
    Text.Core.Instrs I xs [i] [] := by
  have hs := instructionTreeFuel?_syntax _ h I
  rcases hs with hp | ⟨x, rfl, hp⟩
  · simpa using Text.Core.Instrs.plain hp Text.Core.Instrs.nil
  · simpa using Text.Core.Instrs.folded hp Text.Core.Instrs.nil

/-- Every previously accepted scalar instruction retains exactly its existing
canonical syntax when routed through the recursive serializer. -/
theorem instructionTree?_of_leaf {i : Instr} {xs : List SExp}
    (h : instructionSyntax? i = some xs) : instructionTree? i = some xs := by
  cases i <;> first | exact h | cases h

private theorem instructionsTree_sound {is : List Instr} {xss : List (List SExp)}
    (h : is.mapM instructionTree? = some xss) (I : Text.Core.IdCtx) :
    Text.Core.Instrs I xss.flatten is [] :=
  syntaxSeq_sound (mapM_sound (fun _ _ hi => instructionTreeFuel?_syntax _ hi I) h)

theorem instructionSyntaxAt?_sound {I : Text.Core.IdCtx} {i : Instr} {xs : List SExp}
    (h : instructionSyntaxAt? I i = some xs) : Text.Core.Plain I xs i [] := by
  unfold instructionSyntaxAt? at h
  split at h
  · obtain ⟨ft, hf, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨table, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨type, hi, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .callIndirect (.inr ⟨table, rfl, indexSyntax?_sound ht _⟩)
      (Text.Core.TypeUseT.ofType (indexSyntax?_sound hi _) (functionType?_sound hf))
      (by simp)
  · obtain ⟨ft, hf, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨table, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨type, hi, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .returnCallIndirect (.inr ⟨table, rfl, indexSyntax?_sound ht _⟩)
      (Text.Core.TypeUseT.ofType (indexSyntax?_sound hi _) (functionType?_sound hf))
      (by simp)
  · exact instructionSyntax?_sound h I

theorem blockTypeSyntaxAt?_sound {I : Text.Core.IdCtx} {bt : BlockType} {xs : List SExp}
    (h : blockTypeSyntaxAt? I bt = some xs) : Text.Core.BlockTypeT I xs bt [] := by
  unfold blockTypeSyntaxAt? at h
  split at h
  · obtain ⟨ft, hf, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨type, hi, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    refine .inr (.inr ⟨_, _,
      Text.Core.TypeUseT.ofType (indexSyntax?_sound hi _) (functionType?_sound hf),
      by simp, rfl, ?_⟩)
    rintro ⟨ts, hform, _⟩
    exact Text.Core.not_valueFormT_kw (by decide) (by decide) hform
  · exact blockTypeSyntax?_sound h I
theorem catchSyntax?_sound {c : Catch} {x : SExp}
    (h : catchSyntax? c = some x) (I : Text.Core.IdCtx) : Text.Core.CatchT I x c := by
  cases c with
  | catch_ t l =>
    obtain ⟨tx, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨lx, hl, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .inl ⟨tx, lx, t, l, rfl, indexSyntax?_sound ht _, indexSyntax?_sound hl _, rfl⟩
  | catchRef t l =>
    obtain ⟨tx, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨lx, hl, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .inr (.inl ⟨tx, lx, t, l, rfl, indexSyntax?_sound ht _, indexSyntax?_sound hl _, rfl⟩)
  | catchAll l =>
    obtain ⟨lx, hl, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .inr (.inr (.inl ⟨lx, l, rfl, indexSyntax?_sound hl _, rfl⟩))
  | catchAllRef l =>
    obtain ⟨lx, hl, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .inr (.inr (.inr ⟨lx, l, rfl, indexSyntax?_sound hl _, rfl⟩))

private theorem instructionTreeAtFuel?_syntax (fuel : Nat) {I : Text.Core.IdCtx} {i : Instr} {xs : List SExp}
    (h : instructionTreeAtFuel? fuel I i = some xs) :
    InstructionSyntaxT I xs i := by
  induction fuel generalizing i xs I with
  | zero => cases h
  | succ fuel ih =>
    cases i <;> simp only [instructionTreeAtFuel?] at h
    case block bt body =>
      obtain ⟨header, hh, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨parts, hp, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hb := syntaxSeq_sound (mapM_sound (fun i xs hx =>
        ih (I := { I with labels := none :: I.labels }) (i := i) (xs := xs) hx) hp)
      refine .inr ⟨_, rfl, ?_⟩
      simpa using (Text.Core.Folded.block (lx := [])
        (.inl ⟨rfl, rfl, rfl⟩) (blockTypeSyntaxAt?_sound hh) hb)
    case loop bt body =>
      obtain ⟨header, hh, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨parts, hp, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hb := syntaxSeq_sound (mapM_sound (fun i xs hx =>
        ih (I := { I with labels := none :: I.labels }) (i := i) (xs := xs) hx) hp)
      refine .inr ⟨_, rfl, ?_⟩
      simpa using (Text.Core.Folded.loop (lx := [])
        (.inl ⟨rfl, rfl, rfl⟩) (blockTypeSyntaxAt?_sound hh) hb)
    case if_ bt left right =>
      obtain ⟨header, hh, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ls, hl, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rs, hr, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hleft := syntaxSeq_sound (mapM_sound (fun i xs hx =>
        ih (I := { I with labels := none :: I.labels }) (i := i) (xs := xs) hx) hl)
      have hright := syntaxSeq_sound (mapM_sound (fun i xs hx =>
        ih (I := { I with labels := none :: I.labels }) (i := i) (xs := xs) hx) hr)
      refine .inr ⟨_, rfl, ?_⟩
      simpa using (Text.Core.Folded.ifThenElse (lx := [])
        (.inl ⟨rfl, rfl, rfl⟩) (blockTypeSyntaxAt?_sound hh)
        Text.Core.FoldedSeq.nil hleft hright)
    case tryTable bt catches body =>
      obtain ⟨header, hh, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨cs, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨parts, hp, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hb := syntaxSeq_sound (mapM_sound (fun i xs hx =>
        ih (I := { I with labels := none :: I.labels }) (i := i) (xs := xs) hx) hp)
      refine .inr ⟨_, rfl, ?_⟩
      simpa using (Text.Core.Folded.tryTable (lx := [])
        (.inl ⟨rfl, rfl, rfl⟩) (blockTypeSyntaxAt?_sound hh)
        (mapM_sound (fun c x hx => catchSyntax?_sound hx I) hc) hb)
    all_goals exact .inl (instructionSyntaxAt?_sound h)

theorem instructionTreeAt?_sound {I : Text.Core.IdCtx} {i : Instr} {xs : List SExp}
    (h : instructionTreeAt? I i = some xs) :
    Text.Core.Instrs I xs [i] [] := by
  have hs := instructionTreeAtFuel?_syntax _ h
  rcases hs with hp | ⟨x, rfl, hp⟩
  · simpa using Text.Core.Instrs.plain hp Text.Core.Instrs.nil
  · simpa using Text.Core.Instrs.folded hp Text.Core.Instrs.nil

private theorem instructionsTreeAt_sound {I : Text.Core.IdCtx} {is : List Instr}
    {xss : List (List SExp)} (h : is.mapM (instructionTreeAt? I) = some xss) :
    Text.Core.Instrs I xss.flatten is [] :=
  syntaxSeq_sound (mapM_sound (fun i xs hi => instructionTreeAtFuel?_syntax _ (I := I) (i := i) (xs := xs) hi) h)

theorem functionSyntax?_sound {I : Text.Core.IdCtx} {f : Func} {x : SExp}
    (h : functionSyntax? I f = some x) :
    Text.Core.DeclT I x [.func f] { funcs := [none] } [] := by
  unfold functionSyntax? at h
  obtain ⟨ft, hft, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
  · next hlen =>
    have hlen : f.locals.length < 2 ^ 32 := Nat.lt_of_not_ge hlen
    dsimp only at h
    split at h
    · cases h
    · next hok =>
      have hok : (I ++ ({ locals := List.replicate ft.params.length none ++
          (List.map (fun (_ : ValType) => (none : Option String)) f.locals) } : Text.Core.IdCtx)).Ok := by simpa using hok
      obtain ⟨tx, htx, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ls, hls, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨body, hbody, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hl := mapM_sound (fun t x ht => valueSyntax?_sound ht I) hls
      have ht := Text.Core.TypeUseT.ofType (indexSyntax?_sound htx _) (functionType?_sound hft)
      have hloc : Text.Core.Concat (Text.Core.LocalT I) [L (K "local" :: ls)]
          (f.locals.map (·, none)) :=
        concat_one (.inr ⟨ls, f.locals, rfl, hl, rfl⟩) (by simpa using hlen)
      have hb := instructionsTreeAt_sound hbody
      simpa [Function.comp_def, Text.Core.selfExports] using Text.Core.DeclT.func (ix := []) (ex := [])
        (.inl ⟨rfl, rfl⟩) (.nil) ht hloc
        (by simpa only [List.map_map, Function.comp_def] using hok)
        (by simpa only [List.map_map, Function.comp_def] using hb)

theorem nameSyntax?_sound {name : String} {x : SExp} (h : nameSyntax? name = some x) :
    Name x name := by
  unfold nameSyntax? at h
  dsimp only at h
  split at h
  · next hn => cases h; exact ⟨_, rfl, hn⟩
  · cases h

theorem exportSyntax?_sound {e : Export} {x : SExp} (h : exportSyntax? e = some x)
    (I : Text.Core.IdCtx) : Text.Core.DeclT I x [.export_ e] {} [] := by
  unfold exportSyntax? at h
  split at h
  · next f hidx =>
    obtain ⟨name, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .export_ (nameSyntax?_sound hn) (.inr (.inr (.inr (.inr
      ⟨_, _, rfl, indexSyntax?_sound hi _, hidx⟩))))
  · next m hidx =>
    obtain ⟨name, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .export_ (nameSyntax?_sound hn) (.inr (.inr (.inl
      ⟨_, _, rfl, indexSyntax?_sound hi _, hidx⟩)))
  · next g hidx =>
    obtain ⟨name, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .export_ (nameSyntax?_sound hn) (.inr (.inl
      ⟨_, _, rfl, indexSyntax?_sound hi _, hidx⟩))
  · next t hidx =>
    obtain ⟨name, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .export_ (nameSyntax?_sound hn) (.inl
      ⟨_, _, rfl, indexSyntax?_sound hi _, hidx⟩)
  · next t hidx =>
    obtain ⟨name, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .export_ (nameSyntax?_sound hn) (.inr (.inr (.inr (.inl
      ⟨_, _, rfl, indexSyntax?_sound hi _, hidx⟩))))

theorem memoryLimitsSyntax?_sound {limits : Limits} {xs : List SExp}
    (h : memoryLimitsSyntax? limits = some xs) : Text.Core.LimitsT xs limits := by
  unfold memoryLimitsSyntax? at h
  obtain ⟨min, hmin, h⟩ := Option.bind_eq_some_iff.mp h
  cases hmax : limits.max with
  | none =>
      rw [hmax] at h
      cases h
      exact .inl ⟨min, limits.min, rfl, unsignedSyntax?_sound hmin,
        by cases limits; simp_all⟩
  | some max =>
      rw [hmax] at h
      obtain ⟨maxText, hm, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact .inr ⟨min, maxText, limits.min, max, rfl, unsignedSyntax?_sound hmin,
        unsignedSyntax?_sound hm, by cases limits; simp_all⟩

theorem memoryTypeSyntax?_sound {m : MemoryType} {xs : List SExp}
    (h : memoryTypeSyntax? m = some xs) : Text.Core.MemTypeT xs m := by
  unfold memoryTypeSyntax? at h
  obtain ⟨limits, hl, h⟩ := Option.bind_eq_some_iff.mp h
  cases m with
  | mk addr lim =>
    cases addr <;> cases h
    · exact ⟨[], limits, .i32, lim, rfl, .inl ⟨rfl, rfl⟩,
        memoryLimitsSyntax?_sound hl, rfl⟩
    · exact ⟨[K "i64"], limits, .i64, lim, rfl, .inr (.inr ⟨rfl, rfl⟩),
        memoryLimitsSyntax?_sound hl, rfl⟩

theorem memorySyntax?_sound {m : MemoryType} {x : SExp}
    (h : memorySyntax? m = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.mem m] { mems := [none] } [] := by
  unfold memorySyntax? at h
  obtain ⟨xs, hx, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  simpa [Text.Core.selfExports] using (Text.Core.DeclT.mem (I := I) (ix := []) (ex := [])
    (names := []) (.inl ⟨rfl, rfl⟩) .nil (memoryTypeSyntax?_sound hx))

theorem globalTypeSyntax?_sound {g : GlobalType} {x : SExp}
    (h : globalTypeSyntax? g = some x) (I : Text.Core.IdCtx) :
    Text.Core.GlobalTypeT I x g := by
  unfold globalTypeSyntax? at h
  obtain ⟨value, hv, h⟩ := Option.bind_eq_some_iff.mp h
  cases g with
  | mk mutability type =>
    cases mutability <;> cases h
    · exact .inl ⟨type, valueSyntax?_sound hv I, rfl⟩
    · exact .inr ⟨value, type, rfl, valueSyntax?_sound hv I, rfl⟩

theorem constantSyntax?_sound {e : Expr} {xs : List SExp}
    (h : constantSyntax? e = some xs) (I : Text.Core.IdCtx) :
    Text.Core.ExprT I xs e [] := by
  unfold constantSyntax? at h
  obtain ⟨xss, hx, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact instructionsTree_sound hx I

theorem globalSyntax?_sound {g : Global} {x : SExp}
    (h : globalSyntax? g = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.global g] { globals := [none] } [] := by
  unfold globalSyntax? at h
  obtain ⟨type, ht, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨init, hi, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  simpa [Text.Core.selfExports] using (Text.Core.DeclT.global (I := I) (ix := []) (ex := [])
    (names := []) (.inl ⟨rfl, rfl⟩) .nil (globalTypeSyntax?_sound ht I)
    (constantSyntax?_sound hi I))

theorem dataSyntax?_sound {d : Data} {x : SExp}
    (h : dataSyntax? d = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.data d] { datas := [none] } [] := by
  obtain ⟨bytes, mode⟩ := d
  unfold dataSyntax? at h
  dsimp only at h
  split at h
  · cases h
    simpa using (Text.Core.DeclT.dataPassive (I := I) (ix := [])
      (bs := bytes.data.toList)
      (.inl ⟨rfl, rfl⟩) ⟨[bytes.data.toList], .cons rfl .nil, by simp⟩)
  · obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨offset, ho, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    simpa using (Text.Core.DeclT.dataActive (I := I) (ix := [])
      (bs := bytes.data.toList)
      (.inl ⟨rfl, rfl⟩) (.inr ⟨index, rfl, indexSyntax?_sound hi _⟩)
      (.inl ⟨offset, rfl, constantSyntax?_sound ho I⟩)
      ⟨[bytes.data.toList], .cons rfl .nil, by simp⟩)

theorem tableTypeSyntax?_sound {t : TableType} {xs : List SExp}
    (h : tableTypeSyntax? t = some xs) (I : Text.Core.IdCtx) : Text.Core.TableTypeT I xs t := by
  unfold tableTypeSyntax? at h
  obtain ⟨limits, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨element, he, h⟩ := Option.bind_eq_some_iff.mp h
  cases t with
  | mk addr lim el =>
    cases addr <;> cases h
    · exact ⟨[], limits, element, .i32, lim, el, rfl, .inl ⟨rfl, rfl⟩,
        memoryLimitsSyntax?_sound hl, refSyntax?_sound he I, rfl⟩
    · exact ⟨[K "i64"], limits, element, .i64, lim, el, rfl, .inr (.inr ⟨rfl, rfl⟩),
        memoryLimitsSyntax?_sound hl, refSyntax?_sound he I, rfl⟩

theorem defaultTableInit_sound {t : Table} (h : defaultTableInit t = true) :
    t.init = [.refNull t.type.element.heap] := by
  unfold defaultTableInit at h
  split at h
  · next heap he =>
    have hh : heap = t.type.element.heap := by simpa using h
    simpa [hh] using he
  · cases h

theorem foldedInitializerSyntax?_sound {e : Expr} {xs : List SExp}
    (h : foldedInitializerSyntax? e = some xs) (I : Text.Core.IdCtx) :
    Text.Core.ExprT I xs e [] := by
  unfold foldedInitializerSyntax? at h
  obtain ⟨bodies, hb, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  have hs := mapM_sound (fun i xs hx => instructionSyntax?_sound hx I) hb
  clear h hb
  induction hs with
  | nil => exact .nil
  | cons hp _ ih =>
    obtain ⟨name, args, he, _, _⟩ := Text.Core.plain_shape hp
    subst he
    simpa using Text.Core.Instrs.folded (Text.Core.Folded.plain hp Text.Core.Instrs.nil) ih

theorem tableSyntax?_sound {t : Table} {x : SExp}
    (h : tableSyntax? t = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.table t] { tables := [none] } [] := by
  unfold tableSyntax? at h
  obtain ⟨type, ht, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · next hd =>
    cases h
    have hi := defaultTableInit_sound hd
    have he : t = ⟨t.type, [.refNull t.type.element.heap]⟩ := by cases t; simp_all
    rw [he]
    simpa [Text.Core.selfExports] using (Text.Core.DeclT.tableNull (I := I) (ix := []) (ex := [])
      (names := []) (.inl ⟨rfl, rfl⟩) .nil (tableTypeSyntax?_sound ht I))
  · obtain ⟨init, hi, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · next hne =>
      cases h
      simpa [Text.Core.selfExports] using (Text.Core.DeclT.table (I := I) (ix := []) (ex := [])
        (names := []) (.inl ⟨rfl, rfl⟩) .nil (tableTypeSyntax?_sound ht I) hne
        (foldedInitializerSyntax?_sound hi I))

theorem tagSyntax?_sound {I : Text.Core.IdCtx} {t : TagType} {x : SExp}
    (h : tagSyntax? I t = some x) : Text.Core.DeclT I x [.tag t] { tags := [none] } [] := by
  unfold tagSyntax? at h
  obtain ⟨ft, hf, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  simpa [Text.Core.selfExports] using (Text.Core.DeclT.tag (I := I) (ix := []) (ex := [])
    (names := []) (.inl ⟨rfl, rfl⟩) .nil
    ⟨_, Text.Core.TypeUseT.ofType (indexSyntax?_sound hi _) (functionType?_sound hf)⟩)

private theorem elemItems_sound {es : List Expr} {xss : List (List SExp)}
    (h : es.mapM constantSyntax? = some xss) (I : Text.Core.IdCtx) :
    List.Forall₂ (fun x (p : Expr × List FuncType) => Text.Core.ElemExprT I x p.1 p.2)
      (xss.map fun xs => L (K "item" :: xs)) (es.zip (es.map fun _ => [])) := by
  have hs := mapM_sound (fun e xs hx => constantSyntax?_sound hx I) h
  clear h
  induction hs with
  | nil => exact .nil
  | cons hi _ ih => exact .cons (.inl ⟨_, rfl, hi⟩) ih

theorem elemSyntax?_sound {e : Elem} {x : SExp}
    (h : elemSyntax? e = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.elem e] { elems := [none] } [] := by
  unfold elemSyntax? at h
  split at h
  · cases h
  · next hlen =>
    obtain ⟨type, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨items, hi, h⟩ := Option.bind_eq_some_iff.mp h
    have hel : Text.Core.ElemListT I
        (type :: items.map fun xs => L (K "item" :: xs)) e.type e.init [] := by
      refine .inl ⟨type, _, e.init.map (fun _ => []), rfl, refSyntax?_sound ht I,
        elemItems_sound hi I, by simp, by simpa using hlen, ?_⟩
      simp
    cases e with
    | mk type init mode =>
      cases mode with
      | passive =>
        cases h
        exact Text.Core.DeclT.elemPassive (.inl ⟨rfl, rfl⟩) hel
      | declarative =>
        cases h
        exact Text.Core.DeclT.elemDeclare (.inl ⟨rfl, rfl⟩) hel
      | active table offset =>
        obtain ⟨tx, ht, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨ox, ho, h⟩ := Option.bind_eq_some_iff.mp h
        cases h
        simpa using Text.Core.DeclT.elemActive (ix := [])
          (.inl ⟨rfl, rfl⟩) (.inr ⟨tx, rfl, indexSyntax?_sound ht _⟩)
          (.inl ⟨ox, rfl, constantSyntax?_sound ho I⟩) hel

theorem importSyntax?_sound {I : Text.Core.IdCtx} {im : Import} {x : SExp}
    (h : importSyntax? I im = some x) :
    Text.Core.DeclT I x [.import_ im] (importContext im) [] := by
  unfold importSyntax? at h
  split at h
  · next source name type =>
    obtain ⟨ft, hft, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨sourceText, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨nameText, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    apply Text.Core.DeclT.import_ (nameSyntax?_sound hs) (nameSyntax?_sound hn)
    exact .inr (.inr (.inr (.inr ⟨[], _, none, type, _, rfl,
      .inl ⟨rfl, rfl⟩, Text.Core.TypeUseT.ofType (indexSyntax?_sound hi _)
        (functionType?_sound hft), rfl, rfl⟩)))
  · next source name type =>
    obtain ⟨sourceText, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨nameText, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨typeText, ht, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    apply Text.Core.DeclT.import_ (nameSyntax?_sound hs) (nameSyntax?_sound hn)
    exact .inr (.inl ⟨[], typeText, none, type, rfl, .inl ⟨rfl, rfl⟩,
      globalTypeSyntax?_sound ht I, rfl, rfl, rfl⟩)
  · next source name type =>
    obtain ⟨sourceText, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨nameText, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨typeText, ht, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    apply Text.Core.DeclT.import_ (nameSyntax?_sound hs) (nameSyntax?_sound hn)
    exact .inr (.inr (.inl ⟨[], typeText, none, type, rfl, .inl ⟨rfl, rfl⟩,
      memoryTypeSyntax?_sound ht, rfl, rfl, rfl⟩))
  · next source name type =>
    obtain ⟨sourceText, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨nameText, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨typeText, ht, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    apply Text.Core.DeclT.import_ (nameSyntax?_sound hs) (nameSyntax?_sound hn)
    exact .inr (.inr (.inr (.inl ⟨[], typeText, none, type, rfl, .inl ⟨rfl, rfl⟩,
      tableTypeSyntax?_sound ht I, rfl, rfl, rfl⟩)))
  · next source name type =>
    obtain ⟨ft, hft, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨sourceText, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨nameText, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    apply Text.Core.DeclT.import_ (nameSyntax?_sound hs) (nameSyntax?_sound hn)
    exact .inl ⟨[], _, none, type, rfl, .inl ⟨rfl, rfl⟩,
      ⟨_, Text.Core.TypeUseT.ofType (indexSyntax?_sound hi _) (functionType?_sound hft)⟩,
      rfl, rfl⟩

/-- Closed-module callers keep precisely their existing field metadata. -/
theorem moduleFieldsWithImports_noImports (types : List RecType) (funcs : List Func)
    (exports : List Export) :
    moduleFieldsWithImports types [] funcs exports = moduleFields types funcs exports := by
  simp [moduleFieldsWithImports, importFields, moduleFields]

/-- The additive import context agrees with the existing zero-import API. -/
theorem moduleContextWithImports_noImports (types : List RecType) (funcs : List Func)
    (exports : List Export) :
    moduleContextWithImports types [] funcs exports = moduleContext types funcs exports := by
  unfold moduleContextWithImports moduleContext
  rw [moduleFieldsWithImports_noImports]

/-- An absent memory contributes no fields or identifier-context changes. -/
theorem moduleFieldsWithMemories_noMemories (types : List RecType) (imports : List Import)
    (funcs : List Func) (exports : List Export) :
    moduleFieldsWithMemories types imports [] funcs exports =
      moduleFieldsWithImports types imports funcs exports := by
  simp [moduleFieldsWithMemories, moduleFieldsWithImports, memoryFields]

theorem moduleContextWithMemories_noMemories (types : List RecType) (imports : List Import)
    (funcs : List Func) (exports : List Export) :
    moduleContextWithMemories types imports [] funcs exports =
      moduleContextWithImports types imports funcs exports := by
  simp [moduleContextWithMemories, moduleContextWithImports,
    moduleFieldsWithMemories_noMemories]

/-- An empty global list preserves the previous canonical metadata exactly. -/
theorem moduleFieldsWithGlobals_noGlobals (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (funcs : List Func) (exports : List Export) :
    moduleFieldsWithGlobals types imports memories [] funcs exports =
      moduleFieldsWithMemories types imports memories funcs exports := by
  simp [moduleFieldsWithGlobals, moduleFieldsWithMemories, globalFields]

theorem moduleContextWithGlobals_noGlobals (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (funcs : List Func) (exports : List Export) :
    moduleContextWithGlobals types imports memories [] funcs exports =
      moduleContextWithMemories types imports memories funcs exports := by
  simp [moduleContextWithGlobals, moduleContextWithMemories, moduleFieldsWithGlobals_noGlobals]

/-- No data segments preserve the previous field/context metadata exactly. -/
theorem moduleFieldsWithData_noData (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (globals : List Global) (funcs : List Func)
    (exports : List Export) :
    moduleFieldsWithData types imports memories globals funcs [] exports =
      moduleFieldsWithGlobals types imports memories globals funcs exports := by
  simp [moduleFieldsWithData, moduleFieldsWithGlobals, dataFields]

theorem moduleContextWithData_noData (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (globals : List Global) (funcs : List Func)
    (exports : List Export) :
    moduleContextWithData types imports memories globals funcs [] exports =
      moduleContextWithGlobals types imports memories globals funcs exports := by
  simp [moduleContextWithData, moduleContextWithGlobals, moduleFieldsWithData_noData]

theorem startSyntax?_sound {f : FuncIdx} {x : SExp}
    (h : startSyntax? f = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.start f] {} [] := by
  unfold startSyntax? at h
  obtain ⟨fx, hf, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact .start (indexSyntax?_sound hf _)

private def canonicalDecl : Text.Core.Decl → Bool
  | .type _ | .import_ _ | .tag _ | .mem _ | .global _ | .table _ | .func _ | .data _ |
      .elem _ | .start _ | .export_ _ => true
  | _ => false

private theorem resolveAux_canonical (ds : List Text.Core.Decl)
    (h : ∀ d ∈ ds, canonicalDecl d = true)
    (count : Text.Core.Space → Nat) (last : Option (Text.Core.Space × Nat)) :
    Text.Core.resolveAux count last ds = ds := by
  induction ds generalizing count last with
  | nil => rfl
  | cons d ds ih =>
    have hd := h d (by simp)
    have ht : ∀ d ∈ ds, canonicalDecl d = true := fun d hd => h d (by simp [hd])
    cases d <;> simp only [canonicalDecl, Bool.false_eq_true] at hd
    all_goals simp only [Text.Core.resolveAux, Text.Core.Decl.space?]
    all_goals exact congrArg (List.cons _) (ih ht _ _)

private theorem moduleFields_decls (m : Wasm.Module) :
    (moduleFieldsAll m).flatMap (·.1) =
      m.types.map Text.Core.Decl.type ++ m.imports.map Text.Core.Decl.import_ ++
        m.tags.map Text.Core.Decl.tag ++ m.memories.map Text.Core.Decl.mem ++
        m.globals.map Text.Core.Decl.global ++ m.tables.map Text.Core.Decl.table ++
        m.funcs.map Text.Core.Decl.func ++ m.data.map Text.Core.Decl.data ++
        m.elems.map Text.Core.Decl.elem ++ m.start.toList.map Text.Core.Decl.start ++
        m.exports.map Text.Core.Decl.export_ := by
  simp [moduleFieldsAll, typeFields, importFields, tagFields, memoryFields, globalFields,
    tableFields, functionFields, dataFields, elemFields, startFields, exportFields,
    List.flatMap_map, ← List.map_eq_flatMap]

private theorem moduleFields_implicit (m : Wasm.Module) :
    (moduleFieldsAll m).flatMap (·.2.2) = [] := by
  simp [moduleFieldsAll, typeFields, importFields, tagFields, memoryFields, globalFields,
    tableFields, functionFields, dataFields, elemFields, startFields, exportFields]

private theorem canonical_module_decls (m : Wasm.Module) :
    ∀ d ∈ (moduleFieldsAll m).flatMap (·.1), canonicalDecl d = true := by
  intro d hd
  rw [moduleFields_decls] at hd
  simp only [List.mem_append, List.mem_map] at hd
  rcases hd with ((((((((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) <;> rfl

private theorem canonical_module_build (m : Wasm.Module) :
    m = Text.Core.build (Text.Core.resolve ((moduleFieldsAll m).flatMap (·.1))) [] := by
  rw [Text.Core.resolve, resolveAux_canonical _ (canonical_module_decls m), moduleFields_decls]
  cases m with
  | mk types imports tags globals memories tables funcs data elems start exports =>
    cases start <;> simp [Text.Core.build, List.filterMap_map]

private theorem ordered_prefix (before after : List Text.Core.Decl)
    (hb : ∀ d ∈ before, d.isDefinition = false)
    (ha : ∀ d ∈ after, d.isImport = false) : Text.Core.Ordered (before ++ after) := by
  intro i j hi hj hij hjImport
  by_cases hjBefore : j < before.length
  · have hiBefore : i < before.length := Nat.lt_trans hij hjBefore
    rw [List.getElem_append_left hiBefore]
    exact hb _ (List.getElem_mem hiBefore)
  · have hjAfter : j - before.length < after.length := by
      simp only [List.length_append] at hj
      omega
    rw [List.getElem_append_right (Nat.le_of_not_gt hjBefore)] at hjImport
    rw [ha _ (List.getElem_mem hjAfter)] at hjImport
    cases hjImport

private theorem canonical_module_ordered (m : Wasm.Module) :
    Text.Core.Ordered ((moduleFieldsAll m).flatMap (·.1)) := by
  rw [moduleFields_decls, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  apply ordered_prefix
  · intro d hd
    simp only [List.mem_append, List.mem_map] at hd
    rcases hd with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
  · intro d hd
    simp only [List.mem_append, List.mem_map] at hd
    rcases hd with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

/-- The canonical declaration list supplies the module grammar's context,
ordering, start-count and reconstruction obligations independently of its text.
Extensions may reuse this layout proof while retaining their own declarations. -/
theorem moduleFieldsAll_layout (m : Wasm.Module) (hok : (moduleContextAll m).Ok) :
    let outs := moduleFieldsAll m
    let I := moduleContextAll m
    let J := Text.Core.IdCtx.concat (outs.map (·.2.1))
    let ds := outs.flatMap (·.1)
    let implicit := Text.Core.implicitTypes J.typedefs (outs.flatMap (·.2.2))
    I = J ++ Text.Core.implicitCtx implicit ∧ I.Ok ∧ Text.Core.Ordered ds ∧
      Text.Core.startCount ds ≤ 1 ∧ m = Text.Core.build (Text.Core.resolve ds) implicit := by
  simp only [moduleFields_implicit, Text.Core.implicitTypes,
    Text.Core.firstOccurrences, List.foldl_nil, List.filter_nil]
  refine ⟨?_, hok, canonical_module_ordered m, ?_, canonical_module_build m⟩
  · change moduleContextAll m = Text.Core.IdCtx.append (moduleContextAll m) {}
    cases moduleContextAll m
    simp [Text.Core.IdCtx.append]
  · rw [moduleFields_decls]
    cases m.start <;> simp [Text.Core.startCount, List.filter_map, Function.comp_def]

/-- Successful canonical serialization preserves every retained Core module field
under the independent text-format grammar. -/
theorem moduleSyntax?_sound {m : Wasm.Module} {x : SExp}
    (h : moduleSyntax? m = some x) : Text.Core.ModuleT x m := by
  unfold moduleSyntax? at h
  dsimp only at h
  split at h
  · cases h
  · next hok =>
    have hok : (moduleContextAll m).Ok := by simpa using hok
    obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ims, hims, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tags, htags, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ms, hms, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨gs, hgs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tables, htables, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨fs, hfs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ds, hds, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨elems, helems, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ss, hss, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨es, hes, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    let I := moduleContextAll m
    have hts := mapM_sound (fun a x hx => typeSyntax?_sound hx I) hts
    have hims := mapM_sound (fun a x hx => importSyntax?_sound (I := I) (im := a) (x := x) hx) hims
    have htags := mapM_sound (fun a x hx => tagSyntax?_sound (I := I) (t := a) (x := x) hx) htags
    have hms := mapM_sound (fun a x hx => memorySyntax?_sound hx I) hms
    have hgs := mapM_sound (fun a x hx => globalSyntax?_sound hx I) hgs
    have htables := mapM_sound (fun a x hx => tableSyntax?_sound hx I) htables
    have hfs := mapM_sound (fun a x hx => functionSyntax?_sound (I := I) (f := a) (x := x) hx) hfs
    have hds := mapM_sound (fun a x hx => dataSyntax?_sound hx I) hds
    have helems := mapM_sound (fun a x hx => elemSyntax?_sound hx I) helems
    have hss := mapM_sound (fun a x hx => startSyntax?_sound hx I) hss
    have hes := mapM_sound (fun a x hx => exportSyntax?_sound hx I) hes
    have hts' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) ts (typeFields m.types) := by
      simpa [typeFields, List.forall₂_map_right_iff] using hts
    have hims' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) ims (importFields m.imports) := by
      simpa [importFields, List.forall₂_map_right_iff] using hims
    have htags' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) tags (tagFields m.tags) := by
      simpa [tagFields, List.forall₂_map_right_iff] using htags
    have hms' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) ms (memoryFields m.memories) := by
      simpa [memoryFields, List.forall₂_map_right_iff] using hms
    have hgs' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) gs (globalFields m.globals) := by
      simpa [globalFields, List.forall₂_map_right_iff] using hgs
    have htables' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) tables (tableFields m.tables) := by
      simpa [tableFields, List.forall₂_map_right_iff] using htables
    have hfs' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) fs (functionFields m.funcs) := by
      simpa [functionFields, List.forall₂_map_right_iff] using hfs
    have hds' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) ds (dataFields m.data) := by
      simpa [dataFields, List.forall₂_map_right_iff] using hds
    have helems' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) elems (elemFields m.elems) := by
      simpa [elemFields, List.forall₂_map_right_iff] using helems
    have hss' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) ss (startFields m.start) := by
      simpa [startFields, List.forall₂_map_right_iff] using hss
    have hes' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) es (exportFields m.exports) := by
      simpa [exportFields, List.forall₂_map_right_iff] using hes
    refine ⟨ts ++ ims ++ tags ++ ms ++ gs ++ tables ++ fs ++ ds ++ elems ++ ss ++ es, moduleFieldsAll m, I,
      .inl ⟨[], none, rfl, .inl ⟨rfl, rfl⟩⟩, (List.rel_append (List.rel_append (List.rel_append (List.rel_append (List.rel_append (List.rel_append (List.rel_append (List.rel_append (List.rel_append (List.rel_append hts' hims') htags') hms') hgs') htables') hfs') hds') helems') hss') hes'), ?_⟩
    exact moduleFieldsAll_layout m hok

end Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat
