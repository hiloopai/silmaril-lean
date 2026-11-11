module

public import Silmaril.Wasm.Tools.Wast.CheckSpec.Defs

/-!
# The `wast` directive logic: proofs

Proofs for `Silmaril.Wasm.Tools.Wast.Check.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

/-! ## The checking monad over `Id` -/

theorem val_bind {α β : Type} (x : CM Id α) (f : α → CM Id β) :
    val (x >>= f) = match val x with
      | .ok a => val (f a)
      | .error e => .error e := by
  simp only [val, ExceptT.run_bind, Id.run_bind]
  cases Id.run x.run <;> rfl

theorem val_bind_ok {α β : Type} {x : CM Id α} {f : α → CM Id β} {b : β} :
    val (x >>= f) = .ok b ↔ ∃ a, val x = .ok a ∧ val (f a) = .ok b := by
  rw [val_bind]
  cases val x with
  | error e => simp
  | ok a => simp

theorem val_pure {α : Type} (a : α) : val (pure a : CM Id α) = .ok a := rfl

theorem val_throw {α : Type} (e : Chain) : val (throw e : CM Id α) = .error e := rfl

theorem val_liftE {α : Type} (e : Except String α) :
    val (liftE e : CM Id α) = e.mapError (fun s => [s]) := by
  cases e <;> rfl

theorem val_ctx {α : Type} (c : String) (x : CM Id α) :
    val (ctx c x) = (val x).mapError (c :: ·) := by
  simp only [val, ctx, ExceptT.run, ExceptT.mk, Id.run_bind]
  cases Id.run x <;> rfl

theorem val_liftSnap_noSnap (k t s : String) :
    val (liftSnap (noSnap (m := Id) k t s)) =
      .error ["must pass `--snapshot <dir>` to indicate where to place snapshots"] := rfl

theorem mapError_ok {ε ε' α : Type} {f : ε → ε'} {e : Except ε α} {a : α} :
    e.mapError f = .ok a ↔ e = .ok a := by
  cases e <;> simp [Except.mapError]

theorem binaryCompare_ok {a e : ByteArray} : binaryCompare a e = .ok () ↔ a.data = e.data := by
  unfold binaryCompare
  split
  · rename_i h
    simp only [true_iff]
    simpa using h
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro h'
    exact h (by simp [h'])

theorem val_ite {α : Type} (c : Prop) [Decidable c] (x y : CM Id α) :
    val (if c then x else y) = if c then val x else val y := by
  split <;> rfl

theorem val_liftE_ok {α : Type} {e : Except String α} {a : α} :
    val (liftE e : CM Id α) = .ok a ↔ e = .ok a := by
  rw [val_liftE, mapError_ok]

theorem val_ctx_ok {α : Type} {c : String} {x : CM Id α} {a : α} :
    val (ctx c x) = .ok a ↔ val x = .ok a := by
  rw [val_ctx, mapError_ok]

theorem val_pure_ok {α : Type} {a b : α} : val (pure a : CM Id α) = .ok b ↔ a = b := by
  simp [val_pure]

theorem val_throw_ok {α : Type} {e : Chain} {b : α} : val (throw e : CM Id α) = .ok b ↔ False := by
  simp [val_throw]

theorem val_noSnap_ok {k t s : String} {u : Unit} :
    val (liftSnap (noSnap (m := Id) k t s)) = .ok u ↔ False := by
  simp [val_liftSnap_noSnap]

theorem exists_unit_iff {p : Unit → Prop} : (∃ a, p a) ↔ p () :=
  ⟨fun ⟨(), h⟩ => h, fun h => ⟨(), h⟩⟩

theorem val_whenC {c : Bool} {x : Unit → CM Id Unit} {u : Unit} :
    val (whenC c x) = .ok u ↔ (c = true → val (x ()) = .ok ()) := by
  cases u
  cases c with
  | false => simp [whenC, val_pure]
  | true => simp [whenC]

theorem foldedPrint_ok {o : CheckOpts} {test : String} {rt : Roundtrip} {bytes : ByteArray}
    {es : Bool} {f1 : String} :
    val (foldedPrint o noSnap test rt bytes es) = .ok f1 ↔
      (if o.on .testFolded then rt.folded bytes else .ok "") = .ok f1 ∧
        (o.on .testFolded = true → es = true → o.on .snapshotFolded = false) := by
  unfold foldedPrint
  cases ht : o.on .testFolded with
  | false => simp [val_pure]
  | true =>
    simp only [↓reduceIte, val_bind_ok, val_ctx_ok, val_liftE_ok, exists_unit_iff, val_whenC,
      val_noSnap_ok, val_pure_ok, forall_const]
    cases h2 : o.on .snapshotFolded <;> cases hes : es <;> simp

/-- `testRoundtrip` when the backend has a round trip. -/
theorem testRoundtrip_some_ok_iff {b : Backend} {o : CheckOpts} {test : String}
    {bytes : ByteArray} {rb es : Bool} {rt : Roundtrip} (hrt : b.roundtrip = some rt) :
    val (testRoundtrip b o noSnap test bytes rb es) = .ok () ↔ RoundtripOk b o bytes rb es := by
  unfold testRoundtrip RoundtripOk
  rw [hrt]
  simp only [roundtripWith, val_bind_ok, val_ctx_ok, val_liftE_ok, exists_unit_iff, val_whenC,
    foldedPrint_ok, foldedRoundtrip, reencodeCheck, val_noSnap_ok, binaryCompare_ok,
    val_throw_ok, Roundtrip.folded, bne_iff_ne, ne_eq, imp_false, not_not, Bool.and_eq_true,
    not_and]
  constructor
  · rintro ⟨t1, hp, hs, f1, ⟨hf, hfs⟩, hpw, b2, hb2, t2, hp2, hrb, rfl, hfold, hre⟩
    refine ⟨t1, hp, fun he => ?_, f1, hf, hfs, hpw, b2, hb2, hp2, hrb, fun htf => ?_, hre⟩
    · cases h : o.on .snapshotPrint <;> simp_all
    · obtain ⟨bf, hbf, f2, _, hrbf, t3, hp3, _, rfl⟩ := hfold htf
      exact ⟨bf, hbf, hrbf, hp3⟩
  · rintro ⟨t1, hp, hs, f1, hf, hfs, hpw, b2, hb2, hp2, hrb, hfold, hre⟩
    refine ⟨t1, hp, fun he => ?_, f1, ⟨hf, hfs⟩, hpw, b2, hb2, t1, hp2, hrb, rfl, fun htf => ?_, hre⟩
    · cases h : o.on .snapshotPrint <;> simp_all
    · obtain ⟨bf, hbf, hrbf, hp3⟩ := hfold htf
      exact ⟨bf, hbf, f1, by simpa [htf] using hf, hrbf, t1, hp3, rfl, rfl⟩

theorem testRoundtrip_ok_iff {b : Backend} {o : CheckOpts} {test : String} {bytes : ByteArray}
    {rb es : Bool} :
    val (testRoundtrip b o noSnap test bytes rb es) = .ok () ↔ RoundtripOk b o bytes rb es := by
  cases hrt : b.roundtrip with
  | none =>
    unfold testRoundtrip RoundtripOk
    simp [hrt, val_pure]
  | some rt => exact testRoundtrip_some_ok_iff hrt

theorem checkInvalid_ok_iff {b : Backend} {o : CheckOpts} {test src : String} {custom : Bool}
    {q : QuoteWat} {s : List UInt8} :
    val (checkInvalid b o noSnap test src custom q s) = .ok () ↔ InvalidOk b o src custom q s := by
  unfold checkInvalid InvalidOk
  simp only [val_bind_ok, val_liftE_ok, exists_unit_iff, testRoundtrip_ok_iff]
  constructor
  · rintro ⟨bytes, he, hd, hr, hv⟩
    refine ⟨bytes, he, hd, hr, ?_⟩
    cases hval : b.validate bytes with
    | ok u => rw [hval] at hv; simp [val_throw] at hv
    | error e => rw [hval] at hv; exact ⟨e, rfl, (val_liftE_ok).1 hv⟩
  · rintro ⟨bytes, he, hd, hr, e, hv, hm⟩
    refine ⟨bytes, he, hd, hr, ?_⟩
    rw [hv]
    exact (val_liftE_ok).2 hm

theorem malformedOk_of_enc_ok {b : Backend} {o : CheckOpts} {src : String} {custom : Bool}
    {q : QuoteWat} {s : List UInt8} {bytes : ByteArray}
    (henc : encodeQW b.enc src q = .ok bytes) :
    MalformedOk b o src custom q s ↔
      ((∃ e, b.decode bytes = .error e ∧ errorMatches o e s = .ok () ∧
          (b.validate bytes).toBool = custom) ∨
        (b.decode bytes = .ok () ∧ o.on .permissive = true ∧
          utf8? s = some "data count section required" ∧ InvalidOk b o src custom q s)) := by
  unfold MalformedOk
  constructor
  · rintro (⟨e, he, _⟩ | ⟨bytes', e, he, hd, hm, hv⟩ | ⟨bytes', he, hd, hp, hu, hi⟩)
    · rw [henc] at he; cases he
    · rw [henc] at he; cases he; exact .inl ⟨e, hd, hm, hv⟩
    · rw [henc] at he; cases he; exact .inr ⟨hd, hp, hu, hi⟩
  · rintro (⟨e, hd, hm, hv⟩ | ⟨hd, hp, hu, hi⟩)
    · exact .inr (.inl ⟨bytes, e, henc, hd, hm, hv⟩)
    · exact .inr (.inr ⟨bytes, henc, hd, hp, hu, hi⟩)

/-- `checkMalformed` when the encoded module does not decode. -/
theorem checkMalformed_decode_error {b : Backend} {o : CheckOpts} {test src : String}
    {custom : Bool} {q : QuoteWat} {s : List UInt8} {bytes : ByteArray} {e : String}
    (henc : encodeQW b.enc src q = .ok bytes) (hdec : b.decode bytes = .error e) :
    val (checkMalformed b o noSnap test src custom q s) = .ok () ↔
      MalformedOk b o src custom q s := by
  rw [malformedOk_of_enc_ok henc]
  simp only [checkMalformed, henc, hdec, val_bind_ok, val_liftE_ok, exists_unit_iff,
    reduceCtorEq, false_and, or_false, Except.error.injEq, exists_eq_left']
  cases custom <;> cases hval : b.validate bytes <;>
    simp [val_pure, val_throw, Except.toBool]

/-- `checkMalformed` when the encoded module decodes: only the permissive data-count case
passes, and then as an invalid module. -/
theorem checkMalformed_decode_ok {b : Backend} {o : CheckOpts} {test src : String}
    {custom : Bool} {q : QuoteWat} {s : List UInt8} {bytes : ByteArray} {u : Unit}
    (henc : encodeQW b.enc src q = .ok bytes) (hdec : b.decode bytes = .ok u) :
    val (checkMalformed b o noSnap test src custom q s) = .ok () ↔
      MalformedOk b o src custom q s := by
  rw [malformedOk_of_enc_ok henc]
  simp only [checkMalformed, henc, hdec, reduceCtorEq, false_and, exists_false, false_or,
    true_and]
  split
  · rename_i hp
    have hp' : o.on .permissive = true ∧ utf8? s = some "data count section required" := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using hp
    rw [checkInvalid_ok_iff]
    exact ⟨fun h => ⟨hp'.1, hp'.2, h⟩, fun h => h.2.2⟩
  · rename_i hp
    simp only [val_throw_ok, false_iff]
    rintro ⟨h1, h2, _⟩
    exact hp (by simp [h1, h2])

theorem checkMalformed_ok_iff {b : Backend} {o : CheckOpts} {test src : String} {custom : Bool}
    {q : QuoteWat} {s : List UInt8} :
    val (checkMalformed b o noSnap test src custom q s) = .ok () ↔
      MalformedOk b o src custom q s := by
  cases henc : encodeQW b.enc src q with
  | error e =>
    unfold MalformedOk
    simp only [checkMalformed, henc, val_liftE_ok, reduceCtorEq, false_and, exists_false,
      or_false, Except.error.injEq, exists_eq_left']
  | ok bytes =>
    cases hdec : b.decode bytes with
    | error e => exact checkMalformed_decode_error henc hdec
    | ok u => exact checkMalformed_decode_ok henc hdec

theorem testWasm_ok_iff {b : Backend} {o : CheckOpts} {test : String} {bytes : ByteArray}
    {rb : Bool} :
    val (testWasm b o noSnap test bytes rb) = .ok () ↔
      b.validate bytes = .ok () ∧ RoundtripOk b o bytes rb true := by
  simp only [testWasm, val_bind_ok, val_ctx_ok, val_liftE_ok, exists_unit_iff, testRoundtrip_ok_iff]

theorem moduleOk_iff {b : Backend} {o : CheckOpts} {test src : String} {q : QuoteWat} {rb : Bool} :
    val (do
        let bytes ← liftE (encodeQW b.enc src q)
        ctx "failed testing wasm binary produced by `wast`" (testWasm b o noSnap test bytes rb) :
        CM Id Unit) = .ok () ↔ ModuleOk b o src q rb := by
  simp only [val_bind_ok, val_liftE_ok, val_ctx_ok, testWasm_ok_iff, ModuleOk]

theorem checkBase_ok_iff {b : Backend} {o : CheckOpts} {test src : String} {idx : Nat}
    {d : Directive} :
    val (checkBase b o noSnap test idx src d) = .ok () ↔ DirectiveOk b o src d := by
  cases d <;> simp only [checkBase, DirectiveOk, checkMalformed_ok_iff, checkInvalid_ok_iff,
    moduleOk_iff, val_pure]

/-- On a directive other than `thread`, `checkDirective` is `checkBase` on its source slice. -/
theorem checkDirective_base {b : Backend} {o : CheckOpts} {test : String} {source : ByteArray}
    {idx : Nat} {d : Directive} {p : PNode} (hd : ∀ n sh ds, d ≠ .thread n sh ds) :
    checkDirective b o (noSnap (m := Id)) test source idx d p =
      checkBase b o noSnap test idx (modSrc source p d) d := by
  cases d <;> first | (exfalso; exact hd _ _ _ rfl) | simp [checkDirective]

theorem nodeOk_base {b : Backend} {o : CheckOpts} {source : ByteArray} {d : Directive}
    {p : PNode} (hd : ∀ n sh ds, d ≠ .thread n sh ds) :
    NodeOk b o source d p = DirectiveOk b o (modSrc source p d) d := by
  cases d <;> first | (exfalso; exact hd _ _ _ rfl) | simp [NodeOk]

mutual
  theorem checkDirective_ok_iff {b : Backend} {o : CheckOpts} {test : String}
      {source : ByteArray} : ∀ (idx : Nat) (d : Directive) (p : PNode),
      val (checkDirective b o noSnap test source idx d p) = .ok () ↔ NodeOk b o source d p
    | idx, .thread n sh ds, p => by
      simp only [checkDirective, NodeOk]
      exact checkThread_ok_iff idx 0 ds _
    | idx, .module q, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .moduleDefinition k id body, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .moduleInstance k i m, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .assertMalformed q s, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .assertMalformedCustom q s, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .assertInvalid q s, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .assertInvalidCustom q s, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .register n m, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .invoke i, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .assertTrap e s, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .assertReturn e rs, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .assertExhaustion i s, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .assertUnlinkable q s, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .assertException e, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .assertSuspension e s, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff
    | idx, .wait n, p => by
      rw [checkDirective_base (by intros; simp), nodeOk_base (by intros; simp)]
      exact checkBase_ok_iff

  theorem checkThread_ok_iff {b : Backend} {o : CheckOpts} {test : String}
      {source : ByteArray} : ∀ (idx i : Nat) (ds : List Directive) (ps : List PNode),
      val (checkThread b o noSnap test source idx i ds ps) = .ok () ↔ ThreadOk b o source ds ps
    | _, _, [], _ => by simp [checkThread, ThreadOk, val_pure]
    | _, _, _ :: _, [] => by simp [checkThread, ThreadOk, val_pure]
    | idx, i, d :: ds, q :: qs => by
      simp only [checkThread, ThreadOk, val_bind_ok, exists_unit_iff]
      rw [checkDirective_ok_iff, checkThread_ok_iff]
end

theorem checkAll_nil_iff {b : Backend} {o : CheckOpts} {test : String} {source : ByteArray} :
    ∀ (i : Nat) (l : List (Directive × PNode)) (acc : Array (Nat × Chain)),
      Id.run (checkAll b o noSnap test source i l acc) = [] ↔
        acc = #[] ∧ ∀ dp ∈ l, NodeOk b o source dp.1 dp.2
  | _, [], acc => by
    simp only [checkAll, Id.run_pure, Array.toList_eq_nil_iff, List.not_mem_nil, false_imp_iff,
      implies_true, and_true]
  | i, (d, p) :: rest, acc => by
    simp only [checkAll, Id.run_bind, List.mem_cons, forall_eq_or_imp]
    rw [checkAll_nil_iff]
    have h := checkDirective_ok_iff (b := b) (o := o) (test := test) (source := source) i d p
    cases hr : Id.run (checkDirective b o (noSnap (m := Id)) test source i d p).run with
    | ok u =>
      have : NodeOk b o source d p := h.1 (by simp [val, hr])
      simp [this]
    | error e =>
      have : ¬ NodeOk b o source d p := fun hn => by simpa [val, hr] using h.2 hn
      simp [this]

theorem checkScriptPure_directives_nil_iff {b : Backend} {o : CheckOpts} {test : String}
    {source : ByteArray} {ds : List Directive} {ps : List PNode} :
    checkScriptPure b o test source (.directives ds) ps = [] ↔
      ∀ dp ∈ ds.zip ps, NodeOk b o source dp.1 dp.2 := by
  simp only [checkScriptPure, checkScript]
  rw [checkAll_nil_iff]
  simp

theorem checkScriptPure_inline_nil_iff {b : Backend} {o : CheckOpts} {test : String}
    {source : ByteArray} {xs : List Silmaril.Formats.SExpEncoding.SExp} {ps : List PNode} :
    checkScriptPure b o test source (.inline xs) ps = [] ↔
      xs ≠ [] ∧ ModuleOk b o (String.fromUTF8! source) (.wat .core none (.fields xs)) true := by
  cases xs with
  | nil => simp [checkScriptPure, checkScript]
  | cons x xs =>
    have h := checkBase_ok_iff (b := b) (o := o) (test := test) (idx := 0)
      (src := String.fromUTF8! source) (d := .module (.wat .core none (.fields (x :: xs))))
    simp only [DirectiveOk, expectBinaryRoundtrip] at h
    simp only [checkScriptPure, checkScript, Id.run_bind, ne_eq, reduceCtorEq, not_false_eq_true,
      true_and]
    cases hr : Id.run (checkBase b o (noSnap (m := Id)) test 0 (String.fromUTF8! source)
        (.module (.wat .core none (.fields (x :: xs))))).run with
    | ok u => simp [← h, val, hr]
    | error e =>
      constructor
      · intro hc; simp at hc
      · intro hm; have := h.2 hm; simp [val, hr] at this

end Silmaril.Wasm.Tools.Wast
