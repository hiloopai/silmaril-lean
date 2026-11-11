module

public import Silmaril.Wasm.Tools.Wast.Json.Defs

/-!
# `json-from-wast` literals: proofs

Proofs for `Silmaril.Wasm.Tools.Wast.Json.Thms`: the float fast path
`floatLitFast?` is sound for `Text.FN`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

open Silmaril.Wasm Silmaril.Wasm.Text Silmaril.Wasm.Text.ValuesExamples

theorem head?_mem {α : Type} {l : List α} {a : α} (h : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs => simp only [List.head?_cons, Option.some.injEq] at h; subst h; simp

theorem signSplit_append (cs : List Char) : (signSplit cs).1 ++ (signSplit cs).2 = cs := by
  unfold signSplit
  split <;> rfl

/-- The candidate made of the first mantissa and the first exponent of the split of `ds` at
its first mark is a candidate of `ds`. -/
theorem mem_of_split_heads {hex : Bool} {ds : List Char} (isMark : Char → Bool)
    (g : Nat × Nat → Int → FloatMag) {mk : Nat × Nat} {ex : Int}
    (hmk : (mantCands hex (ds.takeWhile fun c => !isMark c)).head? = some mk)
    (hexp : (expCands hex (ds.dropWhile fun c => !isMark c)).head? = some ex) :
    g mk ex ∈ (splits ds).flatMap fun p => (mantCands hex p.1).flatMap fun mk =>
      (expCands hex p.2).map fun e => g mk e := by
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨(_, _), mem_splits.2 (List.takeWhile_append_dropWhile).symm, mk, head?_mem hmk,
    ex, head?_mem hexp, rfl⟩

/-- A hexadecimal magnitude of the fast path is a hexadecimal candidate. -/
theorem fmagFast?_hex {cs : List Char} {v : FloatMag} (h1 : ¬cs = "inf".toList)
    (h2 : ¬cs = "nan".toList) (h3 : ¬cs.take "nan:0x".toList.length = "nan:0x".toList)
    (h4 : cs.take 2 = ['0', 'x']) (h : fmagFast? cs = some v) :
    v ∈ (splits (cs.drop 2)).flatMap fun p => (mantCands true p.1).flatMap fun mk =>
      (expCands true p.2).map fun e => FloatMag.hex mk.1 (e - 4 * mk.2) := by
  revert h
  simp only [fmagFast?, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
  split
  · next mk ex hmk hex =>
    intro h
    cases h
    exact mem_of_split_heads _ (fun mk e => .hex mk.1 (e - 4 * mk.2)) hmk hex
  · intro h; cases h

/-- A decimal magnitude of the fast path is a decimal candidate. -/
theorem fmagFast?_dec {cs : List Char} {v : FloatMag} (h1 : ¬cs = "inf".toList)
    (h2 : ¬cs = "nan".toList) (h3 : ¬cs.take "nan:0x".toList.length = "nan:0x".toList)
    (h4 : ¬cs.take 2 = ['0', 'x']) (h : fmagFast? cs = some v) :
    v ∈ (splits cs).flatMap fun p => (mantCands false p.1).flatMap fun mk =>
      (expCands false p.2).map fun e => FloatMag.dec mk.1 (e - mk.2) := by
  revert h
  simp only [fmagFast?, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
  split
  · next mk ex hmk hex =>
    intro h
    cases h
    exact mem_of_split_heads _ (fun mk e => .dec mk.1 (e - mk.2)) hmk hex
  · intro h; cases h

theorem fmagFast?_mem {cs : List Char} {v : FloatMag} (h : fmagFast? cs = some v) :
    v ∈ fmagCands cs := by
  unfold fmagCands
  simp only [List.mem_append]
  by_cases h1 : cs = "inf".toList
  · have hv : FloatMag.inf = v := by
      simpa only [fmagFast?, ite_eq_left h1, Option.some.injEq] using h
    exact .inl (.inl (.inr (by simp [h1, ← hv])))
  by_cases h2 : cs = "nan".toList
  · have hv : FloatMag.nan = v := by
      simpa only [fmagFast?, ite_eq_right h1, ite_eq_left h2, Option.some.injEq] using h
    exact .inl (.inr (by simp [h2, ← hv]))
  by_cases h3 : cs.take "nan:0x".toList.length = "nan:0x".toList
  · obtain ⟨n, hn, hv⟩ : ∃ n, hexNumVal? (cs.drop "nan:0x".toList.length) = some n ∧
        FloatMag.nanPayload n = v := by
      simpa only [fmagFast?, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3,
        Option.map_eq_some_iff] using h
    have h3' : List.take 6 cs = ['n', 'a', 'n', ':', '0', 'x'] := by simpa using h3
    have hn' : hexNumVal? (cs.drop 6) = some n := by simpa using hn
    exact .inr (by simp [h3', hn', ← hv])
  by_cases h4 : cs.take 2 = ['0', 'x']
  · have hx := fmagFast?_hex h1 h2 h3 h4 h
    exact .inl (.inl (.inl (.inr (by simpa only [h4, ↓reduceIte] using hx))))
  · exact .inl (.inl (.inl (.inl (fmagFast?_dec h1 h2 h3 h4 h))))

theorem floatLitFast?_sound' {t : FloatType} {s : String} {b : BitVec t.width}
    (h : floatLitFast? t s = some b) : FN t s.toList b := by
  unfold floatLitFast? at h
  split at h
  · rename_i sg v hsg hv
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨n, hn, rfl⟩ := h
    exact ⟨_, _, sg, v, n, (signSplit_append s.toList).symm,
      signChars_iff.2 (head?_mem hsg), fmag_iff.2 (fmagFast?_mem hv), hn, rfl⟩
  · simp at h

/-! ## Fast JSON printers -/

theorem foldl_esc_append (cs : List Char) (a b : String) :
    cs.foldl (fun acc c => acc ++ escChar c) (a ++ b) =
      a ++ cs.foldl (fun acc c => acc ++ escChar c) b := by
  induction cs generalizing b with
  | nil => rfl
  | cons c cs ih => simp only [List.foldl_cons, String.append_assoc, ih]

theorem jsonStrInto_eq (acc s : String) : jsonStrInto acc s = acc ++ jsonStr s := by
  unfold jsonStrInto jsonStr
  rw [String.foldl_eq_foldl_toList, String.foldl_eq_foldl_toList,
    show acc ++ "\"" = acc ++ "\"" ++ "" from by simp, foldl_esc_append]
  simp only [String.append_assoc]

mutual
  theorem Json.compactInto_eq' : ∀ (acc : String) (j : Json), j.compactInto acc = acc ++ j.compact
    | acc, .arr xs => by
      rw [Json.compactInto, Json.compactListInto_eq' _ xs, Json.compact]
      simp only [String.append_assoc]
    | acc, .obj kvs => by
      rw [Json.compactInto, Json.compactObjInto_eq' _ kvs, Json.compact]
      simp only [String.append_assoc]
    | acc, .str s => by rw [Json.compactInto, jsonStrInto_eq, Json.compact]
    | acc, .null => rfl
    | acc, .bool _ => rfl
    | acc, .num _ => rfl

  theorem Json.compactListInto_eq' : ∀ (acc : String) (xs : List Json),
      Json.compactListInto acc xs = acc ++ Json.compactList xs
    | acc, [] => by simp [Json.compactListInto, Json.compactList]
    | acc, [x] => by rw [Json.compactListInto, Json.compactList, Json.compactInto_eq']
    | acc, x :: y :: xs => by
      rw [Json.compactListInto, Json.compactListInto_eq' _ (y :: xs), Json.compactInto_eq']
      rw [show Json.compactList (x :: y :: xs) = x.compact ++ "," ++ Json.compactList (y :: xs)
        from by rw [Json.compactList]; simp]
      · simp only [String.append_assoc]
      exact fun h => List.cons_ne_nil _ _ h

  theorem Json.compactObjInto_eq' : ∀ (acc : String) (kvs : List (String × Json)),
      Json.compactObjInto acc kvs = acc ++ Json.compactObj kvs
    | acc, [] => by simp [Json.compactObjInto, Json.compactObj]
    | acc, [(k, v)] => by
      rw [Json.compactObjInto, Json.compactObj, Json.compactInto_eq', jsonStrInto_eq]
      simp only [String.append_assoc]
    | acc, (k, v) :: kv :: kvs => by
      rw [Json.compactObjInto, Json.compactObjInto_eq' _ (kv :: kvs), Json.compactInto_eq',
        jsonStrInto_eq]
      rw [show Json.compactObj ((k, v) :: kv :: kvs) =
          jsonStr k ++ ":" ++ v.compact ++ "," ++ Json.compactObj (kv :: kvs)
        from by rw [Json.compactObj]; simp]
      · simp only [String.append_assoc]
      exact fun h => List.cons_ne_nil _ _ h
end

mutual
  theorem Json.prettyInto_eq' : ∀ (d : Nat) (acc : String) (j : Json),
      j.prettyInto d acc = acc ++ j.prettyAt d
    | d, acc, .arr [] => by rw [Json.prettyInto, Json.prettyAt]
    | d, acc, .obj [] => by rw [Json.prettyInto, Json.prettyAt]
    | d, acc, .arr (x :: xs) => by
      rw [Json.prettyInto, Json.prettyListInto_eq', Json.prettyAt]
      · simp only [String.append_assoc]
      all_goals exact fun h => List.cons_ne_nil _ _ h
    | d, acc, .obj (kv :: kvs) => by
      rw [Json.prettyInto, Json.prettyObjInto_eq', Json.prettyAt]
      · simp only [String.append_assoc]
      all_goals exact fun h => List.cons_ne_nil _ _ h
    | d, acc, .str s => by rw [Json.prettyInto, Json.prettyAt, Json.compactInto_eq'] <;> simp
    | d, acc, .null => by rw [Json.prettyInto, Json.prettyAt, Json.compactInto_eq'] <;> simp
    | d, acc, .bool _ => by rw [Json.prettyInto, Json.prettyAt, Json.compactInto_eq'] <;> simp
    | d, acc, .num _ => by rw [Json.prettyInto, Json.prettyAt, Json.compactInto_eq'] <;> simp

  theorem Json.prettyListInto_eq' : ∀ (d : Nat) (acc : String) (xs : List Json),
      Json.prettyListInto d acc xs = acc ++ Json.prettyList d xs
    | d, acc, [] => by simp [Json.prettyListInto, Json.prettyList]
    | d, acc, [x] => by
      rw [Json.prettyListInto, Json.prettyList, Json.prettyInto_eq']
      simp only [String.append_assoc]
    | d, acc, x :: y :: xs => by
      rw [Json.prettyListInto, Json.prettyListInto_eq' _ _ (y :: xs), Json.prettyInto_eq']
      rw [show Json.prettyList d (x :: y :: xs) =
          indent d ++ x.prettyAt d ++ ",\n" ++ Json.prettyList d (y :: xs)
        from by rw [Json.prettyList]; simp]
      · simp only [String.append_assoc]
      exact fun h => List.cons_ne_nil _ _ h

  theorem Json.prettyObjInto_eq' : ∀ (d : Nat) (acc : String) (kvs : List (String × Json)),
      Json.prettyObjInto d acc kvs = acc ++ Json.prettyObj d kvs
    | d, acc, [] => by simp [Json.prettyObjInto, Json.prettyObj]
    | d, acc, [(k, v)] => by
      rw [Json.prettyObjInto, Json.prettyObj, Json.prettyInto_eq', jsonStrInto_eq]
      simp only [String.append_assoc]
    | d, acc, (k, v) :: kv :: kvs => by
      rw [Json.prettyObjInto, Json.prettyObjInto_eq' _ _ (kv :: kvs), Json.prettyInto_eq',
        jsonStrInto_eq]
      rw [show Json.prettyObj d ((k, v) :: kv :: kvs) =
          indent d ++ jsonStr k ++ ": " ++ v.prettyAt d ++ ",\n" ++ Json.prettyObj d (kv :: kvs)
        from by rw [Json.prettyObj]; simp]
      · simp only [String.append_assoc]
      exact fun h => List.cons_ne_nil _ _ h
end

end Silmaril.Wasm.Tools.Wast
