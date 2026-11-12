module

public import Silmaril.Wasm.Wit.Text.Parse.Defs
public import Silmaril.Proofs.Wasm.Wit.Text.Lex
public import Silmaril.Wasm.Component.Wat.Thms

/-!
# WIT text: docs, versions and gates read back

* `joinOn_splitOn`, `splitOn_joinOn`: splitting at a character and joining are
  inverse (on pieces without the character);
* `docs_prDocs`: doc comments read back exactly;
* `parseVer_verChars`, `numOk_verChars`: a `verOk` version is one number token that
  reads back;
* `gates_prGates`: gates read back.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

open Parse
open Silmaril.Wasm.Component.Wat (natChars parseNat parseNat_natChars digitChar)

/-! ## Splitting and joining -/

theorem splitOn_ne_nil (c : Char) (l : List Char) : splitOn c l ≠ [] := by
  cases l with
  | nil => simp [splitOn]
  | cons d ds =>
    rw [splitOn]; split
    · simp
    · split <;> simp

theorem joinOn_cons (c : Char) (x : List Char) (ws : List (List Char)) :
    joinOn c (x :: ws) = x ++ (if ws = [] then [] else c :: joinOn c ws) := by
  cases ws <;> simp [joinOn]

theorem joinOn_splitOn (c : Char) (l : List Char) : joinOn c (splitOn c l) = l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    rw [splitOn]
    split
    · rename_i h
      rw [joinOn_cons]; simp only [splitOn_ne_nil c ds, ite_false]; rw [ih, h]; rfl
    · split
      · rename_i w ws hw
        rw [hw] at ih
        rw [joinOn_cons, List.cons_append, ← joinOn_cons, ih]
      · rename_i hw; exact absurd hw (splitOn_ne_nil c ds)

theorem splitOn_of_not_mem {c : Char} {x : List Char} (h : c ∉ x) : splitOn c x = [x] := by
  induction x with
  | nil => rfl
  | cons d x ih =>
    have hd : d ≠ c := fun e => h (by simp [e])
    have ih := ih (fun e => h (by simp [e]))
    simp [splitOn, hd, ih]

theorem splitOn_append_sep {c : Char} {x : List Char} (h : c ∉ x) (r : List Char) :
    splitOn c (x ++ c :: r) = x :: splitOn c r := by
  induction x with
  | nil => simp [splitOn]
  | cons d x ih =>
    have hd : d ≠ c := fun e => h (by simp [e])
    have ih := ih (fun e => h (by simp [e]))
    simp [splitOn, hd, ih]

theorem splitOn_joinOn {c : Char} : ∀ {ws : List (List Char)}, ws ≠ [] → (∀ w ∈ ws, c ∉ w) →
    splitOn c (joinOn c ws) = ws
  | [], h, _ => absurd rfl h
  | [x], _, hw => by simp [joinOn, splitOn_of_not_mem (hw x (by simp))]
  | x :: y :: ws, _, hw => by
    rw [joinOn_cons]
    simp only [List.cons_ne_nil, ite_false]
    rw [splitOn_append_sep (hw x (by simp)),
      splitOn_joinOn (List.cons_ne_nil y ws) (fun w hw' => hw w (List.mem_cons_of_mem _ hw'))]

/-! ## Docs -/

/-- `rest` does not start with a doc line. -/
abbrev NoDoc (r : List Tok) : Prop := ∀ s, r.head? ≠ some (.doc s)

theorem docLines_of_noDoc {r : List Tok} (h : NoDoc r) : docLines r = ([], r) := by
  cases r with
  | nil => rfl
  | cons t r =>
    cases t with
    | doc s => exact absurd rfl (h s)
    | _ => rfl

theorem docLines_lines (ls : List (List Char)) {r : List Tok} (h : NoDoc r) :
    docLines ((ls.map fun l => Tok.doc (String.ofList (' ' :: l))) ++ r) =
      (ls.map fun l => String.ofList (' ' :: l), r) := by
  induction ls with
  | nil => simpa using docLines_of_noDoc h
  | cons l ls ih => simp only [List.map_cons, List.cons_append, docLines, ih]

theorem mkDocs_ne {ls : List String} (h : ls ≠ []) :
    mkDocs ls = ⟨some (String.ofList (joinOn '\n' (ls.map fun s => stripSp s.toList)))⟩ := by
  cases ls with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem strip_map (ls : List (List Char)) :
    (ls.map fun l => String.ofList (' ' :: l)).map (fun s => stripSp s.toList) = ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.map_cons, String.toList_ofList, stripSp, List.cons.injEq, true_and]
    exact ih

theorem docs_prDocs (d : Docs) {r : List Tok} (h : NoDoc r) :
    docs (toks (prDocs d) ++ r) = (d, r) := by
  obtain ⟨c⟩ := d
  cases c with
  | none => simp [prDocs, docs, docLines_of_noDoc h, mkDocs]
  | some s =>
    have ht : toks (prDocs ⟨some s⟩) =
        (splitOn '\n' s.toList).map fun l => Tok.doc (String.ofList (' ' :: l)) := by
      simp [prDocs, toks]
    rw [ht, docs, docLines_lines _ h]
    simp only
    rw [mkDocs_ne (by simpa using splitOn_ne_nil '\n' s.toList), strip_map, joinOn_splitOn,
      String.ofList_toList]

theorem noDoc_cons (t : Tok) (r : List Tok) (h : ∀ s, t ≠ .doc s) : NoDoc (t :: r) := by
  intro s; simpa using h s

/-! ## Versions -/

theorem isDigit_digitChar : ∀ d : Fin 10, isDigitC (digitChar d) = true := by decide

theorem natChars_digits (n : Nat) : ∀ c ∈ natChars n, isDigitC c = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natChars]
    split
    · intro c hc; simp at hc; subst hc; exact isDigit_digitChar ⟨n, by omega⟩
    · intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact ih (n / 10) (by omega) c hc
      · exact isDigit_digitChar ⟨n % 10, Nat.mod_lt n (by omega)⟩

theorem digit_ne {c : Char} (h : isDigitC c = true) :
    c ≠ '.' ∧ c ≠ '+' ∧ c ≠ '-' ∧ wordCont c = true := by
  refine ⟨?_, ?_, ?_, by simp [wordCont, h]⟩ <;> (rintro rfl; revert h; decide)

theorem wordCont_ne {c : Char} (h : wordCont c = true) : c ≠ '.' ∧ c ≠ '+' := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; revert h; decide)

theorem natChars_ne_nil' (n : Nat) : natChars n ≠ [] := by
  rw [natChars]; split <;> simp

theorem splitFirst_append {c : Char} {x : List Char} (h : c ∉ x) (r : List Char) :
    splitFirst c (x ++ r) = (x ++ (splitFirst c r).1, (splitFirst c r).2) := by
  induction x with
  | nil => rfl
  | cons d x ih =>
    have hd : d ≠ c := fun e => h (by simp [e])
    have ih := ih (fun e => h (by simp [e]))
    simp [splitFirst, hd, ih]

/-- The pieces of a dot-separated identifier list. -/
theorem ids_facts {ids : List String} (h : ∀ s ∈ ids, s.toList ≠ [] ∧ ∀ c ∈ s.toList, wordCont c = true) :
    ∀ c ∈ joinOn '.' (ids.map String.toList), c ≠ '+' ∧ c ≠ '-' → c = '.' ∨ wordCont c = true := by
  intro c hc _
  induction ids with
  | nil => simp [joinOn] at hc
  | cons s ids ih =>
    rw [List.map_cons, joinOn_cons] at hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · exact .inr ((h s (by simp)).2 c hc)
    · split at hc
      · simp at hc
      · simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact .inl rfl
        · exact ih (fun s hs => h s (by simp [hs])) hc

theorem joinOn_ids_no {ids : List String} (h : ∀ s ∈ ids, s.toList ≠ [] ∧ ∀ c ∈ s.toList, wordCont c = true)
    (d : Char) (hd : d ≠ '.') (hw : wordCont d = false) : d ∉ joinOn '.' (ids.map String.toList) := by
  intro hm
  induction ids with
  | nil => simp [joinOn] at hm
  | cons s ids ih =>
    rw [List.map_cons, joinOn_cons] at hm
    simp only [List.mem_append] at hm
    rcases hm with hm | hm
    · have := (h s (by simp)).2 d hm; simp_all
    · split at hm
      · simp at hm
      · simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · exact hd rfl
        · exact ih (fun s hs => h s (by simp [hs])) hm

theorem dotIds_joinOn {ids : List String} (hne : ids ≠ [])
    (h : ∀ s ∈ ids, s.toList ≠ [] ∧ ∀ c ∈ s.toList, wordCont c = true) :
    dotIds (some (joinOn '.' (ids.map String.toList))) = ids := by
  simp only [dotIds]
  rw [splitOn_joinOn (by simpa using hne)]
  · simp
  · intro w hw hm
    simp only [List.mem_map] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    have := (h s hs).2 _ hm
    revert this; decide

/-- The pre-release and build parts of a `verOk` version. -/
theorem verOk_parts {v : Version} (h : verOk v = true) :
    (∀ s ∈ v.pre, s.toList ≠ [] ∧ ∀ c ∈ s.toList, wordCont c = true) ∧
      (∀ s ∈ v.build, s.toList ≠ [] ∧ ∀ c ∈ s.toList, wordCont c = true) := by
  simp only [verOk, List.all_eq_true, List.mem_append, Bool.and_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, ne_eq] at h
  exact ⟨fun s hs => h s (.inl hs), fun s hs => h s (.inr hs)⟩

theorem parseVer_verChars (v : Version) (h : verOk v = true) : parseVer (verChars v) = some v := by
  obtain ⟨hp, hb⟩ := verOk_parts h
  have dig := fun n => natChars_digits n
  have nod : ∀ n, ∀ c, c = '.' ∨ c = '+' ∨ c = '-' → c ∉ natChars n := by
    intro n c hc hm
    have := digit_ne (dig n c hm)
    rcases hc with rfl | rfl | rfl <;> simp_all
  -- the core `a.b.c`
  set A := natChars v.major ++ '.' :: natChars v.minor ++ '.' :: natChars v.patch with hA
  set B : List Char := if v.pre = [] then [] else '-' :: joinOn '.' (v.pre.map String.toList)
  set C : List Char := if v.build = [] then [] else '+' :: joinOn '.' (v.build.map String.toList)
  have hv : verChars v = A ++ B ++ C := by simp [verChars, hA, B, C]
  have hAc : ∀ c ∈ A, c = '.' ∨ isDigitC c = true := by
    intro c hc
    rw [hA] at hc
    rcases List.mem_append.mp hc with h1 | h1
    · rcases List.mem_append.mp h1 with h2 | h2
      · exact .inr (dig _ _ h2)
      · rcases List.mem_cons.mp h2 with h3 | h3
        · exact .inl h3
        · exact .inr (dig _ _ h3)
    · rcases List.mem_cons.mp h1 with h3 | h3
      · exact .inl h3
      · exact .inr (dig _ _ h3)
  have hAplus : '+' ∉ A := fun hm => by
    rcases hAc _ hm with h | h
    · exact absurd h (by decide)
    · exact (digit_ne h).2.1 rfl
  have hAminus : '-' ∉ A := fun hm => by
    rcases hAc _ hm with h | h
    · exact absurd h (by decide)
    · exact (digit_ne h).2.2.1 rfl
  have hBplus : '+' ∉ B := by
    simp only [B]; split
    · simp
    · simp only [List.mem_cons, not_or]
      exact ⟨by decide, joinOn_ids_no hp '+' (by decide) (by decide)⟩
  have hC : splitFirst '+' C = ([], if v.build = [] then none
      else some (joinOn '.' (v.build.map String.toList))) := by
    simp only [C]; split <;> simp [splitFirst]
  have hB : splitFirst '-' B = ([], if v.pre = [] then none
      else some (joinOn '.' (v.pre.map String.toList))) := by
    simp only [B]; split <;> simp [splitFirst]
  have h1 : splitFirst '+' (verChars v) = (A ++ B, (splitFirst '+' C).2) := by
    rw [hv, List.append_assoc, splitFirst_append hAplus, splitFirst_append hBplus, hC]; simp
  have h2 : splitFirst '-' (A ++ B) = (A, (splitFirst '-' B).2) := by
    rw [splitFirst_append hAminus, hB]; simp
  have h3 : splitOn '.' A = [natChars v.major, natChars v.minor, natChars v.patch] := by
    rw [hA, List.append_assoc, List.cons_append, splitOn_append_sep (nod _ _ (by simp)),
      splitOn_append_sep (nod _ _ (by simp)), splitOn_of_not_mem (nod _ _ (by simp))]
  have hpre : dotIds (splitFirst '-' B).2 = v.pre := by
    rw [hB]; split
    · simp [dotIds, *]
    · exact dotIds_joinOn ‹_› hp
  have hbuild : dotIds (splitFirst '+' C).2 = v.build := by
    rw [hC]; split
    · simp [dotIds, *]
    · exact dotIds_joinOn ‹_› hb
  rw [parseVer, h1]
  simp only
  rw [h2]
  simp only
  rw [h3]
  simp only [parseNat_natChars, hpre, hbuild]

/-! ## The version token is lexable -/

/-- What `takeNum` consumes entirely. -/
def NumTail : List Char → Prop
  | [] => True
  | [c] => wordCont c = true
  | c :: d :: r => (wordCont c = true ∨ ((c = '.' ∨ c = '+') ∧ wordCont d = true)) ∧
      NumTail (d :: r)

theorem takeNum_of_numTail : ∀ {l : List Char}, NumTail l → (takeNum l).2 = []
  | [], _ => rfl
  | [c], h => by simp [NumTail] at h; simp [takeNum, h]
  | c :: d :: r, h => by
    obtain ⟨h1, h2⟩ := h
    have ih := takeNum_of_numTail h2
    rw [takeNum]
    have hc : (wordCont c || ((c == '.' || c == '+') &&
        ((d :: r).head?.map wordCont).getD false)) = true := by
      rcases h1 with h1 | ⟨h1, h3⟩ <;> simp_all
    simp only [hc, ite_true]
    exact ih

theorem numTail_append : ∀ {x y : List Char}, NumTail x → NumTail y → NumTail (x ++ y)
  | [], _, _, hy => hy
  | [_], [], hx, _ => hx
  | [_], _ :: _, hx, hy => ⟨.inl hx, hy⟩
  | _ :: _ :: _, _, hx, hy => ⟨hx.1, numTail_append hx.2 hy⟩

theorem numTail_all : ∀ {l : List Char}, (∀ c ∈ l, wordCont c = true) → NumTail l
  | [], _ => trivial
  | [c], h => h c (by simp)
  | c :: d :: r, h => ⟨.inl (h c (by simp)), numTail_all (fun x hx => h x (by simp_all))⟩

theorem numTail_sep {c d : Char} {l : List Char} (hc : c = '.' ∨ c = '+') (hd : wordCont d = true)
    (h : NumTail (d :: l)) : NumTail (c :: d :: l) := ⟨.inr ⟨hc, hd⟩, h⟩

theorem numTail_sep_natChars {c : Char} (hc : c = '.' ∨ c = '+') (n : Nat) :
    NumTail (c :: natChars n) := by
  cases h : natChars n with
  | nil => exact absurd h (natChars_ne_nil' n)
  | cons d l =>
    have hd := (digit_ne (natChars_digits n d (by simp [h]))).2.2.2
    refine numTail_sep hc hd ?_
    rw [← h]; exact numTail_all fun x hx => (digit_ne (natChars_digits n x hx)).2.2.2

theorem numTail_sep_ids {c : Char} (hc : c = '.' ∨ c = '+') : ∀ {ids : List String},
    ids ≠ [] → (∀ s ∈ ids, s.toList ≠ [] ∧ ∀ c ∈ s.toList, wordCont c = true) →
    NumTail (c :: joinOn '.' (ids.map String.toList))
  | [], h, _ => absurd rfl h
  | s :: ids, _, h => by
    obtain ⟨hne, hall⟩ := h s (by simp)
    have rest : NumTail (joinOn '.' ((s :: ids).map String.toList)) := by
      rw [List.map_cons, joinOn_cons]
      refine numTail_append (numTail_all hall) ?_
      split
      · trivial
      · rename_i hids
        exact numTail_sep_ids (.inl rfl) (by simpa using hids) (fun t ht => h t (by simp [ht]))
    cases hs : s.toList with
    | nil => exact absurd hs hne
    | cons d l =>
      have : joinOn '.' ((s :: ids).map String.toList) = d :: (l ++
          (if ids.map String.toList = [] then [] else '.' :: joinOn '.' (ids.map String.toList))) := by
        rw [List.map_cons, joinOn_cons, hs]; rfl
      rw [this] at rest ⊢
      exact numTail_sep hc (hall d (by simp [hs])) rest

theorem numTail_pre (v : Version)
    (hp : ∀ s ∈ v.pre, s.toList ≠ [] ∧ ∀ c ∈ s.toList, wordCont c = true) :
    NumTail (if v.pre = [] then [] else '-' :: joinOn '.' (v.pre.map String.toList)) := by
  split
  · trivial
  · rename_i hpre
    cases hj : joinOn '.' (v.pre.map String.toList) with
    | nil => simp [NumTail]; decide
    | cons e m =>
      have h := numTail_sep_ids (c := '.') (.inl rfl) hpre hp
      rw [hj] at h
      exact ⟨.inl rfl, h.2⟩

theorem numTail_build (v : Version)
    (hb : ∀ s ∈ v.build, s.toList ≠ [] ∧ ∀ c ∈ s.toList, wordCont c = true) :
    NumTail (if v.build = [] then [] else '+' :: joinOn '.' (v.build.map String.toList)) := by
  split
  · trivial
  · exact numTail_sep_ids (.inr rfl) ‹_› hb

theorem numOk_verChars (v : Version) (h : verOk v = true) :
    numOk (String.ofList (verChars v)) = true := by
  obtain ⟨hp, hb⟩ := verOk_parts h
  unfold numOk
  rw [String.toList_ofList]
  cases hn : natChars v.major with
  | nil => exact absurd hn (natChars_ne_nil' _)
  | cons d l =>
    have hv : verChars v = d :: (l ++ ('.' :: natChars v.minor) ++ ('.' :: natChars v.patch) ++
        (if v.pre = [] then [] else '-' :: joinOn '.' (v.pre.map String.toList)) ++
        (if v.build = [] then [] else '+' :: joinOn '.' (v.build.map String.toList))) := by
      simp [verChars, hn]
    rw [hv]
    simp only [Bool.and_eq_true, List.isEmpty_iff]
    refine ⟨natChars_digits v.major d (by simp [hn]), takeNum_of_numTail ?_⟩
    have hl : NumTail l := numTail_all fun x hx =>
      (digit_ne (natChars_digits v.major x (by simp [hn, hx]))).2.2.2
    refine numTail_append (numTail_append (numTail_append (numTail_append hl
      (numTail_sep_natChars (.inl rfl) _)) (numTail_sep_natChars (.inl rfl) _)) ?_) ?_
    · exact numTail_pre v hp
    · exact numTail_build v hb

/-! ## Gates -/

/-- The versions of a gate are `verOk`. -/
def gateVOk : Gate → Bool
  | .since v | .deprecated v => verOk v
  | .unstable _ => true

theorem gates_nil {r : List Tok} (h : r.head? ≠ some (.sym '@')) : gates r = some ([], r) := by
  cases r with
  | nil => rfl
  | cons t r => simp at h; simp [gates, h]

theorem gates_prGates : ∀ (gs : List Gate) {r : List Tok}, (∀ g ∈ gs, gateVOk g = true) →
    r.head? ≠ some (.sym '@') → gates (toks (prGates gs) ++ r) = some (gs, r)
  | [], _, _, hr => gates_nil hr
  | g :: gs, r, hv, hr => by
    have ih := gates_prGates gs (fun g' h' => hv g' (by simp [h'])) hr
    simp only [prGates] at ih
    have hg := hv g (by simp)
    cases g with
    | since v =>
      simp only [gateVOk] at hg
      simp [prGates, prGate, verTok, gates, gatesAt, String.toList_ofList,
        parseVer_verChars v hg, ih]
    | unstable f =>
      simp [prGates, prGate, gates, gatesAt, ih]
    | deprecated v =>
      simp only [gateVOk] at hg
      simp [prGates, prGate, verTok, gates, gatesAt, String.toList_ofList,
        parseVer_verChars v hg, ih]

end Silmaril.Wasm.Wit.Text
