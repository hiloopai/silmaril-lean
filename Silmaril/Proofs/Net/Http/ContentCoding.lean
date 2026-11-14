module

public import Silmaril.Net.Http.ContentCoding.Defs
public import Silmaril.Net.Http.Qvalue.Thms
public import Silmaril.Formats.Compression.Registry.Thms

/-! Proofs for `Silmaril.Net.Http.ContentCoding.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Net.Http.ContentCoding

open Silmaril.Net.Http.ContentCoding
open Silmaril.Formats.Compression Silmaril.Formats.Compression.Registry

/-! ## Quality values -/

theorem parseWeight_le {w : List UInt8} {q : Nat} (h : parseWeightAfterSemicolon w = some q) :
    q ≤ 1000 := by
  unfold parseWeightAfterSemicolon at h
  split at h
  · split at h
    · exact Silmaril.Net.Http.Qvalue.parseQvalue_le h
    · cases h
  · cases h

theorem withWeight_le {c : Codings} {rest : List UInt8} {p : Pref}
    (h : withWeight c rest = some p) : p.q ≤ 1000 := by
  cases rest with
  | nil => simp only [withWeight, Option.some.injEq] at h; subst h; exact Nat.le_refl _
  | cons _ w =>
    simp only [withWeight, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    exact parseWeight_le hq

theorem parseElement_le {e : List UInt8} {p : Pref} (h : parseElement e = some p) : p.q ≤ 1000 := by
  simp only [parseElement, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, h⟩ := h
  exact withWeight_le h

theorem mapM_parseElement_le :
    ∀ {es : List (List UInt8)} {prefs : List Pref}, es.mapM parseElement = some prefs →
      ∀ p ∈ prefs, p.q ≤ 1000
  | [], prefs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; intro p hp; cases hp
  | e :: es, prefs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨p, hp, ps, hps, rfl⟩ := h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact parseElement_le hp
    · exact mapM_parseElement_le hps x hx

theorem parseAcceptEncoding_le {v : List UInt8} {prefs : List Pref}
    (h : parseAcceptEncoding v = some prefs) : ∀ p ∈ prefs, p.q ≤ 1000 :=
  mapM_parseElement_le h

theorem lookupQ_le {prefs : List Pref} (hp : ∀ p ∈ prefs, p.q ≤ 1000) {n : Name} {q : Nat}
    (h : lookupQ prefs n = some q) : q ≤ 1000 := by
  simp only [lookupQ, Option.map_eq_some_iff] at h
  obtain ⟨p, hf, rfl⟩ := h
  exact hp p (List.mem_of_find?_eq_some hf)

theorem anyQ_le {prefs : List Pref} (hp : ∀ p ∈ prefs, p.q ≤ 1000) {q : Nat}
    (h : anyQ prefs = some q) : q ≤ 1000 := by
  simp only [anyQ, Option.map_eq_some_iff] at h
  obtain ⟨p, hf, rfl⟩ := h
  exact hp p (List.mem_of_find?_eq_some hf)

theorem qOf_le {prefs : List Pref} (hp : ∀ p ∈ prefs, p.q ≤ 1000) (c : Coding) :
    qOf (some prefs) c ≤ 1000 := by
  cases hl : lookupQ prefs c.name with
  | some q => simp only [qOf, hl]; exact lookupQ_le hp hl
  | none =>
    simp only [qOf, hl]
    by_cases hc : c = .identity
    · simp only [hc, ↓reduceIte]; split <;> omega
    · simp only [hc, ↓reduceIte]
      cases ha : anyQ prefs with
      | none => simp
      | some q => simpa using anyQ_le hp ha

/-! ## Selection -/

theorem best_isSome (w : Coding → Nat) :
    ∀ {l : List Coding}, l ≠ [] → (best w l).isSome
  | [], h => absurd rfl h
  | x :: xs, _ => by
    simp only [best]
    cases best w xs with
    | none => rfl
    | some y => by_cases h : w x < w y <;> simp [h]

theorem best_spec (w : Coding → Nat) :
    ∀ {l : List Coding} {c : Coding}, best w l = some c → c ∈ l ∧ ∀ d ∈ l, w d ≤ w c
  | [], c, h => by cases h
  | x :: xs, c, h => by
    simp only [best] at h
    cases hb : best w xs with
    | none =>
      rw [hb] at h
      cases h
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons y ys =>
          have := best_isSome w (l := y :: ys) (List.cons_ne_nil _ _)
          simp [hb] at this
      subst hxs
      exact ⟨List.mem_singleton_self _, fun d hd => by
        rw [List.mem_singleton.mp hd]⟩
    | some y =>
      rw [hb] at h
      obtain ⟨hy, hmax⟩ := best_spec w hb
      by_cases hlt : w x < w y
      · simp only [hlt, ↓reduceIte, Option.some.injEq] at h
        subst h
        refine ⟨List.mem_cons_of_mem _ hy, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Nat.le_of_lt hlt
        · exact hmax d hd
      · simp only [hlt, ↓reduceIte, Option.some.injEq] at h
        subst h
        refine ⟨List.mem_cons_self .., fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Nat.le_refl _
        · exact Nat.le_trans (hmax d hd) (Nat.le_of_not_lt hlt)

theorem select_spec {field : Option (List Pref)} {supported : List Coding} {c : Coding}
    (h : select field supported = some c) :
    0 < qOf field c ∧ c ∈ supported ++ [.identity] ∧
      ∀ d ∈ supported ++ [.identity], qOf field d ≤ qOf field c := by
  unfold select at h
  cases hb : best (qOf field) (supported ++ [.identity]) with
  | none => rw [hb] at h; cases h
  | some x =>
    rw [hb] at h
    by_cases hp : 0 < qOf field x
    · simp only [hp, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨hp, best_spec _ hb⟩
    · simp only [hp, ↓reduceIte, reduceCtorEq] at h

theorem select_eq_none {field : Option (List Pref)} {supported : List Coding}
    (h : select field supported = none) : ∀ d ∈ supported ++ [.identity], qOf field d = 0 := by
  unfold select at h
  have hs := best_isSome (qOf field) (l := supported ++ [.identity]) (by simp)
  cases hb : best (qOf field) (supported ++ [.identity]) with
  | none => rw [hb] at hs; cases hs
  | some x =>
    rw [hb] at h
    have ⟨_, hmax⟩ := best_spec _ hb
    by_cases hp : 0 < qOf field x
    · simp only [hp, ↓reduceIte, reduceCtorEq] at h
    · intro d hd
      have := hmax d hd
      omega

/-- If some candidate has a positive weight, selection succeeds. -/
theorem select_isSome {field : Option (List Pref)} {supported : List Coding} {d : Coding}
    (hd : d ∈ supported ++ [.identity]) (hq : 0 < qOf field d) :
    (select field supported).isSome := by
  cases h : select field supported with
  | some c => rfl
  | none => have := select_eq_none h d hd; omega

theorem selectFor_spec {p : Profile} {ext : Externals} {field : Option (List Pref)} {c : Coding}
    (h : selectFor p ext field = some c) :
    0 < qOf field c ∧ (c = .identity ∨ p.supports ext c = true) := by
  obtain ⟨hq, hm, _⟩ := select_spec h
  refine ⟨hq, ?_⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact .inr (List.mem_filter.mp hm).2
  · exact .inl (List.mem_singleton.mp hm)

/-! ## The identity rules -/

theorem qOf_identity_eq_zero_iff (prefs : List Pref) :
    qOf (some prefs) .identity = 0 ↔
      lookupQ prefs Coding.identity.name = some 0 ∨
        (lookupQ prefs Coding.identity.name = none ∧ anyQ prefs = some 0) := by
  cases hl : lookupQ prefs Coding.identity.name with
  | some q => simp [qOf, hl]
  | none =>
    simp only [qOf, hl, ↓reduceIte, reduceCtorEq, false_or, true_and]
    by_cases ha : anyQ prefs = some 0
    · simp [ha]
    · simp [ha]

theorem qOf_empty (c : Coding) : qOf (some []) c = if c = .identity then 1 else 0 := by
  cases c <;> rfl

theorem select_empty (supported : List Coding) : select (some []) supported = some .identity := by
  have hid : Coding.identity ∈ supported ++ [.identity] := by simp
  have hs := select_isSome hid (by rw [qOf_empty]; decide)
  cases h : select (some []) supported with
  | none => rw [h] at hs; cases hs
  | some c =>
    obtain ⟨hq, _, _⟩ := select_spec h
    rw [qOf_empty] at hq
    by_cases hc : c = .identity
    · rw [hc]
    · simp only [hc, ↓reduceIte, Nat.lt_irrefl] at hq

theorem best_const {w : Coding → Nat} (hw : ∀ c, w c = 1000) (c : Coding) (cs : List Coding) :
    best w (c :: cs) = some c := by
  simp only [best]
  cases best w cs with
  | none => rfl
  | some d => simp only [hw, Nat.lt_irrefl, ↓reduceIte]

theorem select_noField (c : Coding) (cs : List Coding) : select none (c :: cs) = some c := by
  simp only [select, List.cons_append]
  rw [best_const (w := qOf none) (fun _ => rfl)]
  rfl

/-! ## Content-Encoding -/

theorem decodeContent_sound {p : Profile} {ext : Externals} {v body out : List UInt8}
    (h : decodeContent p ext (some v) body = .ok out) :
    ∃ names cs, parseContentEncoding v = some names ∧ resolve names = .ok cs ∧
      p.decode ext cs body = .ok out := by
  simp only [decodeContent] at h
  cases hp : parseContentEncoding v with
  | none => simp only [hp, reduceCtorEq] at h
  | some names =>
    simp only [hp] at h
    cases hr : resolve names with
    | error n => simp only [hr, reduceCtorEq] at h
    | ok cs =>
      simp only [hr] at h
      split at h
      · cases h
      · cases hd : p.decode ext cs body with
        | error e => simp only [hd, reduceCtorEq] at h
        | ok o =>
          simp only [hd, Except.ok.injEq] at h
          subst h
          exact ⟨names, cs, rfl, hr, hd⟩

theorem decodeContent_le {p : Profile} {ext : Externals} {v body out : List UInt8}
    (h : decodeContent p ext (some v) body = .ok out) :
    out = body ∨ out.length ≤ p.maxDecoded := by
  obtain ⟨_, cs, _, _, hd⟩ := decodeContent_sound h
  cases cs with
  | nil => exact .inl (by cases hd; rfl)
  | cons c cs => exact .inr (Profile.decode_le hd)

theorem decodeContent_gzip {L : Nat} (ext : Externals) {data : List UInt8} (hl : data.length ≤ L) :
    decodeContent (httpProfile L) ext (some (ascii "gzip")) (Gzip.encoder data) = .ok data := by
  have h1 : parseContentEncoding (ascii "gzip") = some [ascii "gzip"] := by decide
  have h2 : resolve [ascii "gzip"] = .ok [.gzip] := rfl
  have h3 : (httpProfile L).decode ext [.gzip] (Gzip.encoder data) = .ok data :=
    Profile.decode_single (e := Gzip.encoder) rfl rfl hl
  simp only [decodeContent, h1, h2, h3]
  rfl

theorem decodeContent_deflate {L : Nat} (ext : Externals) {data : List UInt8}
    (hl : data.length ≤ L) :
    decodeContent (httpProfile L) ext (some (ascii "deflate")) (Zlib.encoder data) = .ok data := by
  have h1 : parseContentEncoding (ascii "deflate") = some [ascii "deflate"] := by decide
  have h2 : resolve [ascii "deflate"] = .ok [.deflate] := rfl
  have h3 : (httpProfile L).decode ext [.deflate] (Zlib.encoder data) = .ok data :=
    Profile.decode_single (e := Zlib.encoder) rfl rfl hl
  simp only [decodeContent, h1, h2, h3]
  rfl

theorem gzip_members_gnu :
    Gzip.decoder.members gzipGnu.data.toList = some helloBytes.data.toList := by
  have h := (Gzip.decompress_eq gzipGnu).symm.trans Gzip.decompress_gnu
  rw [Option.map_eq_some_iff] at h
  obtain ⟨x, hx, hxe⟩ := h
  rw [hx, ← hxe]

theorem decodeContent_gnu {L : Nat} (ext : Externals) (hl : 5 ≤ L) :
    decodeContent (httpProfile L) ext (some (ascii "x-gzip")) gzipGnu.data.toList =
      .ok helloBytes.data.toList := by
  have h1 : parseContentEncoding (ascii "x-gzip") = some [ascii "x-gzip"] := by decide
  have h2 : resolve [ascii "x-gzip"] = .ok [.gzip] := rfl
  simp only [decodeContent, h1, h2]
  have h3 : (httpProfile L).decode ext [.gzip] gzipGnu.data.toList =
      .ok helloBytes.data.toList := by
    simp only [Profile.decode, decodeChain, Profile.stage]
    have hs : (httpProfile L).supports ext .gzip = true := rfl
    simp only [hs, ↓reduceIte]
    exact Registry.guarded_eq_ok_iff.mpr
      ⟨by simp only [Registry.stage, Coding.decoder?, gzip_members_gnu],
        decide_eq_true (by show 5 ≤ L; exact hl)⟩
  rw [h3]
  rfl

theorem decodeContent_gnu_tooLarge (ext : Externals) :
    decodeContent (httpProfile 4) ext (some (ascii "x-gzip")) gzipGnu.data.toList =
      .error (.stage (.tooLarge .gzip)) := by
  have h1 : parseContentEncoding (ascii "x-gzip") = some [ascii "x-gzip"] := by decide
  have h2 : resolve [ascii "x-gzip"] = .ok [.gzip] := rfl
  simp only [decodeContent, h1, h2]
  simp only [Profile.decode, decodeChain, Profile.stage, guarded, Registry.stage,
    Coding.decoder?, gzip_members_gnu]
  rfl

end Silmaril.Proofs.Net.Http.ContentCoding
