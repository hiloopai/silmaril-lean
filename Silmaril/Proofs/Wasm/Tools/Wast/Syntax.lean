module

public import Silmaril.Wasm.Tools.Wast.Syntax.Defs

/-!
# Round trips of the `.wast` script grammar: proofs

Proofs of the laws stated in `Silmaril.Wasm.Tools.Wast.Syntax.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

open Silmaril.Formats Silmaril.Formats.SExpEncoding

/-! ## Lists and atoms -/

@[simp] theorem elems?_lst (xs : List SExp) : elems? (lst xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [lst, elems?, ih]

theorem elems?_eq_some {x : SExp} {xs : List SExp} (h : elems? x = some xs) : lst xs = x := by
  induction x generalizing xs with
  | nil => simp [elems?] at h; subst h; rfl
  | atom _ => simp [elems?] at h
  | cons a r _ ihr =>
    simp only [elems?, Option.map_eq_some_iff] at h
    obtain ⟨ys, hys, rfl⟩ := h
    simp [lst, ihr hys]

@[simp] theorem strs?_map (ss : List (List UInt8)) : strs? (ss.map strA) = some ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [strs?, str?, ih]

theorem strs?_eq_some {xs : List SExp} {ss : List (List UInt8)} (h : strs? xs = some ss) :
    ss.map strA = xs := by
  induction xs generalizing ss with
  | nil => simp [strs?] at h; subst h; rfl
  | cons x xs ih =>
    simp only [strs?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    have hx : x = strA b := by
      unfold str? at hb; split at hb <;> simp_all
    simp [hx, ih hbs]

@[simp] theorem syms?_map (ss : List String) : syms? (ss.map sym) = some ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [syms?, sym?, ih]

theorem syms?_eq_some {xs : List SExp} {ss : List String} (h : syms? xs = some ss) :
    ss.map sym = xs := by
  induction xs generalizing ss with
  | nil => simp [syms?] at h; subst h; rfl
  | cons x xs ih =>
    simp only [syms?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    have hx : x = sym b := by
      unfold sym? at hb; split at hb <;> simp_all
    simp [hx, ih hbs]

theorem takeId_eq {xs : List SExp} {id : Option String} {r : List SExp}
    (h : takeId xs = (id, r)) : idOpt id ++ r = xs := by
  unfold takeId at h
  split at h
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl

/-- A list whose head is not an identifier. -/
def NoIdHead (xs : List SExp) : Prop := ∀ n, xs.head? ≠ some (ident n)

theorem takeId_idOpt (id : Option String) (r : List SExp) (h : id = none → NoIdHead r) :
    takeId (idOpt id ++ r) = (id, r) := by
  cases id with
  | some n => simp [idOpt, takeId]
  | none =>
    simp only [idOpt, List.nil_append]
    unfold takeId
    split
    · rename_i n xs
      exact absurd rfl (h rfl n)
    · rfl

/-! ## Values -/

theorem lst_cons (x : SExp) (xs : List SExp) : lst (x :: xs) = .cons x (lst xs) := rfl

theorem Val.toSExp_cons (v : Val) : ∃ h r, v.toSExp = .cons (sym h) r := by
  cases v <;> exact ⟨_, _, rfl⟩

theorem Val.mixedTail?_listToSExps_nonStr (vs : List Val) :
    ∀ b, (Val.listToSExps vs).head? ≠ some (strA b) := by
  intro b
  cases vs with
  | nil => simp [Val.listToSExps]
  | cons v vs =>
    obtain ⟨h, r, hv⟩ := Val.toSExp_cons v
    simp [Val.listToSExps, hv]

theorem Val.mixedTail?_strs (ss : List (List UInt8)) (L : List SExp) :
    Val.mixedTail? (lst (ss.map strA ++ L)) =
      (Val.mixedTail? (lst L)).map (fun p => (ss ++ p.1, p.2)) := by
  induction ss with
  | nil => simp
  | cons b ss ih =>
    simp only [List.map_cons, List.cons_append, lst_cons]
    rw [Val.mixedTail?, ih]
    simp [Option.map_map, Function.comp_def]

mutual
  theorem Val.ofSExp?_toSExp : ∀ v : Val, v.WF → Val.ofSExp? v.toSExp = some v
    | .lit h as, hw => by
      have hh : h ∈ litHeads := hw
      simp [Val.toSExp, Val.ofSExp?, hh]
    | .mixed h ss vs, hw => by
      have hh : h ∉ litHeads := hw.1
      have hvs := Val.mixedTail?_lst vs hw.2
      simp only [Val.toSExp, Val.ofSExp?, hh, ite_false]
      rw [Val.mixedTail?_strs, hvs]
      simp

  theorem Val.mixedTail?_lst : ∀ vs : List Val, Val.listWF vs →
      Val.mixedTail? (lst (Val.listToSExps vs)) = some ([], vs)
    | [], _ => rfl
    | v :: vs, hw => by
      obtain ⟨h, r, hv⟩ := Val.toSExp_cons v
      have h1 := Val.ofSExp?_toSExp v hw.1
      have h2 := Val.valsOf?_lst vs hw.2
      simp only [Val.listToSExps, lst_cons]
      rw [hv] at h1 ⊢
      simp [Val.mixedTail?, h1, h2]

  theorem Val.valsOf?_lst : ∀ vs : List Val, Val.listWF vs →
      Val.valsOf? (lst (Val.listToSExps vs)) = some vs
    | [], _ => rfl
    | v :: vs, hw => by
      have h1 := Val.ofSExp?_toSExp v hw.1
      have h2 := Val.valsOf?_lst vs hw.2
      simp [Val.listToSExps, lst_cons, Val.valsOf?, h1, h2]
end

theorem Val.mixedTail?_cons_nonStr {x r : SExp} (hx : ∀ b, x ≠ strA b) :
    Val.mixedTail? (.cons x r) =
      (do let v ← Val.ofSExp? x; let vs ← Val.valsOf? r; pure ([], v :: vs)) := by
  match x, hx with
  | .atom (.str b), hx => exact absurd rfl (hx b)
  | .atom (.sym _), _ => rfl
  | .atom (.id _), _ => rfl
  | .nil, _ => rfl
  | .cons _ _, _ => rfl

theorem Val.lst_of_mixedTail?_gen (x r : SExp) (p : List (List UInt8) × List Val)
    (hx : ∀ b, x ≠ strA b) (hr : Val.mixedTail? (.cons x r) = some p)
    (ih1 : ∀ v, Val.ofSExp? x = some v → v.toSExp = x)
    (ih2 : ∀ vs, Val.valsOf? r = some vs → lst (Val.listToSExps vs) = r) :
    lst (p.1.map strA ++ Val.listToSExps p.2) = .cons x r := by
  rw [Val.mixedTail?_cons_nonStr hx] at hr
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hr
  obtain ⟨v, hv, vs, hvs, rfl⟩ := hr
  simp [Val.listToSExps, lst_cons, ih1 v hv, ih2 vs hvs]

mutual
  theorem Val.toSExp_of_ofSExp? : ∀ (x : SExp) (v : Val), Val.ofSExp? x = some v → v.toSExp = x
    | .cons (.atom (.sym h)) r, v, hx => by
      unfold Val.ofSExp? at hx
      split at hx
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at hx
        obtain ⟨xs, hxs, as, has, rfl⟩ := hx
        simp [Val.toSExp, syms?_eq_some has, elems?_eq_some hxs]
      · simp only [Option.map_eq_some_iff] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        simp [Val.toSExp, Val.lst_of_mixedTail? r p hp]
    | .nil, v, hx => by simp [Val.ofSExp?] at hx
    | .atom _, v, hx => by simp [Val.ofSExp?] at hx
    | .cons .nil _, v, hx => by simp [Val.ofSExp?] at hx
    | .cons (.cons _ _) _, v, hx => by simp [Val.ofSExp?] at hx
    | .cons (.atom (.str _)) _, v, hx => by simp [Val.ofSExp?] at hx
    | .cons (.atom (.id _)) _, v, hx => by simp [Val.ofSExp?] at hx

  theorem Val.lst_of_mixedTail? : ∀ (r : SExp) (p : List (List UInt8) × List Val),
      Val.mixedTail? r = some p → lst (p.1.map strA ++ Val.listToSExps p.2) = r
    | .nil, p, hr => by
      simp only [Val.mixedTail?, Option.some.injEq] at hr; subst hr; rfl
    | .atom _, p, hr => by simp [Val.mixedTail?] at hr
    | .cons (.atom (.str b)) r, p, hr => by
      simp only [Val.mixedTail?, Option.map_eq_some_iff] at hr
      obtain ⟨q, hq, rfl⟩ := hr
      simp [lst_cons, Val.lst_of_mixedTail? r q hq]
    | .cons (.atom (.sym t)) r, p, hr => Val.lst_of_mixedTail?_gen _ r p (by simp) hr
        (Val.toSExp_of_ofSExp? _) (Val.lst_of_valsOf? r)
    | .cons (.atom (.id t)) r, p, hr => Val.lst_of_mixedTail?_gen _ r p (by simp) hr
        (Val.toSExp_of_ofSExp? _) (Val.lst_of_valsOf? r)
    | .cons .nil r, p, hr => Val.lst_of_mixedTail?_gen _ r p (by simp) hr
        (Val.toSExp_of_ofSExp? _) (Val.lst_of_valsOf? r)
    | .cons (.cons a c) r, p, hr => Val.lst_of_mixedTail?_gen _ r p (by simp) hr
        (Val.toSExp_of_ofSExp? _) (Val.lst_of_valsOf? r)

  theorem Val.lst_of_valsOf? : ∀ (r : SExp) (vs : List Val),
      Val.valsOf? r = some vs → lst (Val.listToSExps vs) = r
    | .nil, vs, hr => by
      simp only [Val.valsOf?, Option.some.injEq] at hr; subst hr; rfl
    | .atom _, vs, hr => by simp [Val.valsOf?] at hr
    | .cons x r, vs, hr => by
      simp only [Val.valsOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hr
      obtain ⟨v, hv, ws, hws, rfl⟩ := hr
      simp [Val.listToSExps, lst_cons, Val.toSExp_of_ofSExp? x v hv, Val.lst_of_valsOf? r ws hws]
end

theorem Val.listOf?_listToSExps : ∀ vs : List Val, Val.listWF vs →
    Val.listOf? (Val.listToSExps vs) = some vs
  | [], _ => rfl
  | v :: vs, hw => by
    simp [Val.listToSExps, Val.listOf?, Val.ofSExp?_toSExp v hw.1,
      Val.listOf?_listToSExps vs hw.2]

theorem Val.listToSExps_of_listOf? : ∀ (xs : List SExp) (vs : List Val),
    Val.listOf? xs = some vs → Val.listToSExps vs = xs
  | [], vs, h => by simp only [Val.listOf?, Option.some.injEq] at h; subst h; rfl
  | x :: xs, vs, h => by
    simp only [Val.listOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, ws, hws, rfl⟩ := h
    simp [Val.listToSExps, Val.toSExp_of_ofSExp? x v hv, Val.listToSExps_of_listOf? xs ws hws]

/-! ## Modules -/

@[simp] theorem ModKind.ofKw?_kw (k : ModKind) : ModKind.ofKw? k.kw = some k := by
  cases k <;> rfl

theorem ModKind.ofKw?_eq_some {s : String} {k : ModKind} (h : ModKind.ofKw? s = some k) :
    k.kw = s := by
  revert h
  unfold ModKind.ofKw?
  split <;> intro h <;> cases h <;> rfl

theorem ModKind.kw_ne (k : ModKind) (s : String) (h1 : s ≠ "module") (h2 : s ≠ "component") :
    k.kw ≠ s := by
  cases k <;> simp [ModKind.kw] <;> intro h <;> simp_all

theorem reservedHead_false {x : SExp} (h : reservedHead x = false) :
    x ≠ sym "binary" ∧ x ≠ sym "quote" ∧ x ≠ sym "definition" ∧ x ≠ sym "instance" ∧
      ∀ n, x ≠ ident n := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl; cases h
  · rintro rfl; cases h
  · rintro rfl; cases h
  · rintro rfl; cases h
  · intro n hx; subst hx; cases h

theorem Body.ofSExps?_toSExps {id : Option String} {b : Body} (hb : b.WF id) :
    Body.ofSExps? b.toSExps = some b := by
  cases b with
  | binary ss => simp [Body.ofSExps?, Body.toSExps]
  | fields xs =>
    have hx : xs.head? ≠ some (sym "binary") := by
      cases id with
      | none =>
        intro h
        exact (reservedHead_false (hb _ h)).1 rfl
      | some _ => exact hb
    simp [Body.ofSExps?, Body.toSExps, hx]

theorem Body.toSExps_of_ofSExps? {xs : List SExp} {b : Body} (h : Body.ofSExps? xs = some b) :
    b.toSExps = xs := by
  unfold Body.ofSExps? at h
  split at h
  · rename_i hh
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨ss, hss, rfl⟩ := h
    have hss' := strs?_eq_some hss
    cases xs with
    | nil => simp at hh
    | cons y ys =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      simp [Body.toSExps, hh, hss']
  · simp only [Option.some.injEq] at h; subst h; rfl

/-- The head of a well-formed body after an absent identifier is not an identifier. -/
theorem Body.noIdHead {b : Body} (hb : b.WF none) : NoIdHead b.toSExps := by
  intro n h
  cases b with
  | binary ss => simp [Body.toSExps] at h
  | fields xs => exact (reservedHead_false (hb _ h)).2.2.2.2 n rfl

theorem Body.noKwHead {id : Option String} {b : Body} (hb : b.WF id) (s : String)
    (hs : s = "quote" ∨ s = "definition" ∨ s = "instance") :
    (idOpt id ++ b.toSExps).head? ≠ some (sym s) := by
  cases id with
  | some n => simp [idOpt]
  | none =>
    show (b.toSExps).head? ≠ _
    cases b with
    | binary ss =>
      simp only [Body.toSExps, List.head?_cons, ne_eq, Option.some.injEq, SExp2.atom.injEq,
        Atom.sym.injEq]
      rcases hs with rfl | rfl | rfl <;> decide
    | fields xs =>
      intro h
      have hr := reservedHead_false (hb _ h)
      rcases hs with rfl | rfl | rfl
      · exact hr.2.1 rfl
      · exact hr.2.2.1 rfl
      · exact hr.2.2.2.1 rfl

theorem Body.noQuoteHead {id : Option String} {b : Body} (hb : b.WF id) :
    (idOpt id ++ b.toSExps).head? ≠ some (sym "quote") :=
  Body.noKwHead hb _ (.inl rfl)

theorem QuoteWat.ofRest?_wat {k : ModKind} {id : Option String} {b : Body} (hb : b.WF id) :
    QuoteWat.ofRest? k (idOpt id ++ b.toSExps) = some (.wat k id b) := by
  have hq := Body.noQuoteHead hb
  have ht : takeId (idOpt id ++ b.toSExps) = (id, b.toSExps) :=
    takeId_idOpt id _ (fun h => by subst h; exact Body.noIdHead hb)
  unfold QuoteWat.ofRest?
  simp only [hq, ↓reduceIte, ht]
  simp [Body.ofSExps?_toSExps hb]

theorem QuoteWat.ofRest?_quote (k : ModKind) (ss : List (List UInt8)) :
    QuoteWat.ofRest? k (sym "quote" :: ss.map strA) = some (.quote k ss) := by
  simp [QuoteWat.ofRest?]

theorem QuoteWat.ofSExps?_toSExps {m : QuoteWat} (hm : m.WF) :
    QuoteWat.ofSExps? m.toSExps = some m := by
  cases m with
  | wat k id b => simp [QuoteWat.ofSExps?, QuoteWat.toSExps, QuoteWat.ofRest?_wat hm]
  | quote k ss => simp [QuoteWat.ofSExps?, QuoteWat.toSExps, QuoteWat.ofRest?_quote]

theorem QuoteWat.toSExps_of_ofRest? {k : ModKind} {xs : List SExp} {m : QuoteWat}
    (h : QuoteWat.ofRest? k xs = some m) : m.toSExps = sym k.kw :: xs := by
  unfold QuoteWat.ofRest? at h
  split at h
  · rename_i hh
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨ss, hss, rfl⟩ := h
    have hss' := strs?_eq_some hss
    cases xs with
    | nil => simp at hh
    | cons y ys =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      simp [QuoteWat.toSExps, hh, hss']
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    have ht := takeId_eq (xs := xs) (id := (takeId xs).1) (r := (takeId xs).2) rfl
    simp [QuoteWat.toSExps, Body.toSExps_of_ofSExps? hb, ht]

theorem QuoteWat.toSExps_of_ofSExps? {xs : List SExp} {m : QuoteWat}
    (h : QuoteWat.ofSExps? xs = some m) : m.toSExps = xs := by
  unfold QuoteWat.ofSExps? at h
  split at h
  · rename_i k rest
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨mk, hk, hm⟩ := h
    rw [QuoteWat.toSExps_of_ofRest? hm, ModKind.ofKw?_eq_some hk]
  · simp at h

theorem QuoteWat.ofSExp?_toSExp {m : QuoteWat} (hm : m.WF) :
    QuoteWat.ofSExp? m.toSExp = some m := by
  simp [QuoteWat.ofSExp?, QuoteWat.toSExp, QuoteWat.ofSExps?_toSExps hm]

theorem QuoteWat.toSExp_of_ofSExp? {x : SExp} {m : QuoteWat}
    (h : QuoteWat.ofSExp? x = some m) : m.toSExp = x := by
  simp only [QuoteWat.ofSExp?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨xs, hxs, hm⟩ := h
  simp [QuoteWat.toSExp, QuoteWat.toSExps_of_ofSExps? hm, elems?_eq_some hxs]

/-! ## Actions -/

theorem Invoke.ofSExps?_toSExps {i : Invoke} (hi : i.WF) :
    Invoke.ofSExps? i.toSExps = some i := by
  have ht : takeId (idOpt i.module ++ strA i.name :: Val.listToSExps i.args) =
      (i.module, strA i.name :: Val.listToSExps i.args) :=
    takeId_idOpt _ _ (fun _ n h => by simp at h)
  simp [Invoke.ofSExps?, Invoke.toSExps, ht, Val.listOf?_listToSExps _ hi]

theorem Invoke.toSExps_of_ofSExps? {xs : List SExp} {i : Invoke}
    (h : Invoke.ofSExps? xs = some i) : i.toSExps = xs := by
  unfold Invoke.ofSExps? at h
  split at h
  · rename_i k rest
    split at h
    · rename_i hk
      subst hk
      split at h
      · rename_i m n args heq
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨vs, hvs, rfl⟩ := h
        have ht := takeId_eq heq
        simp [Invoke.toSExps, Val.listToSExps_of_listOf? _ _ hvs, ← ht]
      · simp at h
    · simp at h
  · simp at h

theorem Exec.ofSExp?_toSExp {e : Exec} (he : e.WF) : Exec.ofSExp? e.toSExp = some e := by
  match e, he with
  | .invoke i, he =>
    have hi : Invoke.ofSExps? i.toSExps = some i := Invoke.ofSExps?_toSExps he
    simp only [Invoke.toSExps] at hi
    simp [Exec.ofSExp?, Exec.toSExp, Invoke.toSExps, hi]
  | .wat (.wat k id b), he =>
    have h1 : k.kw ≠ "invoke" := ModKind.kw_ne k _ (by decide) (by decide)
    have h2 : k.kw ≠ "get" := ModKind.kw_ne k _ (by decide) (by decide)
    simp [Exec.ofSExp?, Exec.toSExp, QuoteWat.toSExp, QuoteWat.toSExps, h1, h2,
      QuoteWat.ofRest?_wat (k := k) he]
  | .get m n, _ =>
    have ht : takeId (idOpt m ++ [strA n]) = (m, [strA n]) :=
      takeId_idOpt _ _ (fun _ n h => by simp at h)
    simp [Exec.ofSExp?, Exec.toSExp, ht]

/-- An `Exec` read from a `get` form is printed back. -/
theorem Exec.toSExp_of_ofSExp?_get {x : SExp} {rest : List SExp} {e : Exec}
    (hxs : elems? x = some (sym "get" :: rest)) (h : Exec.ofSExp? x = some e) :
    e.toSExp = x := by
  rw [← elems?_eq_some hxs]
  simp only [Exec.ofSExp?, Option.bind_eq_bind, hxs, Option.bind_some,
    ite_eq_right (show ¬ ("get" = "invoke") by decide), ↓reduceIte] at h
  split at h
  · rename_i m n heq
    simp only [Option.some.injEq] at h
    subst h
    simp [Exec.toSExp, ← takeId_eq heq]
  · simp at h

/-- An `Exec` read from a module form is printed back. -/
theorem Exec.toSExp_of_ofSExp?_wat {x : SExp} {k : String} {rest : List SExp} {e : Exec}
    (hxs : elems? x = some (sym k :: rest)) (hk1 : ¬ k = "invoke") (hk2 : ¬ k = "get")
    (h : Exec.ofSExp? x = some e) : e.toSExp = x := by
  rw [← elems?_eq_some hxs]
  simp only [Exec.ofSExp?, Option.bind_eq_bind, hxs, Option.bind_some, ite_eq_right hk1, ite_eq_right hk2] at h
  split at h
  · rename_i mk hmk
    split at h
    · rename_i k' id b heq
      simp only [Option.some.injEq] at h
      subst h
      have hq : QuoteWat.toSExps (.wat k' id b) = sym mk.kw :: rest := QuoteWat.toSExps_of_ofRest? heq
      simp only [Exec.toSExp, QuoteWat.toSExp]
      rw [hq, ModKind.ofKw?_eq_some hmk]
    · simp at h
  · simp at h

theorem Exec.toSExp_of_ofSExp? {x : SExp} {e : Exec} (h : Exec.ofSExp? x = some e) :
    e.toSExp = x := by
  have h' := h
  simp only [Exec.ofSExp?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h'
  obtain ⟨xs, hxs, h'⟩ := h'
  split at h'
  · rename_i k rest
    by_cases hk1 : k = "invoke"
    · subst hk1
      simp only [↓reduceIte, Option.map_eq_some_iff] at h'
      obtain ⟨i, hi, rfl⟩ := h'
      rw [← elems?_eq_some hxs]
      simp [Exec.toSExp, Invoke.toSExps_of_ofSExps? hi]
    by_cases hk2 : k = "get"
    · subst hk2
      exact Exec.toSExp_of_ofSExp?_get hxs h
    · exact Exec.toSExp_of_ofSExp?_wat hxs hk1 hk2 h
  · simp at h'

/-! ## Directives: reading what is printed -/

theorem lst_cons2 (a b : SExp) (xs : List SExp) :
    lst (a :: b :: xs) = .cons a (.cons b (lst xs)) := rfl

/-- Reading a non-`thread` directive list is reading its keyword and elements. -/
theorem Directive.ofSExp?_lst {k : String} {rest : List SExp} (hk : k ≠ "thread") :
    Directive.ofSExp? (lst (sym k :: rest)) = Directive.ofKw? k rest := by
  rw [Directive.ofSExp?.eq_def]
  split
  · rename_i n m ds heq
    simp only [lst_cons, SExp2.cons.injEq, SExp2.atom.injEq, Atom.sym.injEq] at heq
    exact absurd heq.1 hk
  · rename_i n ds heq
    simp only [lst_cons, SExp2.cons.injEq, SExp2.atom.injEq, Atom.sym.injEq] at heq
    exact absurd heq.1 hk
  · simp [Directive.ofElems?]

/-- Keywords other than the module keywords are not `ModKind`s. -/
theorem ModKind.ofKw?_none {s : String} (h1 : s ≠ "module") (h2 : s ≠ "component") :
    ModKind.ofKw? s = none := by
  unfold ModKind.ofKw?
  split <;> simp_all

theorem moduleForm?_module {k : ModKind} {m : QuoteWat} (hm : m.WF)
    (hk : ∀ k', m.toSExps.head? = some (sym k'.kw) → k' = k) :
    moduleForm? k m.toSExps.tail = some (.module m) := by
  cases m with
  | wat k' id b =>
    have hk' : k' = k := hk k' rfl
    subst hk'
    have hd := Body.noKwHead hm "definition" (.inr (.inl rfl))
    have hi := Body.noKwHead hm "instance" (.inr (.inr rfl))
    simp only [QuoteWat.toSExps, List.tail_cons]
    simp only [moduleForm?, hd, hi, ↓reduceIte, QuoteWat.ofRest?_wat hm, Option.map_some]
  | quote k' ss =>
    have hk' : k' = k := hk k' rfl
    subst hk'
    simp [moduleForm?, QuoteWat.toSExps, QuoteWat.ofRest?_quote]

theorem Directive.ofKw?_kw (k : ModKind) (rest : List SExp) :
    Directive.ofKw? k.kw rest = moduleForm? k rest := by
  cases k <;> rfl

theorem Directive.ofKw?_module {m : QuoteWat} (hm : m.WF) :
    ∃ k : ModKind, m.toSExps = sym k.kw :: m.toSExps.tail ∧
      Directive.ofKw? k.kw m.toSExps.tail = some (.module m) := by
  cases m with
  | wat k id b =>
    refine ⟨k, rfl, ?_⟩
    have h := moduleForm?_module (k := k) (m := .wat k id b) hm (fun k' h => by
      cases k <;> cases k' <;> simp_all [QuoteWat.toSExps, ModKind.kw])
    rw [Directive.ofKw?_kw]; simpa [QuoteWat.toSExps] using h
  | quote k ss =>
    refine ⟨k, rfl, ?_⟩
    have h := moduleForm?_module (k := k) (m := .quote k ss) hm (fun k' h => by
      cases k <;> cases k' <;> simp_all [QuoteWat.toSExps, ModKind.kw])
    rw [Directive.ofKw?_kw]; simpa [QuoteWat.toSExps] using h

/-- The keyword of a quoted or text module is a module keyword. -/
theorem QuoteWat.toSExp_eq (m : QuoteWat) :
    ∃ k : ModKind, m.toSExp = lst (sym k.kw :: m.toSExps.tail) := by
  cases m <;> exact ⟨_, rfl⟩

theorem modAssert?_print (mk : QuoteWat → List UInt8 → Directive) (nq : Bool)
    {m : QuoteWat} (hm : m.WF) (hq : nq = true → ∀ k ss, m ≠ .quote k ss) (s : List UInt8) :
    modAssert? mk nq [m.toSExp, strA s] = some (mk m s) := by
  simp only [modAssert?, QuoteWat.ofSExp?_toSExp hm, Option.bind_eq_bind, Option.bind_some]
  cases m with
  | wat k id b => cases nq <;> rfl
  | quote k ss =>
    cases nq with
    | false => rfl
    | true => exact absurd rfl (hq rfl k ss)

theorem execAssert?_print (mk : Exec → List UInt8 → Directive) {e : Exec} (he : e.WF)
    (s : List UInt8) : execAssert? mk [e.toSExp, strA s] = some (mk e s) := by
  simp [execAssert?, Exec.ofSExp?_toSExp he]

/-- Every printed directive starts with its keyword. -/

theorem Directive.kw_ne_shared (d : Directive) : d.kw ≠ "shared" := by
  match d with
  | .module (.wat k ..) | .module (.quote k ..) | .moduleDefinition k .. | .moduleInstance k .. =>
    exact ModKind.kw_ne k _ (by decide) (by decide)
  | .assertMalformed .. | .assertMalformedCustom .. | .assertInvalid .. | .assertInvalidCustom ..
  | .assertUnlinkable .. | .register .. | .invoke .. | .assertTrap .. | .assertReturn ..
  | .assertExhaustion .. | .assertException .. | .assertSuspension .. | .thread ..
  | .wait .. => simp only [Directive.kw]; decide

theorem Directive.toSExp_head (d : Directive) : ∃ r, d.toSExp = .cons (sym d.kw) r := by
  cases d with
  | module m => cases m <;> exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

/-! ## Directives: what is read is printed back -/

theorem modAssert?_inv {mk : QuoteWat → List UInt8 → Directive} {nq : Bool} {xs : List SExp}
    {d : Directive} (h : modAssert? mk nq xs = some d) :
    ∃ m s, xs = [m.toSExp, strA s] ∧ d = mk m s := by
  unfold modAssert? at h
  split at h
  · rename_i m s
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, h⟩ := h
    have hm := QuoteWat.toSExp_of_ofSExp? hq
    split at h
    · simp at h
    · simp only [Option.pure_def, Option.some.injEq] at h
      exact ⟨q, s, by rw [hm], h.symm⟩
  · simp at h

theorem execAssert?_inv {mk : Exec → List UInt8 → Directive} {xs : List SExp} {d : Directive}
    (h : execAssert? mk xs = some d) : ∃ e s, xs = [e.toSExp, strA s] ∧ d = mk e s := by
  unfold execAssert? at h
  split at h
  · rename_i e s
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨e', he, rfl⟩ := h
    exact ⟨e', s, by rw [Exec.toSExp_of_ofSExp? he], rfl⟩
  · simp at h

/-- A `module definition` form that is read is printed back. -/
theorem moduleForm?_inv_definition {k : ModKind} {rest : List SExp} {d : Directive}
    (hd : rest.head? = some (sym "definition")) (h : moduleForm? k rest = some d) :
    d.toSExp = lst (sym k.kw :: rest) := by
  rw [moduleForm?, ite_eq_left hd, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rfl⟩ := h
  cases rest with
  | nil => simp at hd
  | cons y ys =>
    simp only [List.head?_cons, Option.some.injEq] at hd
    subst hd
    have ht := takeId_eq (xs := ys) (id := (takeId ys).1) (r := (takeId ys).2) rfl
    simp [Directive.toSExp, Body.toSExps_of_ofSExps? hb, ht]

/-- A `module instance` form that is read is printed back. -/
theorem moduleForm?_inv_instance {k : ModKind} {rest : List SExp} {d : Directive}
    (hd : ¬ rest.head? = some (sym "definition")) (hi : rest.head? = some (sym "instance"))
    (h : moduleForm? k rest = some d) : d.toSExp = lst (sym k.kw :: rest) := by
  rw [moduleForm?, ite_eq_right hd, ite_eq_left hi] at h
  cases rest with
  | nil => simp at hi
  | cons y ys =>
    simp only [List.head?_cons, Option.some.injEq] at hi
    subst hi
    simp only [List.tail_cons] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem moduleForm?_inv {k : ModKind} {rest : List SExp} {d : Directive}
    (h : moduleForm? k rest = some d) : d.toSExp = lst (sym k.kw :: rest) := by
  by_cases hd : rest.head? = some (sym "definition")
  · exact moduleForm?_inv_definition hd h
  by_cases hi : rest.head? = some (sym "instance")
  · exact moduleForm?_inv_instance hd hi h
  rw [moduleForm?, ite_eq_right hd, ite_eq_right hi, Option.map_eq_some_iff] at h
  obtain ⟨m, hm, rfl⟩ := h
  show lst m.toSExps = _
  rw [QuoteWat.toSExps_of_ofRest? hm]

theorem registerOf?_inv {xs : List SExp} {d : Directive} (h : registerOf? xs = some d) :
    d.toSExp = lst (sym "register" :: xs) := by
  unfold registerOf? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem assertReturnOf?_inv {xs : List SExp} {d : Directive} (h : assertReturnOf? xs = some d) :
    d.toSExp = lst (sym "assert_return" :: xs) := by
  unfold assertReturnOf? at h
  split at h
  · rename_i e rs
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨e', he, vs, hvs, rfl⟩ := h
    simp [Directive.toSExp, Exec.toSExp_of_ofSExp? he, Val.listToSExps_of_listOf? _ _ hvs,
      lst_cons]
  · simp at h

theorem assertExhaustionOf?_inv {xs : List SExp} {d : Directive}
    (h : assertExhaustionOf? xs = some d) : d.toSExp = lst (sym "assert_exhaustion" :: xs) := by
  unfold assertExhaustionOf? at h
  split at h
  · rename_i i s
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨is, his, i', hi, rfl⟩ := h
    simp [Directive.toSExp, Invoke.toSExps_of_ofSExps? hi, elems?_eq_some his]
  · simp at h

theorem invokeOf?_inv {rest : List SExp} {d : Directive}
    (h : (Invoke.ofSExps? (sym "invoke" :: rest)).map Directive.invoke = some d) :
    d.toSExp = lst (sym "invoke" :: rest) := by
  rw [Option.map_eq_some_iff] at h
  obtain ⟨i, hi, rfl⟩ := h
  simp [Directive.toSExp, Invoke.toSExps_of_ofSExps? hi]

theorem assertExceptionOf?_inv {e : SExp} {d : Directive}
    (h : (Exec.ofSExp? e).map Directive.assertException = some d) :
    d.toSExp = lst (sym "assert_exception" :: [e]) := by
  rw [Option.map_eq_some_iff] at h
  obtain ⟨e', he, rfl⟩ := h
  simp [Directive.toSExp, Exec.toSExp_of_ofSExp? he]

theorem Directive.ofKw?_inv {k : String} {rest : List SExp} {d : Directive}
    (h : Directive.ofKw? k rest = some d) : d.toSExp = lst (sym k :: rest) := by
  unfold Directive.ofKw? at h
  split at h
  all_goals first
    | exact moduleForm?_inv h | exact registerOf?_inv h | exact invokeOf?_inv h
    | exact assertReturnOf?_inv h | exact assertExhaustionOf?_inv h
    | (obtain ⟨m, s, rfl, rfl⟩ := modAssert?_inv h; rfl)
    | (obtain ⟨e, s, rfl, rfl⟩ := execAssert?_inv h; rfl)
    | (simp at h)
    | (split at h <;> first
        | (simp at h; done)
        | exact assertExceptionOf?_inv h
        | (simp only [Option.some.injEq] at h; subst h; rfl))

theorem Directive.ofElems?_inv {xs : List SExp} {d : Directive}
    (h : Directive.ofElems? xs = some d) : d.toSExp = lst xs := by
  unfold Directive.ofElems? at h
  split at h
  · exact Directive.ofKw?_inv h
  · simp at h

theorem Directive.ofElems_bind_inv {x : SExp} {d : Directive}
    (h : (elems? x >>= Directive.ofElems?) = some d) : d.toSExp = x := by
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨xs, hxs, hd⟩ := h
  rw [Directive.ofElems?_inv hd, elems?_eq_some hxs]

theorem Directive.dirsOf?_nil_inv {ds : List Directive} (h : Directive.dirsOf? .nil = some ds) :
    lst (Directive.listToSExps ds) = .nil := by
  simp only [Directive.dirsOf?, Option.some.injEq] at h
  subst h
  rfl

theorem Directive.dirsOf?_cons_inv {x r : SExp} {ds : List Directive}
    (ih1 : ∀ d, Directive.ofSExp? x = some d → d.toSExp = x)
    (ih2 : ∀ ds, Directive.dirsOf? r = some ds → lst (Directive.listToSExps ds) = r)
    (h : Directive.dirsOf? (.cons x r) = some ds) : lst (Directive.listToSExps ds) = .cons x r := by
  simp only [Directive.dirsOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨d, hd, ds', hds', rfl⟩ := h
  simp [Directive.listToSExps, lst_cons, ih1 d hd, ih2 ds' hds']

theorem Directive.toSExp_of_ofSExp? (x : SExp) :
    ∀ d, Directive.ofSExp? x = some d → d.toSExp = x := by
  refine Directive.ofSExp?.induct
    (fun x => ∀ d, Directive.ofSExp? x = some d → d.toSExp = x)
    (fun r => ∀ ds, Directive.dirsOf? r = some ds → lst (Directive.listToSExps ds) = r)
    ?_ ?_ ?_ ?_ ?_ ?_ x
  · intro n m ds ih d h
    rw [Directive.ofSExp?.eq_1, Option.map_eq_some_iff] at h
    obtain ⟨ds', hds, rfl⟩ := h
    simp [Directive.toSExp, lst, ← ih ds' hds]
  · intro n ds hns ih d h
    rw [Directive.ofSExp?.eq_2 n ds hns, Option.map_eq_some_iff] at h
    obtain ⟨ds', hds, rfl⟩ := h
    simp [Directive.toSExp, lst, ← ih ds' hds]
  · intro x h1 h2 d h
    rw [Directive.ofSExp?.eq_3 x h1 h2] at h
    exact Directive.ofElems_bind_inv h
  · exact fun ds h => Directive.dirsOf?_nil_inv h
  · exact fun x r ih1 ih2 ds h => Directive.dirsOf?_cons_inv ih1 ih2 h
  · intro a ds h
    simp [Directive.dirsOf?] at h

/-! ## Directives: what is printed is read back -/

theorem ModKind.kw_ne_thread (k : ModKind) : k.kw ≠ "thread" :=
  ModKind.kw_ne k _ (by decide) (by decide)

mutual
  theorem Directive.ofSExp?_toSExp : ∀ d : Directive, d.WF → Directive.ofSExp? d.toSExp = some d
    | .module m, hw => by
      obtain ⟨k, hk, hr⟩ := Directive.ofKw?_module (m := m) hw
      have he : (Directive.module m).toSExp = lst (sym k.kw :: m.toSExps.tail) := by
        show lst m.toSExps = _
        rw [← hk]
      rw [he, Directive.ofSExp?_lst (ModKind.kw_ne_thread k), hr]
    | .moduleDefinition k id b, hw => by
      have ht := takeId_idOpt id b.toSExps (fun h => by subst h; exact Body.noIdHead hw)
      show Directive.ofSExp? (lst (sym k.kw :: sym "definition" :: (idOpt id ++ b.toSExps))) = _
      rw [Directive.ofSExp?_lst (ModKind.kw_ne_thread k), Directive.ofKw?_kw]
      simp [moduleForm?, ht, Body.ofSExps?_toSExps hw]
    | .moduleInstance k i m, hw => by
      show Directive.ofSExp? (lst (sym k.kw :: sym "instance" :: (idOpt i ++ idOpt m))) = _
      rw [Directive.ofSExp?_lst (ModKind.kw_ne_thread k), Directive.ofKw?_kw]
      cases i with
      | none =>
        have hm : m = none := hw rfl
        subst hm
        simp [moduleForm?, idOpt]
      | some i => cases m <;> simp [moduleForm?, idOpt]
    | .assertMalformed m s, hw => by
      show Directive.ofSExp? (lst [sym "assert_malformed", m.toSExp, strA s]) = _
      rw [Directive.ofSExp?_lst (by decide)]
      simp only [Directive.ofKw?]
      exact modAssert?_print _ _ hw (by simp) s
    | .assertMalformedCustom m s, hw => by
      show Directive.ofSExp? (lst [sym "assert_malformed_custom", m.toSExp, strA s]) = _
      rw [Directive.ofSExp?_lst (by decide)]
      simp only [Directive.ofKw?]
      exact modAssert?_print _ _ hw (by simp) s
    | .assertInvalid m s, hw => by
      show Directive.ofSExp? (lst [sym "assert_invalid", m.toSExp, strA s]) = _
      rw [Directive.ofSExp?_lst (by decide)]
      simp only [Directive.ofKw?]
      exact modAssert?_print _ _ hw (by simp) s
    | .assertInvalidCustom m s, hw => by
      show Directive.ofSExp? (lst [sym "assert_invalid_custom", m.toSExp, strA s]) = _
      rw [Directive.ofSExp?_lst (by decide)]
      simp only [Directive.ofKw?]
      exact modAssert?_print _ _ hw (by simp) s
    | .assertUnlinkable m s, hw => by
      show Directive.ofSExp? (lst [sym "assert_unlinkable", m.toSExp, strA s]) = _
      rw [Directive.ofSExp?_lst (by decide)]
      simp only [Directive.ofKw?]
      exact modAssert?_print _ _ hw.1 (fun _ => hw.2) s
    | .register n m, _ => by
      show Directive.ofSExp? (lst (sym "register" :: strA n :: idOpt m)) = _
      rw [Directive.ofSExp?_lst (by decide)]
      simp only [Directive.ofKw?]
      cases m <;> rfl
    | .invoke i, hw => by
      have hi : Invoke.ofSExps? i.toSExps = some i := Invoke.ofSExps?_toSExps hw
      show Directive.ofSExp? (lst (sym "invoke" :: (idOpt i.module ++ strA i.name ::
        Val.listToSExps i.args))) = _
      rw [Directive.ofSExp?_lst (by decide)]
      simp only [Directive.ofKw?]
      simp only [Invoke.toSExps] at hi
      simp [hi]
    | .assertTrap e s, hw => by
      show Directive.ofSExp? (lst [sym "assert_trap", e.toSExp, strA s]) = _
      rw [Directive.ofSExp?_lst (by decide)]
      simp only [Directive.ofKw?]
      exact execAssert?_print _ hw s
    | .assertReturn e rs, hw => by
      show Directive.ofSExp? (lst (sym "assert_return" :: e.toSExp :: Val.listToSExps rs)) = _
      rw [Directive.ofSExp?_lst (by decide)]
      simp only [Directive.ofKw?]
      simp [assertReturnOf?, Exec.ofSExp?_toSExp hw.1, Val.listOf?_listToSExps _ hw.2]
    | .assertExhaustion i s, hw => by
      show Directive.ofSExp? (lst [sym "assert_exhaustion", lst i.toSExps, strA s]) = _
      rw [Directive.ofSExp?_lst (by decide)]
      simp only [Directive.ofKw?]
      simp [assertExhaustionOf?, Invoke.ofSExps?_toSExps hw]
    | .assertException e, hw => by
      show Directive.ofSExp? (lst [sym "assert_exception", e.toSExp]) = _
      rw [Directive.ofSExp?_lst (by decide)]
      simp only [Directive.ofKw?]
      simp [Exec.ofSExp?_toSExp hw]
    | .assertSuspension e s, hw => by
      show Directive.ofSExp? (lst [sym "assert_suspension", e.toSExp, strA s]) = _
      rw [Directive.ofSExp?_lst (by decide)]
      simp only [Directive.ofKw?]
      exact execAssert?_print _ hw s
    | .wait n, _ => by
      show Directive.ofSExp? (lst [sym "wait", ident n]) = _
      rw [Directive.ofSExp?_lst (by decide)]
      rfl
    | .thread n (some m) ds, hw => by
      have hds := Directive.dirsOf?_lst ds hw
      show Directive.ofSExp? (.cons (sym "thread") (.cons (ident n)
        (.cons (lst [sym "shared", lst [sym "module", ident m]])
          (lst (Directive.listToSExps ds))))) = _
      rw [show lst [sym "shared", lst [sym "module", ident m]] =
        .cons (sym "shared") (.cons (.cons (sym "module") (.cons (ident m) .nil)) .nil) from rfl]
      rw [Directive.ofSExp?.eq_1, hds]
      rfl
    | .thread n none ds, hw => by
      have hds := Directive.dirsOf?_lst ds hw
      show Directive.ofSExp? (.cons (sym "thread") (.cons (ident n)
        (lst (Directive.listToSExps ds)))) = _
      rw [Directive.ofSExp?.eq_2 n _ ?_, hds]
      · rfl
      · intro m ds' heq
        cases ds with
        | nil => simp [Directive.listToSExps, lst] at heq
        | cons d ds =>
          obtain ⟨r, hr⟩ := Directive.toSExp_head d
          simp only [Directive.listToSExps, lst_cons, hr, SExp2.cons.injEq, SExp2.atom.injEq,
            Atom.sym.injEq] at heq
          exact Directive.kw_ne_shared d heq.1.1

  theorem Directive.dirsOf?_lst : ∀ ds : List Directive, Directive.listWF ds →
      Directive.dirsOf? (lst (Directive.listToSExps ds)) = some ds
    | [], _ => rfl
    | d :: ds, hw => by
      have h1 := Directive.ofSExp?_toSExp d hw.1
      have h2 := Directive.dirsOf?_lst ds hw.2
      simp [Directive.listToSExps, lst_cons, Directive.dirsOf?, h1, h2]
end

/-! ## Scripts -/

theorem Directive.listOf?_listToSExps : ∀ ds : List Directive, Directive.listWF ds →
    Directive.listOf? (Directive.listToSExps ds) = some ds
  | [], _ => rfl
  | d :: ds, hw => by
    simp [Directive.listToSExps, Directive.listOf?, Directive.ofSExp?_toSExp d hw.1,
      Directive.listOf?_listToSExps ds hw.2]

theorem Directive.listToSExps_of_listOf? : ∀ (xs : List SExp) (ds : List Directive),
    Directive.listOf? xs = some ds → Directive.listToSExps ds = xs
  | [], ds, h => by simp only [Directive.listOf?, Option.some.injEq] at h; subst h; rfl
  | x :: xs, ds, h => by
    simp only [Directive.listOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨d, hd, ds', hds, rfl⟩ := h
    simp [Directive.listToSExps, Directive.toSExp_of_ofSExp? x d hd,
      Directive.listToSExps_of_listOf? xs ds' hds]

theorem Directive.directiveStart_toSExp (d : Directive) (h1 : d.kw ≠ "thread")
    (h2 : d.kw ≠ "wait") : directiveStart d.toSExp = true := by
  obtain ⟨r, hr⟩ := Directive.toSExp_head d
  rw [hr]
  match d with
  | .module (.wat k ..) | .module (.quote k ..) | .moduleDefinition k .. | .moduleInstance k .. =>
    cases k <;> simp only [Directive.kw, ModKind.kw, directiveStart] <;> rfl
  | .assertMalformed .. | .assertMalformedCustom .. | .assertInvalid .. | .assertInvalidCustom ..
  | .assertUnlinkable .. | .register .. | .invoke .. | .assertTrap .. | .assertReturn ..
  | .assertExhaustion .. | .assertException .. | .assertSuspension .. =>
    simp only [Directive.kw, directiveStart]; rfl
  | .thread .. => exact absurd rfl h1
  | .wait .. => exact absurd rfl h2

theorem Script.ofSExps?_toSExps {s : Script} (hs : s.WF) : Script.ofSExps? s.toSExps = some s := by
  match s, hs with
  | .directives (d :: ds), ⟨h1, h2, hw⟩ =>
    have hstart := Directive.directiveStart_toSExp d h1 h2
    have hl := Directive.listOf?_listToSExps (d :: ds) hw
    simp only [Script.toSExps, Directive.listToSExps] at hl ⊢
    simp [Script.ofSExps?, hstart, hl]
  | .inline [], _ => rfl
  | .inline (x :: xs), hx =>
    have hx' : directiveStart x = false := hx
    simp [Script.ofSExps?, Script.toSExps, hx']

theorem Script.toSExps_of_ofSExps? {xs : List SExp} {s : Script}
    (h : Script.ofSExps? xs = some s) : s.toSExps = xs := by
  unfold Script.ofSExps? at h
  split at h
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨ds, hds, rfl⟩ := h
      exact Directive.listToSExps_of_listOf? _ _ hds
    · simp only [Option.some.injEq] at h; subst h; rfl
  · simp only [Option.some.injEq] at h; subst h; rfl

end Silmaril.Wasm.Tools.Wast
