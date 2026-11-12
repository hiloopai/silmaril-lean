module

public import Silmaril.Wasm.SpecTec.Surface.Parser.Defs

/-!
# Soundness of the SpecTec surface parser

Each parser function is sound for its grammar relation. The five mutually
recursive expression parsers are handled together: each is a step function
(`primStep`, `seqStep`, …) applied to the parsers at smaller fuel, so
`expSound` is an induction on fuel whose step is one lemma per step function.
The headline `parse?_sound` is in `Silmaril.Wasm.SpecTec.Surface.Parser.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Surface.Parser

open Silmaril.Wasm.SpecTec.Surface.Lexer (Token)
open Silmaril.Wasm.SpecTec.Surface.Syntax

theorem closeP_some {α β : Type} {f : α → β} {o : Option (α × List Token)} {b : β}
    {r : List Token} (h : closeP f o = some (b, r)) :
    ∃ a, o = some (a, .sym ")" :: r) ∧ b = f a := by
  unfold closeP at h
  split at h
  next a r0 => cases h; exact ⟨a, rfl, rfl⟩
  next => cases h

theorem pIters_sound {ts : List Token} :
    ∀ (r : List Token) (e : Exp) {e' : Exp} {r' : List Token},
      ExpPost ts e r → pIters e r = (e', r') → ExpPost ts e' r' := by
  intro r
  induction r with
  | nil => intro e e' r' hp h; cases h; exact hp
  | cons t r ih =>
    intro e e' r' hp h
    unfold pIters at h
    split at h
    next it hit => exact ih _ (.iter hp hit) h
    next => cases h; exact hp

/-- A parser is sound for a relation. -/
def Sound {α : Type} (p : PFun α) (R : List Token → α → List Token → Prop) : Prop :=
  ∀ {ts x r}, p ts = some (x, r) → R ts x r

theorem closeP_rel {α β : Type} {p : PFun α} {R : List Token → α → List Token → Prop}
    {f : α → β} {r r' : List Token} {b : β} (hp : Sound p R) (h : closeP f (p r) = some (b, r')) :
    ∃ a, R r a (.sym ")" :: r') ∧ b = f a := by
  obtain ⟨a, ha, hb⟩ := closeP_some h
  exact ⟨a, hp ha, hb⟩

theorem prim_app {args : PFun (List Exp)} {x : List Char} {r r' : List Token} {e : Exp}
    (hargs : Sound args Args) (h : closeP (.var x) (args r) = some (e, r')) :
    ExpPrim (.idParen x :: r) e r' := by
  obtain ⟨as, ha, rfl⟩ := closeP_rel (p := args) (R := Args) hargs h
  exact .app ha

theorem prim_call {args : PFun (List Exp)} {f : List Char} {r r' : List Token} {e : Exp}
    (hargs : Sound args Args) (h : closeP (.call f) (args r) = some (e, r')) :
    ExpPrim (.sym "$" :: .idParen f :: r) e r' := by
  obtain ⟨as, ha, rfl⟩ := closeP_rel (p := args) (R := Args) hargs h
  exact .call ha

theorem prim_arith {arith : PFun Exp} {r r' : List Token} {e : Exp}
    (harith : Sound arith Arith) (h : closeP id (arith r) = some (e, r')) :
    ExpPrim (.sym "$" :: .sym "(" :: r) e r' := by
  obtain ⟨e', ha, rfl⟩ := closeP_rel (p := arith) (R := Arith) harith h
  exact .arith ha

theorem prim_paren {exp : PFun Exp} {r r' : List Token} {e : Exp}
    (hexp : Sound exp ExpE) (h : closeP .paren (exp r) = some (e, r')) :
    ExpPrim (.sym "(" :: r) e r' := by
  obtain ⟨e', ha, rfl⟩ := closeP_rel (p := exp) (R := ExpE) hexp h
  exact .paren ha

theorem prim_kw {k : String} {r r' : List Token} {e : Exp}
    (h : (if k ∈ typKwNames then some (Exp.var k.toList [], r) else none) = some (e, r')) :
    ExpPrim (.sym k :: r) e r' := by
  split at h
  next hk => cases h; exact .typKw hk
  next => cases h

theorem primStep_sound {args : PFun (List Exp)} {arith exp : PFun Exp}
    (hargs : Sound args Args) (harith : Sound arith Arith) (hexp : Sound exp ExpE) :
    Sound (primStep args arith exp) ExpPrim := by
  intro ts e r h
  unfold primStep at h
  split at h
  next => cases h; exact .var
  next => exact prim_app hargs h
  next => cases h; exact .nat
  next => cases h; exact .call0
  next => exact prim_call hargs h
  next => exact prim_arith harith h
  next => cases h; exact .eps
  next => exact prim_paren hexp h
  next => exact prim_kw h
  next => cases h

theorem seqStep_sound {prim : PFun Exp} {seq : PFun (List Exp)}
    (hprim : Sound prim ExpPrim) (hseq : Sound seq ExpSeq) : Sound (seqStep prim seq) ExpSeq := by
  intro ts es r h
  unfold seqStep at h
  split at h
  next => cases h
  next e r0 hp =>
    rcases hi : pIters e r0 with ⟨e', r'⟩
    have hpost : ExpPost ts e' r' := pIters_sound r0 e (.prim (hprim hp)) hi
    simp only [hi] at h
    split at h
    next =>
      split at h
      next es' r'' hs => cases h; exact .cons hpost (hseq hs)
      next => cases h; exact .one hpost
    next => cases h; exact .one hpost

theorem expStep_sound {seq : PFun (List Exp)} (hseq : Sound seq ExpSeq) :
    Sound (expStep seq) ExpE := by
  intro ts e r h
  unfold expStep at h
  split at h
  next => cases h
  next es hs => cases h; exact .seq (hseq hs)
  next es t r0 hs =>
    split at h
    next op hop =>
      obtain ⟨⟨es', r'⟩, hs', he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact .cmp (hseq hs) hop (hseq hs')
    next => cases h; exact .seq (hseq hs)

theorem arithStep_sound {prim : PFun Exp} (hprim : Sound prim ExpPrim) :
    Sound (arithStep prim) Arith := by
  intro ts e r h
  unfold arithStep at h
  split at h
  next => cases h
  next e0 hp => cases h; exact .one (.exp (hprim hp))
  next e0 t r0 hp =>
    split at h
    next op _ hop =>
      obtain ⟨⟨e', r'⟩, hp', he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact .cmp (.exp (hprim hp)) hop (.exp (hprim hp'))
    next op _ hop =>
      obtain ⟨⟨e', r'⟩, hp', he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact .bin (.exp (hprim hp)) ‹_› (.exp (hprim hp'))
    next => cases h; exact .one (.exp (hprim hp))

theorem argsStep_sound {exp : PFun Exp} {args : PFun (List Exp)}
    (hexp : Sound exp ExpE) (hargs : Sound args Args) : Sound (argsStep exp args) Args := by
  intro ts es r h
  unfold argsStep at h
  split at h
  next => cases h; exact .nil
  next =>
    split at h
    next e r0 he =>
      obtain ⟨⟨es', r'⟩, ha, hes⟩ := Option.map_eq_some_iff.mp h
      cases hes
      exact .cons (hexp he) (hargs ha)
    next e r0 _ he => cases h; exact .one (hexp he)
    next => cases h

/-- The expression parsers are sound at fuel `n`. -/
structure ExpSound (n : Nat) : Prop where
  prim : Sound (pPrim n) ExpPrim
  seq : Sound (pSeq n) ExpSeq
  exp : Sound (pExp n) ExpE
  arith : Sound (pArith n) Arith
  args : Sound (pArgs n) Args

theorem expSound : ∀ n, ExpSound n := by
  intro n
  induction n with
  | zero =>
    exact ⟨(nomatch ·), (nomatch ·), (nomatch ·), (nomatch ·), (nomatch ·)⟩
  | succ n ih =>
    exact ⟨fun h => primStep_sound ih.args ih.arith ih.exp h,
      fun h => seqStep_sound ih.prim ih.seq h, fun h => expStep_sound ih.seq h,
      fun h => arithStep_sound ih.prim h, fun h => argsStep_sound ih.exp ih.args h⟩

theorem pTypIters_sound {ts : List Token} :
    ∀ (r : List Token) (ty : Typ) {ty' : Typ} {r' : List Token},
      TypP ts ty r → pTypIters ty r = (ty', r') → TypP ts ty' r' := by
  intro r
  induction r with
  | nil => intro ty ty' r' hp h; cases h; exact hp
  | cons t r ih =>
    intro ty ty' r' hp h
    unfold pTypIters at h
    split at h
    next it hit => exact ih _ (.iter hp hit) h
    next => cases h; exact hp

theorem pTyp_sound {n : Nat} : Sound (pTyp n) TypP := by
  intro ts ty r h
  unfold pTyp at h
  split at h
  next x r0 => exact pTypIters_sound r0 _ .var (Option.some.inj h)
  next x r0 =>
    obtain ⟨⟨ty0, r1⟩, hc, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨as, ha, rfl⟩ := closeP_some hc
    exact pTypIters_sound r1 _ (.app ((expSound n).args ha)) he
  next t r0 _ _ =>
    split at h
    next ty0 hk => exact pTypIters_sound r0 _ (.kw hk) (Option.some.inj h)
    next => cases h
  next => cases h

theorem pBalanced_sound (d : Nat) (ts : List Token) :
    ∀ {b r : List Token}, pBalanced d ts = some (b, r) → Balanced d ts b r := by
  fun_induction pBalanced d ts with
  | case1 r0 => intro b r h; cases h; exact .close
  | case2 d r0 ih =>
    intro b r h
    obtain ⟨⟨b', r'⟩, hb, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact .closeIn (ih hb)
  | case3 d t r0 _ _ ho ih =>
    intro b r h
    obtain ⟨⟨b', r'⟩, hb, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    have ho' : opens t = true ∧ t ≠ .sym "[" ∧ t ≠ .sym "{" := by simpa using ho
    exact .openP ho'.1 ho'.2.1 ho'.2.2 (ih hb)
  | case4 => intro b r h; cases h
  | case5 d t r0 _ _ ho hc ih =>
    intro b r h
    obtain ⟨⟨b', r'⟩, hb, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    have hc' : (t ≠ .sym "[" ∧ t ≠ .sym "{") ∧ closes t = false := by simpa using hc
    have ho' : opens t = false := by simpa [hc'.1.1, hc'.1.2] using ho
    exact .other ho' hc'.2 (ih hb)
  | case6 => intro b r h; cases h

theorem pHints_sound (n : Nat) (ts : List Token) :
    ∀ {hs : List Hint} {r : List Token}, pHints n ts = (hs, r) → Hints ts hs r := by
  fun_induction pHints n ts with
  | case1 n x r0 b r' hb hs' r'' hh ih =>
    intro hs r h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .cons (pBalanced_sound 0 r0 hb) (ih hh)
  | case2 => intro hs r h; cases h; exact .nil
  | case3 => intro hs r h; cases h; exact .nil

theorem pPrems_sound (n : Nat) (ts : List Token) :
    ∀ {ps : List Prem} {r : List Token}, pPrems n ts = some (ps, r) → Prems ts ps r := by
  fun_induction pPrems n ts with
  | case1 n r0 ih =>
    intro ps r h
    obtain ⟨⟨ps', r'⟩, hp, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact .otherwise (ih hp)
  | case2 n r0 e r' he ih =>
    intro ps r h
    obtain ⟨⟨ps', r''⟩, hp, hq⟩ := Option.map_eq_some_iff.mp h
    cases hq
    exact .ifP ((expSound n).exp he) (ih hp)
  | case3 => intro ps r h; cases h
  | case4 => intro ps r h; cases h; exact .nil

theorem allNl_sound {ts : List Token} (h : allNl ts = true) : AllNl ts := by
  intro t ht
  simpa using List.all_eq_true.mp h t ht

theorem pSigRest_spec {n : Nat} {x : List Char} {as : List Exp} {r0 : List Token} {d : Def}
    (h : pSigRest n x as r0 = some d) :
    ∃ t r' hs r'', TypP r0 t r' ∧ Hints r' hs r'' ∧ AllNl r'' ∧ d = .decSig x as t hs := by
  unfold pSigRest at h
  split at h
  next t r' ht =>
    rcases hh : pHints n r' with ⟨hs, r''⟩
    simp only [hh] at h
    split at h
    next hn => cases h; exact ⟨t, r', hs, r'', pTyp_sound ht, pHints_sound n r' hh, allNl_sound hn, rfl⟩
    next => cases h
  next => cases h

theorem pClauseRest_spec {n : Nat} {x : List Char} {as : List Exp} {r0 : List Token} {d : Def}
    (h : pClauseRest n x as r0 = some d) :
    ∃ e r' ps r'', ExpE r0 e r' ∧ Prems r' ps r'' ∧ AllNl r'' ∧ d = .decClause x as e ps := by
  unfold pClauseRest at h
  split at h
  next e r' he =>
    split at h
    next ps r'' hp =>
      split at h
      next hn => cases h; exact ⟨e, r', ps, r'', (expSound n).exp he, pPrems_sound n r' hp, allNl_sound hn, rfl⟩
      next => cases h
    next => cases h
  next => cases h

theorem decSig_of {n : Nat} {x : List Char} {as : List Exp} {r r0 : List Token} {d : Def}
    (ha : Args r as (.sym ")" :: .sym ":" :: r0)) (h : pSigRest n x as r0 = some d) :
    DefP (.sym "def" :: .sym "$" :: .idParen x :: r) d := by
  obtain ⟨t, r1, hs, r2, ht, hh, hn, rfl⟩ := pSigRest_spec h
  exact .decSig ha ht hh hn

theorem decSig0_of {n : Nat} {x : List Char} {r0 : List Token} {d : Def}
    (h : pSigRest n x [] r0 = some d) : DefP (.sym "def" :: .sym "$" :: .id x :: .sym ":" :: r0) d := by
  obtain ⟨t, r1, hs, r2, ht, hh, hn, rfl⟩ := pSigRest_spec h
  exact .decSig0 ht hh hn

theorem decClause_of {n : Nat} {x : List Char} {as : List Exp} {r r0 : List Token} {d : Def}
    (ha : Args r as (.sym ")" :: .sym "=" :: r0)) (h : pClauseRest n x as r0 = some d) :
    DefP (.sym "def" :: .sym "$" :: .idParen x :: r) d := by
  obtain ⟨e, r1, ps, r2, he, hp, hn, rfl⟩ := pClauseRest_spec h
  exact .decClause ha he hp hn

theorem decClause0_of {n : Nat} {x : List Char} {r0 : List Token} {d : Def}
    (h : pClauseRest n x [] r0 = some d) :
    DefP (.sym "def" :: .sym "$" :: .id x :: .sym "=" :: r0) d := by
  obtain ⟨e, r1, ps, r2, he, hp, hn, rfl⟩ := pClauseRest_spec h
  exact .decClause0 he hp hn

theorem pGramRest_sound {n : Nat} {x : List Char} {r0 : List Token} {d : Def}
    (h : pGramRest n x r0 = some d) : GramAliasP (.sym "grammar" :: .id x :: .sym ":" :: r0) d := by
  unfold pGramRest at h
  split at h
  next t r1 ht =>
    split at h
    next hs g r2 hh =>
      split at h
      next as r3 ha =>
        split at h
        next hn =>
          cases h
          exact .mk (pTyp_sound ht) (pHints_sound n r1 hh) ((expSound n).args ha) (allNl_sound hn)
        next => cases h
      next => cases h
    next => cases h
  next => cases h

theorem pDef_sound {n : Nat} {sp : List Token} {d : Def} (h : pDef n sp = some d) : DeclP sp d := by
  revert h
  fun_cases pDef n sp with
  | case1 x r hs r' hh t r'' ht hn =>
    intro h
    cases h
    exact .defP (.syntaxAlias (pHints_sound n r hh) (pTyp_sound ht) (allNl_sound hn))
  | case5 x r as r' ha => exact fun h => .defP (decSig_of ((expSound n).args ha) h)
  | case6 x r as r' ha => exact fun h => .defP (decClause_of ((expSound n).args ha) h)
  | case8 x r' => exact fun h => .defP (decSig0_of h)
  | case9 x r' => exact fun h => .defP (decClause0_of h)
  | case10 x r' => exact fun h => .gramAlias (pGramRest_sound h)
  | _ => intro h; cases h

theorem parseList_sound (n : Nat) (ts : List Token) :
    ∀ {ds : List Def}, parseList n ts = some ds → Parses ts ds := by
  fun_induction parseList n ts with
  | case1 => intro ds h; cases h; exact .nil
  | case3 n r ih => intro ds h; exact .nl (ih h)
  | case4 n r ih =>
    intro ds h
    obtain ⟨ds', hd, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact .sep (ih hd)
  | case6 n t ts _ _ sp r hs hne d hd ih =>
    intro ds h
    obtain ⟨ds', hp, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact .decl hs (pDef_sound hd) (ih hp)
  | case7 n t ts _ _ sp r hs hne hd ih =>
    intro ds h
    obtain ⟨ds', hp, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact .skip hs hne (ih hp)
  | _ => intro ds h; cases h

end Silmaril.Wasm.SpecTec.Surface.Parser
