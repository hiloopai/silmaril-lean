module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Fragment
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Scripts

/-!
# The binary and text fragments of a script are closed

`binaryAxioms env` keeps the productions of the grammars named `B…`, and `textAxioms env` keeps
those named `T…`. This module proves that both fragments are closed in all nine imported
scripts. A `B` grammar mentions only `B` grammars, and likewise for `T`. The fragment therefore
has the whole script's least model on its nonterminals (`binary_leastModel_eq`,
`text_leastModel_eq`). The whole script is a conservative extension of each fragment
(`entails_binary_iff`, `entails_text_iff`).

**The nonterminals.** A SpecTec nonterminal is a grammar name with its unevaluated arguments,
and an argument can itself be a grammar (`Blist(Bbyte)`). The closed set is
`NTOver q`: the name satisfies `q` and so does every grammar named inside a grammar argument.
The predicate `q` is the name prefix (`isB`, `isT`).

**The proof.** The syntactic check `symOK q` says every grammar named in an IL symbol satisfies
`q`. It is preserved by the substitution of grammar arguments (`symOK_substSym`). It implies that
the translated symbol mentions only nonterminals in `NTOver q` (`symIn_transSym`). So a script
whose `q` grammars pass the check has a closed `q` fragment (`closedUnder_ntOver`). The check
itself, `checkGrams`, is a boolean function of the script's grammar map. It is evaluated by the
kernel (`decide +kernel`) at each of the nine scripts. That is a kernel reduction, without native code.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.Logic.Institution
open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts

/-! ## The syntactic check -/

mutual

/-- Every grammar named in the IL symbol satisfies `q`, including inside grammar arguments. -/
def symOK (q : IL.Id → Bool) : IL.Sym → Bool
  | .varG x args => q x && argsOK q args
  | .numG _ => true
  | .textG _ => true
  | .epsG => true
  | .seqG gs => symsOK q gs
  | .altG gs => symsOK q gs
  | .rangeG g₁ g₂ => symOK q g₁ && symOK q g₂
  | .iterG g _ => symOK q g
  | .attrG _ g => symOK q g

/-- `symOK` on lists of symbols. -/
def symsOK (q : IL.Id → Bool) : List IL.Sym → Bool
  | [] => true
  | g :: gs => symOK q g && symsOK q gs

/-- `symOK` on the grammar arguments of an argument list. -/
def argsOK (q : IL.Id → Bool) : List IL.Arg → Bool
  | [] => true
  | .gramA g :: rest => symOK q g && argsOK q rest
  | .expA _ :: rest => argsOK q rest
  | .typA _ :: rest => argsOK q rest
  | .defA _ :: rest => argsOK q rest

end

/-- The body of a production passes the check. -/
def prodOK (q : IL.Id → Bool) : IL.Prod → Bool
  | .prodD _ g _ _ => symOK q g

/-- Every grammar of the map whose name satisfies `q` has productions that pass the check. -/
def checkGrams (q : IL.Id → Bool) (m : Map GramDef) : Bool :=
  m.all fun xd => !q xd.1 || xd.2.2.2.all (prodOK q)

/-- The nonterminals over `q`: the name and every grammar inside a grammar argument satisfy `q`. -/
def NTOver (q : IL.Id → Bool) (n : NT) : Prop := q n.1 = true ∧ argsOK q n.2 = true

/-- Grammar names of the binary format. -/
def isB (x : IL.Id) : Bool := x.front == 'B'

/-- Grammar names of the text format. -/
def isT (x : IL.Id) : Bool := x.front == 'T'

theorem and_true_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true :=
  Bool.and_eq_true_iff.mp h

/-! ## The check transfers to translated symbols -/

theorem symIn_rangeSym (R : NT → Prop) (g₁ g₂ : IL.Sym) : SymIn R (rangeSym g₁ g₂) := by
  unfold rangeSym
  split
  · split <;> trivial
  · trivial

theorem symIn_byteSym (R : NT → Prop) (n : Nat) : SymIn R (byteSym n) := by
  unfold byteSym
  split <;> trivial

mutual

/-- A checked symbol translates to a symbol over `NTOver q`. -/
theorem symIn_transSym (env : Env) (q : IL.Id → Bool) :
    ∀ s : IL.Sym, symOK q s = true → SymIn (NTOver q) (transSym env s)
  | .varG _ _, h => and_true_split h
  | .numG n, _ => symIn_byteSym _ n
  | .textG _, _ => trivial
  | .epsG, _ => trivial
  | .seqG gs, h => symsIn_transSyms env q gs h
  | .altG gs, h => symsIn_transSyms env q gs h
  | .rangeG g₁ g₂, _ => symIn_rangeSym _ g₁ g₂
  | .iterG g (.mk _ _), h => symIn_transSym env q g h
  | .attrG _ g, h => symIn_transSym env q g h

/-- `symIn_transSym` on lists. -/
theorem symsIn_transSyms (env : Env) (q : IL.Id → Bool) :
    ∀ gs : List IL.Sym, symsOK q gs = true → SymsIn (NTOver q) (transSyms env gs)
  | [], _ => trivial
  | g :: gs, h =>
    ⟨symIn_transSym env q g (and_true_split h).1, symsIn_transSyms env q gs (and_true_split h).2⟩

end

/-! ## The check survives the substitution of grammar arguments -/

/-- Every grammar a substitution binds passes the check. -/
def SubstOK (q : IL.Id → Bool) (σ : List (IL.Id × IL.Sym)) : Prop :=
  ∀ p ∈ σ, symOK q p.2 = true

theorem lookup_ok {q : IL.Id → Bool} {σ : List (IL.Id × IL.Sym)} (hσ : SubstOK q σ)
    {x : IL.Id} {g : IL.Sym} (h : List.lookup x σ = some g) : symOK q g = true := by
  induction σ with
  | nil => cases h
  | cons p σ ih =>
    obtain ⟨k, g'⟩ := p
    have hrest : SubstOK q σ := fun p hp => hσ p (List.mem_cons_of_mem _ hp)
    by_cases hk : (x == k) = true
    · have hg : g' = g := by simpa [List.lookup, hk] using h
      exact hg ▸ hσ (k, g') List.mem_cons_self
    · have h' : List.lookup x σ = some g := by simpa [List.lookup, hk] using h
      exact ih hrest h'

theorem substGramId_ok {q : IL.Id → Bool} {σ : List (IL.Id × IL.Sym)} (hσ : SubstOK q σ)
    {x : IL.Id} (hx : q x = true) : q (substGramId σ x) = true := by
  unfold substGramId
  split
  · next x' h => exact (and_true_split (lookup_ok hσ h)).1
  · exact hx

theorem argsOK_tail {q : IL.Id → Bool} {a : IL.Arg} {rest : List IL.Arg}
    (h : argsOK q (a :: rest) = true) : argsOK q rest = true := by
  cases a with
  | gramA g => exact (and_true_split h).2
  | expA _ => exact h
  | typA _ => exact h
  | defA _ => exact h

mutual

/-- Substituting checked grammars into a checked symbol gives a checked symbol. -/
theorem symOK_substSym {q : IL.Id → Bool} {σ : List (IL.Id × IL.Sym)} (hσ : SubstOK q σ) :
    ∀ s : IL.Sym, symOK q s = true → symOK q (substSym σ s) = true
  | .varG x [], h => by
    cases hl : List.lookup x σ with
    | none => simpa [substSym, hl] using h
    | some g => simpa [substSym, hl] using lookup_ok hσ hl
  | .varG x (a :: rest), h => by
    have hx : q x = true := (and_true_split h).1
    have has : argsOK q (a :: rest) = true := (and_true_split h).2
    show (q (substGramId σ x) && argsOK q (substArgs σ (a :: rest))) = true
    rw [substGramId_ok hσ hx, argsOK_substArgs hσ (a :: rest) has]
    rfl
  | .numG _, h => h
  | .textG _, h => h
  | .epsG, h => h
  | .seqG gs, h => symsOK_substSyms hσ gs h
  | .altG gs, h => symsOK_substSyms hσ gs h
  | .rangeG g₁ g₂, h => by
    show (symOK q (substSym σ g₁) && symOK q (substSym σ g₂)) = true
    rw [symOK_substSym hσ g₁ (and_true_split h).1, symOK_substSym hσ g₂ (and_true_split h).2]
    rfl
  | .iterG g _, h => symOK_substSym hσ g h
  | .attrG _ g, h => symOK_substSym hσ g h

/-- `symOK_substSym` on lists. -/
theorem symsOK_substSyms {q : IL.Id → Bool} {σ : List (IL.Id × IL.Sym)} (hσ : SubstOK q σ) :
    ∀ gs : List IL.Sym, symsOK q gs = true → symsOK q (substSyms σ gs) = true
  | [], _ => rfl
  | g :: gs, h => by
    show (symOK q (substSym σ g) && symsOK q (substSyms σ gs)) = true
    rw [symOK_substSym hσ g (and_true_split h).1, symsOK_substSyms hσ gs (and_true_split h).2]
    rfl

/-- `symOK_substSym` on argument lists. -/
theorem argsOK_substArgs {q : IL.Id → Bool} {σ : List (IL.Id × IL.Sym)} (hσ : SubstOK q σ) :
    ∀ rest : List IL.Arg, argsOK q rest = true → argsOK q (substArgs σ rest) = true
  | [], _ => rfl
  | .gramA g :: rest, h => by
    show (symOK q (substSym σ g) && argsOK q (substArgs σ rest)) = true
    rw [symOK_substSym hσ g (and_true_split h).1, argsOK_substArgs hσ rest (and_true_split h).2]
    rfl
  | .expA _ :: rest, h => argsOK_substArgs hσ rest h
  | .typA _ :: rest, h => argsOK_substArgs hσ rest h
  | .defA _ :: rest, h => argsOK_substArgs hσ rest h

end

/-- The grammar arguments of a checked argument list form a checked substitution. -/
theorem substOK_gramArgSubst {q : IL.Id → Bool} :
    ∀ (ps : List IL.Param) (args : List IL.Arg), argsOK q args = true →
      SubstOK q (gramArgSubst ps args)
  | [], _, _ => by
    intro p hp
    simp [gramArgSubst] at hp
  | _ :: _, [], _ => by
    intro p hp
    simp [gramArgSubst] at hp
  | .gramP x _ _ :: ps, .gramA g :: rest, h => by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (and_true_split h).1
    · exact substOK_gramArgSubst ps rest (and_true_split h).2 p hp
  | .gramP _ _ _ :: ps, .expA _ :: rest, h => substOK_gramArgSubst ps rest h
  | .gramP _ _ _ :: ps, .typA _ :: rest, h => substOK_gramArgSubst ps rest h
  | .gramP _ _ _ :: ps, .defA _ :: rest, h => substOK_gramArgSubst ps rest h
  | .expP _ _ :: ps, a :: rest, h => substOK_gramArgSubst ps rest (argsOK_tail h)
  | .typP _ :: ps, a :: rest, h => substOK_gramArgSubst ps rest (argsOK_tail h)
  | .defP _ _ _ :: ps, a :: rest, h => substOK_gramArgSubst ps rest (argsOK_tail h)

/-! ## Closedness -/

theorem checkGrams_cons {q : IL.Id → Bool} {y : IL.Id} {e : GramDef} {m : Map GramDef}
    (hc : checkGrams q ((y, e) :: m) = true) :
    (!q y || e.2.2.all (prodOK q)) = true ∧ checkGrams q m = true :=
  Bool.and_eq_true_iff.mp hc

theorem checkGrams_spec {q : IL.Id → Bool} {m : Map GramDef} (hc : checkGrams q m = true)
    {x : IL.Id} {d : GramDef} (hd : Map.find? m x = some d) (hx : q x = true) :
    ∀ p ∈ d.2.2, prodOK q p = true := by
  induction m with
  | nil => cases hd
  | cons yd m ih =>
    obtain ⟨y, e⟩ := yd
    have hall := checkGrams_cons hc
    by_cases hy : y = x
    · have hde : e = d := by simpa [Map.find?, hy] using hd
      have hq : q y = true := hy ▸ hx
      have hall' : e.2.2.all (prodOK q) = true := by simpa [hq] using hall.1
      exact hde ▸ fun p hp => List.all_eq_true.mp hall' p hp
    · have hd' : Map.find? m x = some d := by simpa [Map.find?, hy] using hd
      exact ih hall.2 hd'

/-- **A script whose `q` grammars pass the check has a closed `q` fragment.** -/
theorem closedUnder_ntOver {q : IL.Id → Bool} {E env : Env} (hc : checkGrams q env.grams = true) :
    ClosedUnder (NTOver q) (prodsOf E env) := by
  intro n hn g hg
  unfold prodsOf at hg
  cases hfind : env.findGram? n.1 with
  | none => simp [hfind] at hg
  | some d =>
    obtain ⟨ps, t, prods⟩ := d
    rw [hfind] at hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    obtain ⟨qs, body, e, prems⟩ := p
    have hbody : symOK q body = true := checkGrams_spec hc hfind hn.1 _ hp
    have hσ : SubstOK q (gramArgSubst ps n.2) := substOK_gramArgSubst ps n.2 hn.2
    exact symIn_transSym E q _ (symOK_substSym hσ body hbody)

/-! ## The binary and text fragments -/

theorem ntOver_isB {n : NT} (h : NTOver isB n) : n.1.front = 'B' := beq_iff_eq.mp h.1

theorem ntOver_isT {n : NT} (h : NTOver isT n) : n.1.front = 'T' := beq_iff_eq.mp h.1

/-- **The binary fragment has the script's least model** on the binary nonterminals. -/
theorem binary_leastModel_eq {env : Env} (hc : checkGrams isB env.grams = true) {n : NT}
    (hn : NTOver isB n) :
    (leastModel ⟨actAlg, restrictProds (fun n => n.1.front = 'B')
      (prodsOf env env)⟩).rel n = (leastModel (gramOf env)).rel n :=
  leastModel_restrict_eq actAlg (closedUnder_ntOver hc) (fun _ => ntOver_isB) hn

/-- **The text fragment has the script's least model** on the text nonterminals. -/
theorem text_leastModel_eq {env : Env} (hc : checkGrams isT env.grams = true) {n : NT}
    (hn : NTOver isT n) :
    (leastModel ⟨actAlg, restrictProds (fun n => n.1.front = 'T')
      (prodsOf env env)⟩).rel n = (leastModel (gramOf env)).rel n :=
  leastModel_restrict_eq actAlg (closedUnder_ntOver hc) (fun _ => ntOver_isT) hn

/-- **The script is conservative over its binary fragment**: about a binary nonterminal, the
binary fragment and the whole script have the same consequences. -/
theorem entails_binary_iff {env : Env} (hc : checkGrams isB env.grams = true) {x : IL.Id}
    {args : List IL.Arg} (hn : NTOver isB (x, args)) (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    Entails (binaryAxioms env) (derivesNT x args ρ bs v) ↔
      Entails (scriptAxioms env) (derivesNT x args ρ bs v) :=
  entails_fragment_iff actAlg (closedUnder_ntOver hc) (fun _ => ntOver_isB) (g := .nt (x, args)) hn bs _

/-- **The script is conservative over its text fragment.** -/
theorem entails_text_iff {env : Env} (hc : checkGrams isT env.grams = true) {x : IL.Id}
    {args : List IL.Arg} (hn : NTOver isT (x, args)) (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    Entails (textAxioms env) (derivesNT x args ρ bs v) ↔
      Entails (scriptAxioms env) (derivesNT x args ρ bs v) :=
  entails_fragment_iff actAlg (closedUnder_ntOver hc) (fun _ => ntOver_isT) (g := .nt (x, args)) hn bs _

/-! ## The nine scripts pass the check -/

section Nine

set_option maxRecDepth 100000

theorem checkB_wasm10_original : checkGrams isB Wasm10.envOriginal.grams = true := by
  decide +kernel
theorem checkB_wasm10_fixed : checkGrams isB Wasm10.envFixed.grams = true := by decide +kernel
theorem checkB_main10 : checkGrams isB Versions.Main.Wasm10.env.grams = true := by
  decide +kernel
theorem checkB_wasm20_original : checkGrams isB Wasm20.envOriginal.grams = true := by
  decide +kernel
theorem checkB_wasm20_fixed : checkGrams isB Wasm20.envFixed.grams = true := by decide +kernel
theorem checkB_main20 : checkGrams isB Versions.Main.Wasm20.env.grams = true := by
  decide +kernel
theorem checkB_wasm30_original : checkGrams isB Wasm30.envOriginal.grams = true := by
  decide +kernel
theorem checkB_wasm30_fixed : checkGrams isB Wasm30.envFixed.grams = true := by decide +kernel
theorem checkB_main30 : checkGrams isB Versions.Main.Wasm30.env.grams = true := by
  decide +kernel

theorem checkT_wasm10_original : checkGrams isT Wasm10.envOriginal.grams = true := by
  decide +kernel
theorem checkT_wasm10_fixed : checkGrams isT Wasm10.envFixed.grams = true := by decide +kernel
theorem checkT_main10 : checkGrams isT Versions.Main.Wasm10.env.grams = true := by
  decide +kernel
theorem checkT_wasm20_original : checkGrams isT Wasm20.envOriginal.grams = true := by
  decide +kernel
theorem checkT_wasm20_fixed : checkGrams isT Wasm20.envFixed.grams = true := by decide +kernel
theorem checkT_main20 : checkGrams isT Versions.Main.Wasm20.env.grams = true := by
  decide +kernel
theorem checkT_wasm30_original : checkGrams isT Wasm30.envOriginal.grams = true := by
  decide +kernel
theorem checkT_wasm30_fixed : checkGrams isT Wasm30.envFixed.grams = true := by decide +kernel
theorem checkT_main30 : checkGrams isT Versions.Main.Wasm30.env.grams = true := by
  decide +kernel

end Nine

set_option maxRecDepth 100000 in
/-- All nine scripts pass both checks. -/
theorem checks_nineEnvs :
    ∀ env, NineEnvs env → checkGrams isB env.grams = true ∧ checkGrams isT env.grams = true := by
  intro env h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨checkB_wasm10_original, checkT_wasm10_original⟩
  · exact ⟨checkB_wasm10_fixed, checkT_wasm10_fixed⟩
  · exact ⟨checkB_main10, checkT_main10⟩
  · exact ⟨checkB_wasm20_original, checkT_wasm20_original⟩
  · exact ⟨checkB_wasm20_fixed, checkT_wasm20_fixed⟩
  · exact ⟨checkB_main20, checkT_main20⟩
  · exact ⟨checkB_wasm30_original, checkT_wasm30_original⟩
  · exact ⟨checkB_wasm30_fixed, checkT_wasm30_fixed⟩
  · exact ⟨checkB_main30, checkT_main30⟩

/-- **In all nine grammar theories, the binary and text fragments are closed**, so each script is
a conservative extension of each fragment. -/
theorem nineEnvs_fragments_closed :
    ∀ env, NineEnvs env →
      ClosedUnder (NTOver isB) (prodsOf env env) ∧ ClosedUnder (NTOver isT) (prodsOf env env) :=
  fun env h => ⟨closedUnder_ntOver (checks_nineEnvs env h).1,
    closedUnder_ntOver (checks_nineEnvs env h).2⟩

end Silmaril.Wasm.SpecTec.GrammarInst
