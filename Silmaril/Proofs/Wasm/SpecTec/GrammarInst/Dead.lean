module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Separate

/-!
# Dead productions of the byte semantics

Three reasons a production of an elaborated SpecTec grammar has no derivation in the byte
semantics (`Sem.SymDerives`, whose least model is the grammar theory's `gramRelSup`), each
decided syntactically:

* **Arity.** `AttrG (e, g)` needs `g` to contribute exactly one value
  (`Sem.attrActFn`). `minVals g` is a lower bound on what `g` contributes
  (`minVals_le`): a `TextG` contributes one value per byte, a `VarG`, `AttrG` or `IterG`
  one, a `SeqG` the sum of its factors. A production `x:g` with `2 ≤ minVals g` is dead
  (`not_prodDerives_attr_of_arity`), and so is a grammar all of whose productions are
  (`deadByArity`, `not_symDerives_of_deadByArity`). This is the arity obstacle of
  `Equiv/TextBridge.lean`, as a decision procedure.
* **Scope.** A variable the body of a production never binds is unbound when the premises are
  checked. `symFrames z g` decides, for a fragment of symbols and binding patterns, that
  deriving `g` leaves the binding of `z` alone (`symDerives_frame`, from `matchExp_frame` for
  patterns). An `IfPr` premise or an iterated premise that must read `z` then fails
  (`not_evalExp_varE_none`, `not_premsHold_iterPr_of_unbound_dom`).

Nothing here depends on a particular script.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.BinaryModule (Rounds symDerives_iterG)

/-! ## Values contributed by a symbol -/

mutual

/-- A lower bound on the number of values a symbol contributes in the byte semantics. -/
def minVals : IL.Sym → Nat
  | .textG t => (Unicode.utf8 t).length
  | .varG _ _ => 1
  | .attrG _ _ => 1
  | .iterG _ _ => 1
  | .seqG gs => minValsL gs
  | _ => 0

/-- `minVals` summed over the factors of a sequence. -/
def minValsL : List IL.Sym → Nat
  | [] => 0
  | g :: gs => minVals g + minValsL gs

end

/-- `actAlg.ofBytes` contributes one value per byte and keeps the scope. -/
theorem ofBytes_apply_elim : ∀ {bs : Grammar.Bytes} {ρ ρ' : VarEnv} {l : List Value},
    actAlg.ofBytes bs ρ l ρ' → l.length = bs.length ∧ ρ' = ρ
  | [], _, _, _, h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  | b :: bs, _, _, _, h => by
      obtain ⟨l₁, ρ₁, l₂, ⟨rfl, rfl⟩, h₂, rfl⟩ := h
      obtain ⟨hl, rfl⟩ := ofBytes_apply_elim h₂
      exact ⟨by simp [hl], rfl⟩

/-- A literal text terminal contributes one value per byte and keeps the scope. -/
theorem symDerives_textG_elim {env : Env} {ρ ρ' : VarEnv} {t : Text} {bs : Grammar.Bytes}
    {l : List Value} (h : SymDerives env ρ (.textG t) bs l ρ') :
    bs = Unicode.utf8 t ∧ l.length = bs.length ∧ ρ' = ρ := by
  obtain ⟨a, ha, hv⟩ := h
  rw [symDen_textG] at ha
  obtain ⟨rfl, rfl⟩ := ha
  exact ⟨rfl, ofBytes_apply_elim hv⟩

/-- A nonterminal contributes one value and keeps the caller's scope. -/
theorem symDerives_varG_elim {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {args : List IL.Arg}
    {bs : Grammar.Bytes} {l : List Value} (h : SymDerives env ρ (.varG x args) bs l ρ') :
    l.length = 1 ∧ ρ' = ρ := by
  cases hg : env.findGram? x with
  | none =>
      obtain ⟨a, ha, -⟩ := h
      rw [symDen_varG_of_none env x args hg] at ha
      exact ha.elim
  | some r =>
      obtain ⟨ps, t, prods⟩ := r
      obtain ⟨rfl, p, -, hp⟩ := (symDerives_varG hg).mp h
      obtain ⟨q, g, e, prems⟩ := p
      obtain ⟨-, -, -, -, -, v, -, -, -, -, -, rfl⟩ := hp
      exact ⟨rfl, rfl⟩

mutual

/-- **`minVals` is a lower bound** on the values a derivation contributes. -/
theorem minVals_le {env : Env} :
    ∀ (g : IL.Sym) {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value},
      SymDerives env ρ g bs l ρ' → minVals g ≤ l.length
  | .textG t, _, _, _, _, h => by
      obtain ⟨rfl, hl, -⟩ := symDerives_textG_elim h
      simp [minVals, hl]
  | .varG _ _, _, _, _, _, h => by
      simp [minVals, (symDerives_varG_elim h).1]
  | .attrG _ _, _, _, _, _, h => by
      obtain ⟨v, ρ₁, -, rfl, -⟩ := symDerives_attrG.mp h
      simp [minVals]
  | .iterG _ (.mk _ _), _, _, _, _, h => by
      obtain ⟨rows, -, -, rfl, -⟩ := symDerives_iterG.mp h
      simp [minVals]
  | .seqG gs, _, _, _, _, h => by
      simpa [minVals] using minValsL_le gs h
  | .numG _, _, _, _, _, _ => by simp [minVals]
  | .epsG, _, _, _, _, _ => by simp [minVals]
  | .altG _, _, _, _, _, _ => by simp [minVals]
  | .rangeG _ _, _, _, _, _, _ => by simp [minVals]

/-- `minValsL` is a lower bound for a sequence. -/
theorem minValsL_le {env : Env} :
    ∀ (gs : List IL.Sym) {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value},
      SymDerives env ρ (.seqG gs) bs l ρ' → minValsL gs ≤ l.length
  | [], _, _, _, _, _ => by simp [minValsL]
  | g :: gs, _, _, _, _, h => by
      obtain ⟨b₁, l₁, ρ₁, b₂, l₂, h₁, h₂, -, rfl⟩ := symDerives_seqG_cons.mp h
      have k₁ := minVals_le g h₁
      have k₂ := minValsL_le gs h₂
      simp only [minValsL, List.length_append]
      omega

end

/-- An attribute over a symbol that contributes at least two values derives nothing. -/
theorem not_symDerives_attr_of_arity {env : Env} {ρ ρ' : VarEnv} {e : Exp} {g : IL.Sym}
    (hg : 2 ≤ minVals g) {bs : Grammar.Bytes} {l : List Value} :
    ¬ SymDerives env ρ (.attrG e g) bs l ρ' := by
  intro h
  obtain ⟨v, ρ₁, hd, -, -⟩ := symDerives_attrG.mp h
  have := minVals_le g hd
  simp at this
  omega

/-- `substSym` passes through an attribute. -/
theorem substSym_attrG (σ : List (IL.Id × IL.Sym)) (e : Exp) (g : IL.Sym) :
    substSym σ (.attrG e g) = .attrG e (substSym σ g) := rfl

/-- **Arity-dead productions.** A production `x:g` whose body `g`, after the grammar arguments
are substituted, contributes at least two values derives nothing. -/
theorem not_prodDerives_attr_of_arity {env : Env} {ρ : VarEnv} {ps : List Param}
    {args : List IL.Arg} {q : List Param} {e ev : Exp} {g : IL.Sym} {prems : List Prem}
    (hg : 2 ≤ minVals (substSym (gramArgSubst ps args) g)) {bs : Grammar.Bytes}
    {l : List Value} : ¬ ProdDerives env ρ ps args (.prodD q (.attrG e g) ev prems) bs l := by
  rintro ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, -, -, hs, -, -, -⟩
  rw [substSym_attrG] at hs
  exact not_symDerives_attr_of_arity hg hs

/-- A production is dead by arity (after the substitution `σ` of grammar arguments): it is
`x:g` with `2 ≤ minVals g`. -/
def deadByArity (σ : List (IL.Id × IL.Sym)) : IL.Prod → Bool
  | .prodD _ (.attrG _ g) _ _ => decide (2 ≤ minVals (substSym σ g))
  | _ => false

/-- **Arity-dead grammars.** A nonterminal all of whose productions are dead by arity derives
nothing, at any arguments that substitute no grammar. -/
theorem not_symDerives_of_deadByArity {env : Env} {x : IL.Id} {ps : List Param} {t : Typ}
    {prods : List IL.Prod} (hg : env.findGram? x = some (ps, t, prods))
    (hd : prods.all (deadByArity []) = true) {args : List IL.Arg}
    (hσ : gramArgSubst ps args = []) {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    ¬ SymDerives env ρ (.varG x args) bs l ρ' := by
  intro h
  obtain ⟨-, p, hp, hpd⟩ := (symDerives_varG hg).mp h
  have hdp := List.all_eq_true.mp hd p hp
  obtain ⟨q, g, ev, prems⟩ := p
  cases g with
  | attrG e g =>
      have h2 : 2 ≤ minVals (substSym (gramArgSubst ps args) g) := by
        rw [hσ]
        simpa [deadByArity] using hdp
      exact not_prodDerives_attr_of_arity h2 hpd
  | _ => simp [deadByArity] at hdp

/-! ## Sequences -/

/-- A three-factor sequence derives the concatenation of its factors. -/
theorem symDerives_seq3 {env : Env} {ρ ρ₁ ρ₂ ρ₃ : VarEnv} {g₁ g₂ g₃ : IL.Sym}
    {b₁ b₂ b₃ : Grammar.Bytes} {l₁ l₂ l₃ : List Value} (h₁ : SymDerives env ρ g₁ b₁ l₁ ρ₁)
    (h₂ : SymDerives env ρ₁ g₂ b₂ l₂ ρ₂) (h₃ : SymDerives env ρ₂ g₃ b₃ l₃ ρ₃) :
    SymDerives env ρ (.seqG [g₁, g₂, g₃]) (b₁ ++ b₂ ++ b₃) (l₁ ++ l₂ ++ l₃) ρ₃ := by
  have h₃' : SymDerives env ρ₂ (.seqG [g₃]) b₃ l₃ ρ₃ := symDerives_seqG_single h₃
  have h₂' : SymDerives env ρ₁ (.seqG [g₂, g₃]) (b₂ ++ b₃) (l₂ ++ l₃) ρ₃ :=
    symDerives_seqG_cons.mpr ⟨_, _, _, _, _, h₂, h₃', rfl, rfl⟩
  rw [List.append_assoc, List.append_assoc]
  exact symDerives_seqG_cons.mpr ⟨_, _, _, _, _, h₁, h₂', rfl, rfl⟩

/-! ## Scope frames -/

/-- Binding a different name leaves a lookup alone. -/
theorem findVal?_bindVal_ne {ρ : VarEnv} {y z : IL.Id} (h : y ≠ z) (v : Value) :
    (ρ.bindVal y v).findVal? z = ρ.findVal? z := by
  simp only [VarEnv.findVal?, VarEnv.bindVal, Map.bind]
  split
  · rfl
  · simp [Map.find?, h]

/-- Iteration domains whose sources are variables other than `z`. -/
def domsFrame (z : IL.Id) : List Dom → Bool
  | [] => true
  | .mk _ (.varE y) :: ds => y != z && domsFrame z ds
  | _ :: _ => false

mutual

/-- Binding patterns whose matching provably leaves the binding of `z` alone: a variable other
than `z`, a numeral, an injection or tuple of such patterns, and a list or option iteration
whose domains are variables other than `z`. -/
def patFrames (z : IL.Id) : Exp → Bool
  | .varE y => y != z
  | .numE _ => true
  | .caseE _ e => patFrames z e
  | .tupE es => patFramesL z es
  | .iterE _ (.mk .list ds) => domsFrame z ds
  | .iterE _ (.mk .opt ds) => domsFrame z ds
  | _ => false

/-- `patFrames` for every pattern of a list. -/
def patFramesL (z : IL.Id) : List Exp → Bool
  | [] => true
  | e :: es => patFrames z e && patFramesL z es

end

/-- The sources of `domsFrame` domains are `patFrames` patterns. -/
theorem patFramesL_domSrc {z : IL.Id} :
    ∀ {ds : List Dom}, domsFrame z ds = true → patFramesL z (ds.map domSrc) = true
  | [], _ => rfl
  | .mk _ e :: ds, h => by
      cases e with
      | varE y =>
          simp only [domsFrame, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
          simp only [List.map_cons, patFramesL, patFrames, domSrc, Bool.and_eq_true, bne_iff_ne,
            ne_eq]
          exact ⟨h.1, patFramesL_domSrc h.2⟩
      | _ => simp [domsFrame] at h

/-- The frame property of matching at fuel `n`, for patterns and pattern lists. -/
def MatchFrameAt (z : IL.Id) (n : Nat) : Prop :=
  (∀ (env : Env) (ρ : VarEnv) (e : Exp) (v : Value) (ρ' : VarEnv), patFrames z e = true →
      matchExp n env ρ e v = .ok ρ' → ρ'.findVal? z = ρ.findVal? z) ∧
  (∀ (env : Env) (ρ : VarEnv) (es : List Exp) (vs : List Value) (ρ' : VarEnv),
      patFramesL z es = true → matchExps n env ρ es vs = .ok ρ' → ρ'.findVal? z = ρ.findVal? z)

/-- The list case of `matchIterE_frame`. -/
theorem matchIterE_list_frame {z : IL.Id} {k : Nat} (ih : ∀ j < k + 1, MatchFrameAt z j)
    {env : Env} {ρ ρ' : VarEnv} {e : Exp} {ds : List Dom} {v : Value}
    (hs : patFramesL z (ds.map domSrc) = true)
    (h : matchIterE k env ρ e .list ds v = .ok ρ') : ρ'.findVal? z = ρ.findVal? z :=
  match k, h with
  | 0, h => by simp [matchIterE] at h
  | 1, h => by simp [matchIterE, matchIterList] at h
  | i + 2, h => by
      have h' : ∃ vs, v.asList? = some vs ∧ ∃ rows,
          matchRounds i env ρ e (ds.map domVar) none 0 vs = .ok rows ∧
            matchExps i env ρ (ds.map domSrc) (iterCols rows ds.length) = .ok ρ' := by
        simpa only [matchIterE, matchIterList, Res.bind_eq_ok, Res.ofOption_eq_ok] using h
      obtain ⟨vs, -, rows, -, hm⟩ := h'
      exact (ih i (by omega)).2 _ _ _ _ _ hs hm

/-- The option case of `matchIterE_frame`. -/
theorem matchIterE_opt_frame {z : IL.Id} {k : Nat} (ih : ∀ j < k + 1, MatchFrameAt z j)
    {env : Env} {ρ ρ' : VarEnv} {e : Exp} {ds : List Dom} {v : Value}
    (hs : patFramesL z (ds.map domSrc) = true)
    (h : matchIterE k env ρ e .opt ds v = .ok ρ') : ρ'.findVal? z = ρ.findVal? z :=
  match k, h with
  | 0, h => by simp [matchIterE] at h
  | j + 1, h => by
      have h' : ∃ vs, matchExps j env ρ (ds.map domSrc) vs = .ok ρ' := by
        simp only [matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨o, -, h⟩ := h
        cases o with
        | none => exact ⟨_, h⟩
        | some w =>
            simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at h
            obtain ⟨σ, -, ws, -, h⟩ := h
            exact ⟨_, h⟩
      obtain ⟨vs, hm⟩ := h'
      exact (ih j (by omega)).2 _ _ _ _ _ hs hm

/-- Matching a variable other than `z` leaves `z` alone. -/
theorem matchExp_varE_frame {z y : IL.Id} (hy : y ≠ z) {m : Nat} {env : Env} {ρ ρ' : VarEnv}
    {v : Value} (h : matchExp (m + 1) env ρ (.varE y) v = .ok ρ') :
    ρ'.findVal? z = ρ.findVal? z := by
  simp only [matchExp] at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h
    exact findVal?_bindVal_ne hy v

/-- Matching a numeral leaves the scope alone. -/
theorem matchExp_numE_frame {z : IL.Id} {m : Nat} {env : Env} {ρ ρ' : VarEnv} {k : Num}
    {v : Value} (h : matchExp (m + 1) env ρ (.numE k) v = .ok ρ') :
    ρ'.findVal? z = ρ.findVal? z := by
  have h' : v = .num k ∧ (Except.ok ρ : Res VarEnv) = .ok ρ' := by
    simpa only [matchExp, Res.assert_eq_ok] using h
  rw [Except.ok.inj h'.2]

/-- The step case of `matchFrameAt` for a single pattern. -/
theorem matchExp_frame_succ {z : IL.Id} {m : Nat} (ih : ∀ j < m + 1, MatchFrameAt z j)
    {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value} (he : patFrames z e = true)
    (h : matchExp (m + 1) env ρ e v = .ok ρ') : ρ'.findVal? z = ρ.findVal? z := by
  match e, he, h with
  | .varE y, he, h => exact matchExp_varE_frame (by simpa [patFrames] using he) h
  | .numE _, _, h => exact matchExp_numE_frame h
  | .caseE op e, he, h =>
      have h' : ∃ p : MixopS × Value, v.asCase? = some p ∧ p.1 = op ∧
          matchExp m env ρ e p.2 = .ok ρ' := by
        simpa only [matchExp, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] using h
      obtain ⟨p, -, -, hm⟩ := h'
      exact (ih m (by omega)).1 _ _ _ _ _ (by simpa [patFrames] using he) hm
  | .tupE es, he, h =>
      have h' : ∃ vs, v.asTuple? = some vs ∧ matchExps m env ρ es vs = .ok ρ' := by
        simpa only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok] using h
      obtain ⟨vs, -, hm⟩ := h'
      exact (ih m (by omega)).2 _ _ _ _ _ (by simpa [patFrames] using he) hm
  | .iterE e (.mk .list ds), he, h =>
      have h' : matchIterE m env ρ e .list ds v = .ok ρ' := by simpa only [matchExp] using h
      exact matchIterE_list_frame ih (patFramesL_domSrc (by simpa [patFrames] using he)) h'
  | .iterE e (.mk .opt ds), he, h =>
      have h' : matchIterE m env ρ e .opt ds v = .ok ρ' := by simpa only [matchExp] using h
      exact matchIterE_opt_frame ih (patFramesL_domSrc (by simpa [patFrames] using he)) h'
  | .iterE _ (.mk .list1 _), he, _ | .iterE _ (.mk (.listN _ _) _), he, _ | .boolE _, he, _
  | .textE _, he, _ | .unE .., he, _ | .binE .., he, _ | .cmpE .., he, _ | .projE .., he, _
  | .uncaseE .., he, _ | .optE _, he, _ | .theE _, he, _ | .strE _, he, _ | .dotE .., he, _
  | .compE .., he, _ | .listE _, he, _ | .liftE _, he, _ | .memE .., he, _ | .lenE _, he, _
  | .catE .., he, _ | .idxE .., he, _ | .sliceE .., he, _ | .updE .., he, _ | .extE .., he, _
  | .callE .., he, _ | .cvtE .., he, _ | .subE .., he, _ => simp [patFrames] at he

/-- The step case of `matchFrameAt` for a pattern list. -/
theorem matchExps_frame_succ {z : IL.Id} {m : Nat} (ih : ∀ j < m + 1, MatchFrameAt z j)
    {env : Env} {ρ ρ' : VarEnv} {es : List Exp} {vs : List Value}
    (hes : patFramesL z es = true) (h : matchExps (m + 1) env ρ es vs = .ok ρ') :
    ρ'.findVal? z = ρ.findVal? z := by
  match es, vs, hes, h with
  | [], [], _, h => simp only [matchExps] at h; cases h; rfl
  | e :: es, v :: vs, hes, h =>
      have hf : patFrames z e = true ∧ patFramesL z es = true := by
        simpa only [patFramesL, Bool.and_eq_true] using hes
      have h' : ∃ σ, matchExp m env ρ e v = .ok σ ∧ matchExps m env σ es vs = .ok ρ' := by
        simpa only [matchExps, Res.bind_eq_ok] using h
      obtain ⟨σ, h₁, h₂⟩ := h'
      rw [(ih m (by omega)).2 _ _ _ _ _ hf.2 h₂, (ih m (by omega)).1 _ _ _ _ _ hf.1 h₁]
  | [], _ :: _, _, h => simp [matchExps] at h
  | _ :: _, [], _, h => simp [matchExps] at h

/-- **The frame lemma for matching**: a `patFrames z` pattern leaves the binding of `z`
alone, at every fuel. -/
theorem matchFrameAt (z : IL.Id) (n : Nat) : MatchFrameAt z n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => exact ⟨fun _ _ _ _ _ _ h => by simp [matchExp] at h,
      fun _ _ _ _ _ _ h => by simp [matchExps] at h⟩
  | m + 1 => exact ⟨fun _ _ _ _ _ he h => matchExp_frame_succ (fun j hj => ih j hj) he h,
      fun _ _ _ _ _ hes h => matchExps_frame_succ (fun j hj => ih j hj) hes h⟩

/-- `matchFrameAt`, for `MatchExp`. -/
theorem matchExp_frame {z : IL.Id} {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value}
    (he : patFrames z e = true) (h : MatchExp env ρ e v ρ') : ρ'.findVal? z = ρ.findVal? z := by
  obtain ⟨n, h⟩ := h
  exact (matchFrameAt z n).1 _ _ _ _ _ he h

mutual

/-- Symbols whose derivations provably leave the binding of `z` alone: terminals,
nonterminals (which restore the caller's scope), sequences and alternatives of such symbols,
attributes `e:g` with a `patFrames z` pattern `e`, and iterations without domains. -/
def symFrames (z : IL.Id) : IL.Sym → Bool
  | .numG _ => true
  | .textG _ => true
  | .epsG => true
  | .varG _ _ => true
  | .seqG gs => symFramesL z gs
  | .altG gs => symFramesL z gs
  | .attrG e g => patFrames z e && symFrames z g
  | .iterG _ (.mk _ []) => true
  | _ => false

/-- `symFrames` for every symbol of a list. -/
def symFramesL (z : IL.Id) : List IL.Sym → Bool
  | [] => true
  | g :: gs => symFrames z g && symFramesL z gs

end

mutual

/-- **The frame lemma for derivations**: deriving a `symFrames z` symbol leaves the binding of
`z` alone. -/
theorem symDerives_frame {z : IL.Id} {env : Env} :
    ∀ (g : IL.Sym) {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value},
      symFrames z g = true → SymDerives env ρ g bs l ρ' → ρ'.findVal? z = ρ.findVal? z
  | .numG n, _, _, _, _, _, h => by
      by_cases hn : n < 256
      · rw [(symDerives_numG hn).mp h |>.2.2]
      · obtain ⟨a, ha, -⟩ := h
        rw [symDen_numG_of_not_lt env hn] at ha
        exact ha.elim
  | .textG _, _, _, _, _, _, h => by rw [(symDerives_textG_elim h).2.2]
  | .epsG, _, _, _, _, _, h => by rw [(symDerives_epsG.mp h).2.2]
  | .varG _ _, _, _, _, _, _, h => by rw [(symDerives_varG_elim h).2]
  | .seqG gs, _, _, _, _, hf, h => symFramesL_seq gs (by simpa [symFrames] using hf) h
  | .altG gs, _, _, _, _, hf, h => by
      obtain ⟨g, hg, hd⟩ := symDerives_altG.mp h
      exact symFramesL_alt gs (by simpa [symFrames] using hf) hg hd
  | .attrG e g, _, _, _, _, hf, h => by
      simp only [symFrames, Bool.and_eq_true] at hf
      obtain ⟨v, ρ₁, hd, -, hm⟩ := symDerives_attrG.mp h
      rw [matchExp_frame hf.1 hm, symDerives_frame g hf.2 hd]
  | .iterG g (.mk it ds), _, _, _, _, hf, h => by
      cases ds with
      | nil =>
          obtain ⟨rows, -, -, -, hb⟩ := symDerives_iterG.mp h
          simp only [BindDoms] at hb
          rw [hb]
      | cons _ _ => simp [symFrames] at hf
  | .rangeG _ _, _, _, _, _, hf, _ => by simp [symFrames] at hf
termination_by structural g => g

/-- `symDerives_frame` for a sequence. -/
theorem symFramesL_seq {z : IL.Id} {env : Env} :
    ∀ (gs : List IL.Sym) {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value},
      symFramesL z gs = true → SymDerives env ρ (.seqG gs) bs l ρ' →
        ρ'.findVal? z = ρ.findVal? z
  | [], _, _, _, _, _, h => by rw [(symDerives_seqG_nil.mp h).2.2]
  | g :: gs, _, _, _, _, hf, h => by
      simp only [symFramesL, Bool.and_eq_true] at hf
      obtain ⟨b₁, l₁, ρ₁, b₂, l₂, h₁, h₂, -, -⟩ := symDerives_seqG_cons.mp h
      rw [symFramesL_seq gs hf.2 h₂, symDerives_frame g hf.1 h₁]
termination_by structural gs => gs

/-- `symDerives_frame` for a member of an alternative. -/
theorem symFramesL_alt {z : IL.Id} {env : Env} :
    ∀ (gs : List IL.Sym) {g : IL.Sym} {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value},
      symFramesL z gs = true → g ∈ gs → SymDerives env ρ g bs l ρ' →
        ρ'.findVal? z = ρ.findVal? z
  | [], _, _, _, _, _, _, hg, _ => absurd hg (List.not_mem_nil)
  | g' :: gs, _, _, _, _, _, hf, hg, h => by
      simp only [symFramesL, Bool.and_eq_true] at hf
      rcases List.mem_cons.mp hg with hgg | hg
      · rw [hgg] at h
        exact symDerives_frame g' hf.1 h
      · exact symFramesL_alt gs hf.2 hg h
termination_by structural gs => gs

end

/-! ## Premises that read an unbound variable -/

/-- Every element of a successful `mapM` succeeds. -/
theorem mapM_ok_mem {α β : Type} {f : α → Res β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → ∀ a ∈ l, ∃ b, f a = .ok b
  | [], _, _, _, ha => absurd ha List.not_mem_nil
  | x :: l, r, h, a, ha => by
      simp only [List.mapM_cons, Res.bind_eq_ok] at h
      obtain ⟨b, hb, bs, hbs, -⟩ := h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨b, hb⟩
      · exact mapM_ok_mem hbs a ha

/-- A variable that is unbound has no value. -/
theorem not_evalExp_varE_none {env : Env} {ρ : VarEnv} {y : IL.Id} (hy : ρ.findVal? y = none)
    {v : Value} : ¬ EvalExp env ρ (.varE y) v := by
  rw [evalExp_varE_iff, hy]
  simp

/-- `evalDoms` fails when a domain is an unbound variable. -/
theorem evalDoms_unbound {env : Env} {ρ : VarEnv} {ds : List Dom} {x y : IL.Id}
    (hd : Dom.mk x (.varE y) ∈ ds) (hy : ρ.findVal? y = none) :
    ∀ {j : Nat} {xvs : List (IL.Id × Value)}, evalDoms j env ρ ds ≠ .ok xvs
  | 0, _, h => by simp [evalDoms] at h
  | i + 1, _, h => by
      rw [evalDoms] at h
      obtain ⟨b, hb⟩ := mapM_ok_mem h _ hd
      obtain ⟨w, hw, -⟩ := Res.map_eq_ok.mp hb
      exact not_evalExp_varE_none hy ⟨i, hw⟩

/-- `premIter` of a `list` iteration fails when a domain is an unbound variable. -/
theorem premIter_list_unbound {env : Env} {ρ ρ' : VarEnv} {pr : Prem} {ds : List Dom}
    {x y : IL.Id} (hd : Dom.mk x (.varE y) ∈ ds) (hy : ρ.findVal? y = none) :
    ∀ {k : Nat}, premIter k env ρ pr .list ds ≠ .ok ρ'
  | 0, h => by simp [premIter] at h
  | j + 1, h => by
      rw [premIter] at h
      obtain ⟨xvs, hx, -⟩ := Res.bind_eq_ok.mp h
      exact evalDoms_unbound hd hy hx

/-- **An iterated premise over an unbound domain fails.** `premIter` evaluates every domain of a
`list` iteration first (`evalDoms`), so if one of them is a variable unbound in the scope, the
premise list starting with it does not hold. -/
theorem not_premsHold_iterPr_of_unbound {env : Env} {ρ ρ' : VarEnv} {pr : Prem} {ds : List Dom}
    {rest : List Prem} {x y : IL.Id} (hd : Dom.mk x (.varE y) ∈ ds) (hy : ρ.findVal? y = none) :
    ¬ PremsHold env ρ (.iterPr pr (.mk .list ds) :: rest) ρ' := by
  rintro ⟨n, h⟩
  match n, h with
  | 0, h => simp [premsHold] at h
  | 1, h => simp [premsHold, premHolds] at h
  | k + 2, h =>
      rw [premsHold, List.foldlM_cons, Res.bind_eq_ok] at h
      obtain ⟨ρ₁, h₁, -⟩ := h
      rw [premHolds] at h₁
      exact premIter_list_unbound hd hy h₁

end Silmaril.Wasm.SpecTec.GrammarInst
