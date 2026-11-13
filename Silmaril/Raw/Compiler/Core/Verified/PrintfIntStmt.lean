module

public import Silmaril.Compiler.Core.Verified.PrintfInputs.Defs
public import Silmaril.Compiler.Core.Verified.PrintfArg.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # The statement `printf("…%d…", e)`, `e` a closed `int` expression

Cerberus elaborates `printf(s, e)`, `s` a string literal with one `%d` and `e` an `int`
expression, to (inside the statement's `bound`)

```
let strong ((f, (r, ps, va, pr)), a, x) =
  unseq(let strong f' = pure(<printf_proxy>) in pure((f', cfunction(f'))),
        <decay of lit>, e) in
if not(params_length(ps) <= 2) then undef(UB038) else
if not(va) || not(are_compatible(int, r)) then undef(UB041) else
let strong p = { <the format argument object, as for printf(s)> } in
let strong i = create_and_store(int, conv_loaded_int(int, x)) in
let strong ret = ccall(ty, f, [p, [(int, i)]]) in
let strong _ = unseq(kill(static const char*, p), kill(static int, i)) in pure(ret)
```

`printfInt file ls fenv e = some (pre, suf, n)` when `e` has this shape, the literal of `ls`
reads `pre%dsuf` with no other conversion (`splitD`), the operand is an `int` expression without
locals (`StateExpr.term`, no slot read) whose value `n` stays in range (`okB`; constant folding of
a pure integer expression), the callee is `printf_proxy`
with std.core's bodies, the helper is std.core's `create_and_store` and the checks fold to
`false`. The machine code prints `n` in decimal at run time (`PrintLink.Item.int`).

`printfTerm` also accepts operands reading State slots, returning the term without evaluating
it. `printfTerm_reaches` is parametric in the current slot values and requires `Term.Ok` and
`StateExpr.Locs`; it preserves all earlier objects and output. The closed interface above is
an instance of this theorem.

`printfTerm_reaches` composes the proved boundaries of the formatted call: the three operands
(`PrintfInputs.unseq_reaches`), the format object (`PrintfStmt.ptrArg_reaches`), the integer
object (`PrintfArg.createStore_reaches`), the call and its cleanup (`PrintfCall.callInt_reaches`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintfIntStmt

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open Fold (WVal WEnv PExp Doc eval matchP extend EnvSub)
open StrMem PrintfStd StrLit PrintfStmt

abbrev EExp := Expr Codec.wireModel Unit Unit Sym

instance (cs : List Int) : Decidable (StringFormat cs) := by unfold StringFormat; infer_instance

/-! ## The recogniser -/

/-- A format `pre%dsuf` without another `%`: `pre` and `suf`. -/
def splitD : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
      if c = '%' then
        match rest with
        | d :: suf => if d = 'd' ∧ suf.all (· != '%') then some ([], suf) else none
        | [] => none
      else (splitD rest).map fun (p, s) => (c :: p, s)

/-- The statement's pieces. -/
def stmtShape : EExp → Option (Pattern Sym × Sym × Sym × EExp × EExp × EExp × PExp × PExp × Sym ×
    EExp × Sym × EExp × EExp)
  | .mk _ (.sseq (.mk _ (.ctor .tuple [pf, .mk _ (.base (some a, _)), .mk _ (.base (some x, _))]))
      (.mk _ (.unseq [t0, t1, t2]))
      (.mk _ (.if_ c1 _ (.mk _ (.if_ c2 _ (.mk _ (.sseq (.mk _ (.base (some p, _))) argobj
        (.mk _ (.sseq (.mk _ (.base (some i, _))) iarg rest))))))))) =>
      some (pf, a, x, t0, t1, t2, c1, c2, p, argobj, i, iarg, rest)
  | _ => none

/-- `create_and_store(int, conv_loaded_int(int, x))`: the helper, the conversion and `x`. -/
def intArg : EExp → Option (Sym × Sym × Sym)
  | .mk _ (.proc _ (.sym f) [.mk _ _ (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))),
      .mk _ _ (.call (.sym cv) [.mk _ _ (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))),
        .mk _ _ (.sym x)])]) => some (f, cv, x)
  | _ => none

/-- The range checks of `StateExpr.Term.Ok`, computed. -/
def okB (σ : StateExpr.Key → Int) : StateExpr.Term → Bool
  | .lit c => decide (-2147483648 ≤ c ∧ c ≤ 2147483647)
  | .var q => decide (-2147483648 ≤ σ q ∧ σ q ≤ 2147483647)
  | .bin op a b => okB σ a && okB σ b &&
      decide (-2147483648 ≤ Guard.apply op (a.val σ) (b.val σ) ∧
        Guard.apply op (a.val σ) (b.val σ) ≤ 2147483647)
  | .cmp _ c₁ c₂ a b => okB σ a && okB σ b && decide (-2147483648 ≤ c₁ ∧ c₁ ≤ 2147483647) &&
      decide (-2147483648 ≤ c₂ ∧ c₂ ≤ 2147483647)
  | .cond c a b => okB σ c && (if c.val σ = 0 then okB σ a else okB σ b)
  | .un u a => okB σ a && decide (-2147483648 ≤ u.apply (a.val σ) ∧ u.apply (a.val σ) ≤ 2147483647)
  | .bit _ a b => okB σ a && okB σ b
  | .divpos _ _ a => okB σ a

/-- The characters of a format, without its terminator. -/
def chars (cs : List Int) : List Char := cs.dropLast.map fun c => Char.ofNat c.toNat

/-- **The statement** `printf("pre%dsuf", e)`: the literal parts and an open integer term.
The recogniser checks syntax and helper bodies; its caller proves validity for the current slots. -/
def printfTerm (file : Doc) (ls : List (Sym × List Int)) (fenv : WEnv) (e : EExp) :
    Option (List Char × List Char × StateExpr.Term) := do
  let (pf, a, x, t0, t1, t2, c1, c2, p, argobj, i, iarg, rest) ← stmtShape e
  let w0 ← ExitCall.calleeTask file t0
  let lit ← fmtTask t1
  let t ← StateExpr.term file t2
  let cs ← litOf ls lit
  let (pre, suf) ← splitD (chars cs)
  let xs ← matchP pf w0
  let _ ← ptrArg file (extend xs fenv) a argobj
  let (f, cv, x') ← intArg iarg
  let (g, q, p') ← PrintfCall.callInt rest
  match (extend xs fenv).lookup g with
  | some (.loaded (.specified (.pointer (.function y)))) =>
      if StringFormat cs ∧ (∀ y ∈ xs, y.1.key ≠ a.key ∧ y.1.key ≠ x.key) ∧ a.key ≠ x.key ∧
          fenv.lookup a = none ∧ fenv.lookup x = none ∧
          ExitCall.foldsFalse file (extend xs fenv) c1 ∧ ExitCall.foldsFalse file (extend xs fenv) c2 ∧
          x'.key = x.key ∧ x.key ≠ p.key ∧ p.key ≠ i.key ∧ q.key = p.key ∧ p'.key = i.key ∧
          g.key ≠ p.key ∧ g.key ≠ i.key ∧ (stdOf file y).isSome ∧ PrintfArg.isCreateStore file f ∧
          ConvInt.isConvLoadedInt file cv
      then some (pre, suf, t) else none
  | _ => none

/-- The closed-operand interface retained by the existing printf fragment. -/
def printfInt (file : Doc) (ls : List (Sym × List Int)) (fenv : WEnv) (e : EExp) :
    Option (List Char × List Char × Int) := do
  let (pre, suf, t) ← printfTerm file ls fenv e
  if t.vars.isEmpty ∧ okB (fun _ => 0) t then some (pre, suf, t.val fun _ => 0) else none

/-- What the statement prints. -/
def text (pre suf : List Char) (n : Int) : String :=
  String.ofList pre ++ (toString n ++ String.ofList suf)

/-! ## Inversions -/

theorem splitD_spec : ∀ {l pre suf : List Char}, splitD l = some (pre, suf) →
    l = pre ++ '%' :: 'd' :: suf ∧ (∀ c ∈ pre, c ≠ '%') ∧ (∀ c ∈ suf, c ≠ '%')
  | [], _, _, h => by simp [splitD] at h
  | c :: rest, pre, suf, h => by
    unfold splitD at h
    split at h
    · rename_i hc
      subst hc
      split at h
      · rename_i d s
        split at h
        · rename_i hds
          obtain ⟨rfl, hall⟩ := hds
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [List.all_eq_true, bne_iff_ne, ne_eq] at hall
          exact ⟨rfl, by simp, hall⟩
        · cases h
      · cases h
    · rename_i hc
      obtain ⟨⟨p, s⟩, hp, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨e, hpre, hsuf⟩ := splitD_spec hp
      refine ⟨by rw [e]; rfl, ?_, hsuf⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hc
      · exact hpre y hy

theorem stmtShape_inv {e : EExp} {pf : Pattern Sym} {a x : Sym} {t0 t1 t2 : EExp} {c1 c2 : PExp}
    {p i : Sym} {argobj iarg rest : EExp}
    (h : stmtShape e = some (pf, a, x, t0, t1, t2, c1, c2, p, argobj, i, iarg, rest)) :
    ∃ a0 a1 pa ba pxa bx a2 a3 u3 a4 u4 a5 pp bp a6 pi bi,
      e = .mk a0 (.sseq (.mk a1 (.ctor .tuple [pf, .mk pa (.base (some a, ba)), .mk pxa (.base (some x, bx))]))
        (.mk a2 (.unseq [t0, t1, t2])) (.mk a3 (.if_ c1 u3 (.mk a4 (.if_ c2 u4
          (.mk a5 (.sseq (.mk pp (.base (some p, bp))) argobj
            (.mk a6 (.sseq (.mk pi (.base (some i, bi))) iarg rest))))))))) := by
  unfold stmtShape at h; split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

theorem intArg_inv {e : EExp} {f cv x : Sym} (h : intArg e = some (f, cv, x)) :
    ∃ A U b1 u1 c1 b2 u2 b3 u3 c3 b4 u4, e = .mk A (.proc U (.sym f)
      [.mk b1 u1 (.val (.ctype (.mk c1 (.basic (.integer (.signed .int)))))),
       .mk b2 u2 (.call (.sym cv) [.mk b3 u3 (.val (.ctype (.mk c3 (.basic (.integer (.signed .int)))))),
        .mk b4 u4 (.sym x)])]) := by
  unfold intArg at h; split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

theorem okB_ok (σ : StateExpr.Key → Int) : (t : StateExpr.Term) → okB σ t = true → t.Ok σ
  | .lit c, h => by simp only [okB, decide_eq_true_eq] at h; exact h
  | .var q, h => by simp only [okB, decide_eq_true_eq] at h; exact h
  | .bin op a b, h => by
    simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨okB_ok σ a h.1.1, okB_ok σ b h.1.2, h.2⟩
  | .cmp r c₁ c₂ a b, h => by
    simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨okB_ok σ a h.1.1.1, okB_ok σ b h.1.1.2, h.1.2, h.2⟩
  | .cond c a b, h => by
    show c.Ok σ ∧ (if c.val σ = 0 then a.Ok σ else b.Ok σ)
    simp only [okB, Bool.and_eq_true] at h
    obtain ⟨hc, h2⟩ := h
    refine ⟨okB_ok σ c hc, ?_⟩
    split at h2 <;> split <;> first | exact okB_ok σ _ h2 | (exfalso; contradiction)
  | .un u a, h => by
    simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨okB_ok σ a h.1, h.2⟩
  | .bit o a b, h => by
    simp only [okB, Bool.and_eq_true] at h
    exact ⟨okB_ok σ a h.1, okB_ok σ b h.2⟩
  | .divpos o d a, h => by
    simp only [okB] at h
    exact okB_ok σ a h

/-! ## The run -/

/-- **The statement `printf("pre%dsuf", e)` runs**: it prints `pre`, the decimal digits of `e`
and `suf`, and returns their number, keeping every earlier object, killing only its two argument
objects, using at most 32 bytes below the last allocation. -/
theorem printfTerm_reaches {file : Program} {labels : Labels} {ls : List (Sym × List Int)}
    {fenv : WEnv} {e : EExp} {pre suf : List Char} {t : StateExpr.Term}
    (h : printfTerm file ls fenv e = some (pre, suf, t))
    {σ : StateExpr.Key → Int} (ok : t.Ok σ)
    {env : Env} (hr : EnvSub fenv env) {m : Mem.Concrete.State} (hlit : LitEnv ls env m)
    (locs : StateExpr.Locs env m σ t)
    (hdead : DeadBelow m) (hroom : 64 ≤ m.lastAddress) (ann : List Annot) (k : List Frame) :
    ∃ m', ReturnConst.Reaches file labels ⟨.effectExpr (.mk ann (.bound e)) env, k, m⟩
        ⟨.value (.loaded (.specified (.integer (text pre suf (t.val σ)).length))), k, m'⟩ ∧
      m'.stdout = m.stdout ++ text pre suf (t.val σ) ∧ Keeps m m' ∧ DeadBelow m' ∧
      m.lastAddress - 32 ≤ m'.lastAddress := by
  unfold printfTerm at h
  obtain ⟨⟨pf, a, x, t0, t1, t2, c1, c2, p, argobj, i, iarg, rest⟩, q1, h⟩ := bind_some h
  try dsimp only at h
  obtain ⟨w0, q2, h⟩ := bind_some h
  obtain ⟨lit, q3, h⟩ := bind_some h
  obtain ⟨t', q4, h⟩ := bind_some h
  obtain ⟨cs, q5, h⟩ := bind_some h
  obtain ⟨⟨pre', suf'⟩, q6, h⟩ := bind_some h; try dsimp only at h
  obtain ⟨xs, q7, h⟩ := bind_some h
  obtain ⟨ct, q8, h⟩ := bind_some h
  obtain ⟨⟨f, cv, x'⟩, q9, h⟩ := bind_some h; try dsimp only at h
  obtain ⟨⟨g, q, p'⟩, q10, h⟩ := bind_some h; try dsimp only at h
  split at h
  case h_2 => cases h
  rename_i y hgl
  split at h
  case isFalse => cases h
  rename_i hc
  cases h
  obtain ⟨hcs, hxa, hax, hfa, hfx, hc1, hc2, hx'x, hxp, hpi, hqp, hp'i, hgp, hgi, hsy, hcr, hcv⟩ := hc
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hsy
  obtain ⟨a0, a1, pa, ba, pxa, bx, a2, a3, u3, a4, u4, a5, pp, bp, a6, pi, bi, rfl⟩ := stmtShape_inv q1
  obtain ⟨hshape, hpre, hsuf⟩ := splitD_spec q6
  have hn := StateExpr.Term.int_of_ok t ok
  obtain ⟨lx, hmem, hlk⟩ := litOf_mem q5
  obtain ⟨sid, saddr, hlx, hstr, hpos0, hlt0⟩ := hlit lx cs hmem
  have hl : env.lookup lit = some (.object (.pointer (.allocated sid saddr))) := by
    rw [← ReturnLit.lookup_key hlk]; exact hlx
  let V : Val := .loaded (.specified (.pointer (.allocated sid saddr)))
  let N : Val := .loaded (.specified (.integer (t.val σ)))
  let REST : EExp := .mk a6 (.sseq (.mk pi (.base (some i, bi))) iarg rest)
  let PAT : Pattern Sym :=
    .mk a1 (.ctor .tuple [pf, .mk pa (.base (some a, ba)), .mk pxa (.base (some x, bx))])
  let K1 : List Frame := .strongBind PAT
    (.mk a3 (.if_ c1 u3 (.mk a4 (.if_ c2 u4 (.mk a5 (.sseq (.mk pp (.base (some p, bp))) argobj REST))))))
    env :: .bound :: k
  obtain ⟨m1, ys, ru, -, touched, keep1⟩ := PrintfInputs.unseq_reaches file labels q2 q3 q4
    ok hl a2 K1 m hstr locs
  obtain ⟨l1, u1, rfl⟩ := touched
  have hm : matchPattern PAT (.tuple [runtimeValue w0, V, N]) =
      some (Fold.bmap xs ++ [(a, V), (x, N)]) := by
    simp [PAT, matchPattern, matchPatterns, Fold.matchP_rv, q7, bind, Option.bind]
  let E1 : Env := extendEnv (Fold.bmap xs ++ [(a, V), (x, N)]) env
  have eE1 : E1 = extendEnv (Fold.bmap xs) ((env.insert x N).insert a V) := extendEnv_append _ _ _
  have hr1 : EnvSub (extend xs fenv) E1 := by
    rw [eE1]; exact ((hr.insert_right hfx N).insert_right hfa V).extend xs
  have hxa' : ∀ z ∈ Fold.bmap xs, z.1.key ≠ a.key := by
    intro z hz
    simp only [Fold.bmap, List.mem_map] at hz
    obtain ⟨⟨s', w'⟩, hs', rfl⟩ := hz
    exact (hxa _ hs').1
  have hxx' : ∀ z ∈ Fold.bmap xs, z.1.key ≠ x.key := by
    intro z hz
    simp only [Fold.bmap, List.mem_map] at hz
    obtain ⟨⟨s', w'⟩, hs', rfl⟩ := hz
    exact (hxa _ hs').2
  have haE : E1.lookup a = some V := by
    rw [eE1, lookup_extend_other hxa']
    exact Map.lookup_insert _ _ _
  have hxE : E1.lookup x = some N := by
    rw [eE1, lookup_extend_other hxx', Map.lookup_insert_of_key_ne _ _ (Ne.symm hax)]
    exact Map.lookup_insert _ _ _
  let M0 : Mem.Concrete.State := {m with currentLocation := l1, lastUsed := u1}
  let M : Mem.Concrete.State := SeqReach.focusMemory a4 (SeqReach.focusMemory a3 M0)
  have kM : Keeps m M := (keep1.trans (PrintfStd.keeps_focus a3 _)).trans (PrintfStd.keeps_focus a4 _)
  have hMl : M.lastAddress = m.lastAddress := by simp [M, M0]
  have hMn : M.nextId = m.nextId := by simp [M, M0]
  have hMd : M.dead = m.dead := by simp [M, M0]
  have hb := ptrAddr_bounds M
  let K2 : List Frame := .annotations ys :: .bound :: k
  obtain ⟨xs2, M2, r8, hobj, k8, o8, n8, l8, d8⟩ := ptrArg_reaches file labels hr1 q8 haE
    ⟨hpos0, by omega⟩ (.strongBind (.mk pp (.base (some p, bp))) REST E1 :: K2) M
    (by omega) (by rw [hMn, hMd]; intro hmem'; exact absurd (hdead _ hmem') (lt_irrefl _))
  let PV : Val := .object (.pointer (.allocated M.nextId (ptrAddr M)))
  let E2 : Env := extendEnv [(p, PV)] E1
  -- the integer argument object
  obtain ⟨A, U, b1, uu1, cc1, b2, uu2, b3, uu3, cc3, b4, uu4, rfl⟩ := intArg_inv q9
  cases uu1; cases uu2; cases uu3; cases uu4
  have hx2 : E2.lookup x' = some N := by
    rw [ReturnLit.lookup_key hx'x, lk_other hxp]; exact hxE
  let K3 : List Frame := .strongBind (.mk pi (.base (some i, bi))) rest E2 :: .annotations xs2 :: K2
  have hargs : List.Forall₂ (fun p v => SeqReach.PureEval file labels p E2 v)
      [.mk b1 () (.val (.ctype (.mk cc1 (.basic (.integer (.signed .int)))))),
       .mk b2 () (.call (.sym cv) [.mk b3 () (.val (.ctype (.mk cc3 (.basic (.integer (.signed .int)))))),
        .mk b4 () (.sym x')])]
      [.ctype (Mem.Concrete.intType cc1), N] := by
    refine .cons (SeqReach.pure_value b1 _ E2) (.cons ?_ .nil)
    intro k' m'
    exact (Eval.sound file _ (ConvInt.convLoadedInt_eval (ann := cc3) hcv hn
      (.cons .val (.cons (.sym hx2) .nil)))) labels k' m' rfl
  have rproc := PrintfStd.proc_apply (file := file) (labels := labels) A U f hargs K3 M2
  let M3 : Mem.Concrete.State := SeqReach.focusMemory A M2
  have k3 : Keeps M2 M3 := PrintfStd.keeps_focus A M2
  have hM3n : M3.nextId = M2.nextId := by simp [M3]
  have hM3l : M3.lastAddress = M2.lastAddress := by simp [M3]
  have hM3d : M3.dead = M2.dead := by simp [M3]
  have hM3o : M3.stdout = M2.stdout := by simp [M3]
  have hib := Globals.nextIntAddress_bounds M3
  obtain ⟨m4, zs, rcs, slot, k4, o4, n4, l4, d4⟩ := PrintfArg.createStore_reaches (file := file)
    (labels := labels) hcr E2 K3 M3 cc1 hn (by omega)
    (by rw [hM3n, hM3d, n8, d8, hMn, hMd]; intro hmem'; have := hdead _ hmem'; omega)
  let IV : Val := .object (.pointer (.allocated M3.nextId (Mem.Concrete.nextIntAddress M3)))
  let E3 : Env := extendEnv [(i, IV)] E2
  have hg3 : E3.lookup g = some (.loaded (.specified (.pointer (.function y)))) := by
    rw [lk_other hgi, lk_other hgp]; exact hr1 g _ hgl
  have hqi : q.key ≠ i.key := by rw [hqp]; exact hpi
  have hq3 : E3.lookup q = some PV := by
    rw [lk_other hqi]; exact lk_same hqp _ _
  have hp3 : E3.lookup p' = some IV := lk_same hp'i _ _
  have k24 : Keeps M2 m4 := k3.trans k4
  have hstr4 : StrObj m4 sid saddr cs := hstr.keeps (kM.trans (k8.trans k24))
  obtain ⟨m', zs2, r10, o10, n10, l10, d10, kk10⟩ := PrintfCall.callInt_reaches file labels q10 hs hg3
    hq3 hp3 hcs (hobj.keeps k24) hstr4 slot (by omega) (by omega) hn
    (by omega) pre suf hpre hsuf hshape (.annotations zs :: .annotations xs2 :: K2)
  have chain := (ExitCall.lift file labels (ExitCall.ra_bound file labels ann _) (ExitCall.plain_effectExpr _ _)).trans
    ((ExitCall.lift file labels (ExitCall.ra_sseq file labels a0 _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    (ru.trans
    ((PrintfStd.v_strongBind ys hm _ _).trans
    ((if_false_sub file labels hr1 hc1 _ _).trans
    ((if_false_sub file labels hr1 hc2 _ _).trans
    ((ExitCall.lift file labels (ExitCall.ra_sseq file labels a5 _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    (r8.trans
    ((PrintfStd.v_strongBind xs2 rfl _ _).trans
    ((ExitCall.lift file labels (ExitCall.ra_sseq file labels a6 _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    (rproc.trans
    (rcs.trans
    ((PrintfStd.v_strongBind zs rfl _ _).trans
    (r10.trans
    ((PrintfStd.v_merge _ _ _ _ _).trans
    ((PrintfStd.v_merge _ _ _ _ _).trans
    ((PrintfStd.v_merge _ _ _ _ _).trans
    (v_bound _ _ k _)))))))))))))))))
  refine ⟨m', chain, ?_, kk10 m (kM.trans (k8.trans k24)) (by omega) (by omega), ?_, ?_⟩
  · rw [o10, o4, hM3o, o8]; simp [M, M0, text]
  · intro j hj
    rw [d10, d4, hM3d, d8, hMd] at hj
    rw [n10, n4]
    rcases List.mem_cons.mp hj with rfl | hj
    · omega
    rcases List.mem_cons.mp hj with rfl | hj
    · omega
    · have := hdead j hj; omega
  · omega

/-- An invalid open operand reaches overflow through the enclosing statement and arena.
No format or argument object needs to be allocated on this path. -/
theorem printfTerm_fails {file : Program} {labels : Labels} {ls : List (Sym × List Int)}
    {fenv : WEnv} {e : EExp} {pre suf : List Char} {t : StateExpr.Term}
    (h : printfTerm file ls fenv e = some (pre, suf, t))
    {env : Env} {m : Mem.Concrete.State} {σ : StateExpr.Key → Int}
    (bad : ¬ t.Ok σ) (locs : StateExpr.Locs env m σ t)
    (ann : List Annot) (k : List Frame) :
    ArenaFail.Fails file labels false ⟨.effectExpr (.mk ann (.bound e)) env, k, m⟩
      IntExpr.overflow := by
  unfold printfTerm at h
  obtain ⟨⟨pf, a, x, t0, t1, t2, c1, c2, p, argobj, i, iarg, rest⟩, q1, h⟩ := bind_some h
  try dsimp only at h
  obtain ⟨w0, q2, h⟩ := bind_some h
  obtain ⟨lit, q3, h⟩ := bind_some h
  obtain ⟨t', q4, h⟩ := bind_some h
  obtain ⟨cs, _, h⟩ := bind_some h
  obtain ⟨⟨pre', suf'⟩, _, h⟩ := bind_some h; try dsimp only at h
  obtain ⟨xs, _, h⟩ := bind_some h
  obtain ⟨ct, _, h⟩ := bind_some h
  obtain ⟨⟨f, cv, x'⟩, _, h⟩ := bind_some h; try dsimp only at h
  obtain ⟨⟨g, q, p'⟩, _, h⟩ := bind_some h; try dsimp only at h
  split at h
  case h_2 => cases h
  split at h
  case isFalse => cases h
  cases h
  obtain ⟨a0, a1, pa, ba, pxa, bx, a2, a3, u3, a4, u4, a5, pp, bp, a6, pi, bi, rfl⟩ := stmtShape_inv q1
  apply ArenaFail.Fails.pre file labels
    (ExitCall.local_next file labels (ExitCall.ra_bound file labels ann _) (ExitCall.plain_effectExpr _ _))
  apply ArenaFail.Fails.pre file labels
    (ExitCall.local_next file labels (ExitCall.ra_sseq file labels a0 _ _ _) (ExitCall.plain_effectExpr _ _))
  exact PrintfInputs.unseq_fails file labels q2 q3 q4 bad a2 _ m locs

/-- The closed statement is an instance of the open statement with no slot reads. -/
theorem printfInt_reaches {file : Program} {labels : Labels} {ls : List (Sym × List Int)}
    {fenv : WEnv} {e : EExp} {pre suf : List Char} {n : Int}
    (h : printfInt file ls fenv e = some (pre, suf, n))
    {env : Env} (hr : EnvSub fenv env) {m : Mem.Concrete.State} (hlit : LitEnv ls env m)
    (hdead : DeadBelow m) (hroom : 64 ≤ m.lastAddress) (ann : List Annot) (k : List Frame) :
    ∃ m', ReturnConst.Reaches file labels ⟨.effectExpr (.mk ann (.bound e)) env, k, m⟩
        ⟨.value (.loaded (.specified (.integer (text pre suf n).length))), k, m'⟩ ∧
      m'.stdout = m.stdout ++ text pre suf n ∧ Keeps m m' ∧ DeadBelow m' ∧
      m.lastAddress - 32 ≤ m'.lastAddress := by
  unfold printfInt at h
  obtain ⟨⟨pre', suf', t⟩, ht, h⟩ := bind_some h
  dsimp only at h
  split at h
  · rename_i hc
    cases h
    exact printfTerm_reaches ht (okB_ok _ t hc.2) hr hlit
      (fun q hq => by simp [List.isEmpty_iff.mp hc.1] at hq) hdead hroom ann k
  · cases h

end Silmaril.Compile.Core.Verified.PrintfIntStmt
