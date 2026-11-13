module

public import Silmaril.Compiler.Core.Verified.TyMem.Defs
/-! # Statements over several typed locals

`StateStmt` for locals of every supported integer type. The block's locals are `xs`, each with
its type; a statement's runs from a memory satisfying `TyMem.Inv`:

* `x = e;` (`assignStmt`): the negative store of `conv_loaded_int(T, t)` into `x` of type `T`,
  lifted to the enclosing `bound`; `x` then holds `cv T` of the value (`assign_runs`).
* `T x = e;` (`initStmt`): `let strong t = bound(e) in store(T, x, conv_loaded_int(T, t))`
  (`init_runs`).
* `T x;` (`uninitStmt`): `store(T, x, Unspecified(T))` (`uninit_runs`).
* `return e;` (`retStmt`): `let strong u = bound(e) in kill(T₁, x₁); …; kill(Tₙ, xₙ);
  run ret(conv_loaded_int(R, u))` (`ret_halts`): the value `cv R` of `e`, the term `convT R e`.
* `if (c) return e;` (`ifRet`): as in `StateStmt` (`ifRet_runs`).

Each run reaches undefined behaviour (a signed operator leaves its type) or its normal end.
Values are those of the closed terms `TyExpr.close (defsOf ds) t`; a conversion to `T` is the
term `convT T t`, the wrap-around (`TyConv.cv`) computed as `t + 0` wrapped at `T`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyStmt

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches tagsOf)
open Silmaril.Cerberus.Core.PureEvalExt (Ev)
open Mem.Concrete (LiveSz tyType)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ReturnConst (focusMemory)
open TyActions (supported width signed Fits TSlot stored)
open TyConv (cv isConvLoaded)
open TyExpr (Key Term term zero values close)
open TyMem (Local Inv Defined defsOf update ptr Typed noLoc)
open StateStmt (Overflows fails_overflows lookup_two_fst lookup_two_snd pure_unit_reaches bound_pop
  sym_readTask boolSource_touched seqFocus_touched)
open IntExpr (spec overflow)
open LoadTask (Touched)

variable {file : Program} {labels : Labels}

/-! ## Conversions as terms -/

/-- The conversion of `t` to `ity`: `t + 0` wrapped at `ity`. -/
def convT (ity : IntegerType) (t : Term) : Term := .bin (.wrap ity .add) t (.lit 0)

theorem fits_zero {ity : IntegerType} (hs : supported ity = true) : Fits ity 0 :=
  TyConv.fits_zero hs

theorem convT_val {ity : IntegerType} (hs : supported ity = true) (t : Term) (σ : Key → Int) :
    (convT ity t).val σ = cv ity (t.val σ) := by
  simp only [convT, Term.val, TyGuard.G.val, Guard.apply]
  rw [TyConv.cv_of_fits hs (fits_zero hs), Int.add_zero, TyConv.cv_of_fits hs (TyConv.cv_fits hs _)]

theorem close_convT (ds : Key → Term) (ity : IntegerType) (t : Term) :
    close ds (convT ity t) = convT ity (close ds t) := rfl

/-! ## Recognisers -/

/-- The locals of a block: symbols and types. -/
abbrev Vars := List (Sym × IntegerType)

/-- `x` is a local of type `ity`. -/
def isLocal (xs : Vars) (x : Sym) (ity : IntegerType) : Bool :=
  xs.any fun y => y.1.key == x.key && y.2 == ity

/-- The key of `x` is no local's. -/
def isFresh (xs : Vars) (x : Sym) : Bool := xs.all fun y => y.1.key != x.key

/-- `t` reads locals at their types. -/
def typedIn (xs : Vars) (t : Term) : Bool :=
  t.vars.all fun q => xs.any fun y => y.1.key == q.1 && y.2 == q.2

/-- `x = e;` -/
def assignStmt (file : File Codec.wireModel Unit Unit) : Eff → Option (Sym × IntegerType × Term)
  | .mk _ (.sseq (.mk _ (.base (none, _)))
      (.mk _ (.bound (.mk _ (.wseq
        (.mk _ (.ctor .tuple [.mk _ (.base (some p, _)), .mk _ (.base (some t, _))]))
        (.mk _ (.unseq [.mk _ (.pure (.mk _ () (.sym x))), e]))
        (.mk _ (.wseq (.mk _ (.base (none, _)))
          (.mk sann (.action (.mk .neg (.mk _ _ (.store false
            (.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity))))))
            (.mk _ () (.sym p'))
            (.mk _ () (.call (.sym s) [.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity₂))))),
              .mk _ () (.sym t')])) .na)))))
          (.mk _ (.pure (.mk _ () (.call (.sym s') [.mk _ () (.val (.ctype (.mk _
            (.basic (.integer ity₃))))), .mk _ () (.sym t'')]))))))))))
      (.mk _ (.pure (.mk _ () (.val .unit))))) =>
      if p'.key = p.key ∧ t'.key = t.key ∧ t''.key = t.key ∧ t.key ≠ p.key ∧ noLoc sann = true ∧
          isConvLoaded file s = true ∧ isConvLoaded file s' = true ∧ ity₂ = ity ∧ ity₃ = ity ∧
          supported ity = true then
        (term file e).map fun te => (x, ity, te)
      else none
  | _ => none

/-- `T x = e;` -/
def initStmt (file : File Codec.wireModel Unit Unit) : Eff → Option (Sym × IntegerType × Term)
  | .mk _ (.sseq (.mk _ (.base (some t, _))) (.mk _ (.bound e))
      (.mk _ (.action (.mk .pos (.mk _ _ (.store false
        (.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity))))))
        (.mk _ () (.sym x))
        (.mk _ () (.call (.sym s) [.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity₂))))),
          .mk _ () (.sym t')])) .na)))))) =>
      if t'.key = t.key ∧ t.key ≠ x.key ∧ isConvLoaded file s = true ∧ ity₂ = ity ∧
          supported ity = true then
        (term file e).map fun te => (x, ity, te)
      else none
  | _ => none

/-- `T x;`: the store of `Unspecified(T)`. -/
def uninitStmt : Eff → Option (Sym × IntegerType)
  | .mk _ (.action (.mk .pos (.mk _ _ (.store false
      (.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity))))))
      (.mk _ () (.sym x))
      (.mk _ () (.val (.loaded (.unspecified (.mk _ (.basic (.integer ity₂))))))) .na)))) =>
      if ity₂ = ity ∧ supported ity = true then some (x, ity) else none
  | _ => none

/-- `kill(T, x)`. -/
def killTy (x : Sym) (ity : IntegerType) : Eff → Bool
  | .mk _ (.action (.mk .pos (.mk _ _ (.kill (.static (.mk _ (.basic (.integer ity'))))
      (.mk _ () (.sym x')))))) => x'.key = x.key && ity' == ity
  | _ => false

/-- `run ret(conv_loaded_int(R, u))`: the type `R`. -/
def runRet (file : File Codec.wireModel Unit Unit) (ret u : Sym) : Eff → Option IntegerType
  | .mk _ (.run () l [.mk _ () (.call (.sym s)
      [.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity))))), .mk _ () (.sym u')])]) =>
      if l.key = ret.key ∧ u'.key = u.key ∧ isConvLoaded file s = true ∧ supported ity = true then
        some ity
      else none
  | _ => none

/-- `kill(T₁, x₁); …; kill(Tₙ, xₙ); run ret(conv_loaded_int(R, u))`. -/
def killsRun (file : File Codec.wireModel Unit Unit) (ret u : Sym) : Vars → Eff → Option IntegerType
  | [], e => runRet file ret u e
  | x :: xs, e => match e with
    | .mk _ (.sseq (.mk _ (.base (none, _))) kl rest) =>
        if killTy x.1 x.2 kl = true then killsRun file ret u xs rest else none
    | _ => none

/-- `return e;` in a block with the locals `xs`: the returned term, converted. -/
def retStmt (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : Vars) : Eff → Option Term
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e)) kr) =>
      if isFresh xs u = true then
        match killsRun file ret u xs kr, term file e with
        | some r, some t => some (convT r t)
        | _, _ => none
      else none
  | _ => none

/-- `if (c) return e;` in a block with the locals `xs`: the test and the returned term. -/
def ifRet (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : Vars) :
    Eff → Option (Term × Term)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec))
      (.mk _ (.sseq (.mk _ (.base (some b, _))) cb
        (.mk _ (.if_ (.mk _ () (.sym b')) ea (.mk _ (.pure (.mk _ () (.val .unit))))))))) =>
      if b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ isFresh xs c = true ∧ isFresh xs b = true then
        match term file ec, retStmt file ret xs ea with
        | some tc, some ta => some (tc, ta)
        | _, _ => none
      else none
  | _ => none

/-! ## Locals -/

/-- Locals whose keys and types are those of `xs`. -/
def Keys (ls : List Local) (xs : Vars) : Prop :=
  ls.map (fun l => (l.sym.key, l.ity)) = xs.map (fun y => (y.1.key, y.2))

theorem Keys.keys {ls : List Local} {xs : Vars} (h : Keys ls xs) :
    ls.map (·.sym.key) = xs.map (·.1.key) := by
  have := congrArg (List.map Prod.fst) h
  simpa [List.map_map, Function.comp_def] using this

theorem Keys.fresh {ls : List Local} {xs : Vars} (h : Keys ls xs) {u : Sym}
    (hu : isFresh xs u = true) : ∀ l ∈ ls, l.sym.key ≠ u.key := by
  intro l hl
  have hm : l.sym.key ∈ xs.map (·.1.key) := by
    rw [← h.keys]; exact List.mem_map_of_mem hl
  obtain ⟨y, hy, hyk⟩ := List.mem_map.mp hm
  have := List.all_eq_true.mp hu y hy
  simp only [bne_iff_ne, ne_eq] at this
  rw [← hyk]; exact this

theorem Keys.mem {ls : List Local} {xs : Vars} (h : Keys ls xs) {k : Key} {ity : IntegerType}
    (hx : xs.any (fun y => y.1.key == k && y.2 == ity) = true) :
    ∃ l ∈ ls, l.sym.key = k ∧ l.ity = ity := by
  obtain ⟨y, hy, hyx⟩ := List.any_eq_true.mp hx
  simp only [Bool.and_eq_true, beq_iff_eq] at hyx
  have hm : (y.1.key, y.2) ∈ ls.map (fun l => (l.sym.key, l.ity)) := by
    rw [h]; exact List.mem_map_of_mem (f := fun y => (y.1.key, y.2)) hy
  obtain ⟨l, hl, hlk⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at hlk
  exact ⟨l, hl, hlk.1.trans hyx.1, hlk.2.trans hyx.2⟩

theorem Keys.mem_of_local {ls : List Local} {xs : Vars} (h : Keys ls xs) {x : Sym} {ity : IntegerType}
    (hx : isLocal xs x ity = true) : ∃ l ∈ ls, x.key = l.sym.key ∧ l.ity = ity := by
  obtain ⟨l, hl, hk, ht⟩ := h.mem hx
  exact ⟨l, hl, hk.symm, ht⟩

theorem Keys.typed {ls : List Local} {xs : Vars} (h : Keys ls xs) {t : Term}
    (ht : typedIn xs t = true) : Typed ls t := by
  intro q hq
  exact h.mem (List.all_eq_true.mp ht q hq)

/-! ## Shows -/

/-- What a run from a statement shows: the value `v` returned, or undefined behaviour. -/
def Shows (s : State) (v : Int) (stdout : String) : Prop :=
  (∃ m', m'.stdout = stdout ∧ Reaches file labels s ⟨.halt (.defined (spec v)), [], m'⟩) ∨
  ∃ s', Reaches file labels s s' ∧ s'.control = .halt overflow

theorem Shows.pre {s s' : State} {v : Int} {out : String}
    (h : Reaches file labels s s') (o : Shows (file := file) (labels := labels) s' v out) :
    Shows (file := file) (labels := labels) s v out := by
  rcases o with ⟨m', hout, r⟩ | ⟨s'', r, hs⟩
  · exact .inl ⟨m', hout, h.trans r⟩
  · exact .inr ⟨s'', h.trans r, hs⟩

theorem Shows.of_overflows {s : State} {v : Int} {out : String}
    (o : Overflows (file := file) (labels := labels) s) : Shows (file := file) (labels := labels) s v out :=
  .inr o

/-! ## Returns -/

/-- A focused memory action whose operands evaluate (`Ev`). -/
theorem action_reaches {ann : List Annot} {e : ExprNode Codec.wireModel Unit Unit Sym}
    {env : Env} {k : List Frame} {m : Mem.Concrete.State} {op : Prim} {p : PE} {rest : List PE}
    {vs : List Val}
    (h : request file labels ⟨.effectExpr (.mk ann e) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr p env) (.arguments op [] rest env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.arguments op [] rest env :: k))
    (hev : Ev file (tagsOf file m) env (.inr (p :: rest)) (.inr vs)) :
    Reaches file labels ⟨.effectExpr (.mk ann e) env, k, m⟩ ⟨.apply op vs, k, focusMemory ann m⟩ :=
  (Straight.focus_reaches h).trans (by
    have hs := PureEvalExt.args_reaches file _ hev op [] k (focusMemory ann m)
      (Locals.tagsOf_focus ann m) (labels := labels)
    simpa [PureEval.argState] using hs)

theorem killsRun_nil {f : File Codec.wireModel Unit Unit} {ret u : Sym} {e : Eff} {r : IntegerType}
    (h : killsRun f ret u [] e = some r) :
    ∃ (rann : List Annot) (l : Sym) (cann a3 c3 a4 : List Annot) (s u' : Sym),
      e = .mk rann (.run () l [.mk cann () (.call (.sym s) [TyActions.tyVal a3 c3 r, .mk a4 () (.sym u')])]) ∧
      l.key = ret.key ∧ u'.key = u.key ∧ isConvLoaded f s = true ∧ supported r = true := by
  simp only [killsRun] at h
  unfold runRet at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact ⟨_, _, _, _, _, _, _, _, rfl, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
    · cases h
  · cases h

theorem killsRun_cons {f : File Codec.wireModel Unit Unit} {ret u : Sym} {x : Sym × IntegerType}
    {xs : Vars} {e : Eff} {r : IntegerType} (h : killsRun f ret u (x :: xs) e = some r) :
    ∃ (ann pann : List Annot) (ty : BaseType) (kl rest : Eff),
      e = .mk ann (.sseq (.mk pann (.base (none, ty))) kl rest) ∧ killTy x.1 x.2 kl = true ∧
        killsRun f ret u xs rest = some r := by
  simp only [killsRun] at h
  split at h
  · split at h
    · rename_i hk
      exact ⟨_, _, _, _, _, rfl, hk, h⟩
    · cases h
  · cases h

theorem killTy_inv {x : Sym} {ity : IntegerType} {e : Eff} (h : killTy x ity e = true) :
    ∃ (ann : List Annot) (l : Loc) (u : Unit) (c1 a2 : List Annot) (x' : Sym),
      e = .mk ann (.action (.mk .pos (.mk l u (.kill (.static (tyType c1 ity))
        (.mk a2 () (.sym x')))))) ∧ x'.key = x.key := by
  unfold killTy at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hx, rfl⟩ := h
    exact ⟨_, _, _, _, _, _, rfl, hx⟩
  · cases h

/-- **The kills, then the jump to the return label**, halt with the converted value. -/
theorem killsRun_halts {ret u : Sym} (hret : ReturnLabel labels ret) :
    (xs : Vars) → (ls : List Local) → Keys ls xs → (xs.map (·.1.key)).Nodup →
    {e : Eff} → {r : IntegerType} → killsRun file ret u xs e = some r → (env : Env) →
    {k : List Frame} → NoBoundary k → (m : Mem.Concrete.State) →
    (∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)) →
    (∀ l ∈ ls, supported l.ity = true ∧ LiveSz m l.id l.addr (width l.ity)) →
    (∀ a ∈ ls, ∀ b ∈ ls, a.sym.key ≠ b.sym.key → a.id ≠ b.id) →
    {v : Int} → env.lookup u = some (spec v) →
    ∃ m', m'.stdout = m.stdout ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.halt (.defined (spec (cv r v))), [], m'⟩
  | [], ls, hls, _, e, r, h, env, k, hk, m, _, _, _, v, hu => by
    obtain ⟨rann, l, cann, a3, c3, a4, s, u', rfl, hl, hu', hs, hr⟩ := killsRun_nil h
    have heval : Ev file (tagsOf file (focusMemory rann m)) env
        (.inl (.mk cann () (.call (.sym s) [TyActions.tyVal a3 c3 r, .mk a4 () (.sym u')])))
        (.inl (spec (cv r v))) :=
      TyConv.convLoaded_ev (ann := c3) hs hr
        (.cons .val (.cons (.sym (by rw [ReturnLit.lookup_key hu']; exact hu)) .nil))
    obtain ⟨m', out, halts⟩ := ReturnLit.jump_halts hl hret (spec (cv r v)) env hk (focusMemory rann m)
    refine ⟨m', by simp [out], ?_⟩
    refine (Straight.focus_reaches (m := m) Straight.request_run).trans ?_
    exact (PureEvalExt.ev_reaches file _ heval _ _ rfl).trans halts
  | x :: xs, ls, hls, nodup, e, r, h, env, k, hk, m, henv, hlive, hids, v, hu => by
    cases ls with
    | nil => cases hls
    | cons l ls =>
      simp only [Keys, List.map_cons, List.cons.injEq, Prod.mk.injEq] at hls
      obtain ⟨⟨hxl, hxt⟩, hls⟩ := hls
      obtain ⟨hxs, nodup⟩ := List.nodup_cons.mp nodup
      obtain ⟨ann, pann, ty, kl, rest, rfl, hkl, hrest⟩ := killsRun_cons h
      obtain ⟨kann, loc, uu, c1, a2, x', rfl, hx'k⟩ := killTy_inv hkl
      have hx' : env.lookup x' = some (ptr l) :=
        henv l (by simp) x' (hx'k.trans hxl.symm)
      obtain ⟨hsl, livel⟩ := hlive l (by simp)
      rw [← hxt]
      have kill := TyActions.kill_reaches (file := file) (labels := labels) kann a2 c1 loc uu x' hsl env
        (.strongBind (.mk pann (.base (none, ty))) rest env :: k) m hx' livel
      let m₁ := Locals.killed (focusMemory kann m) l.id
      have hls' : Keys ls xs := hls
      have ne : ∀ l' ∈ ls, l'.id ≠ l.id := by
        intro l' hl'
        refine (hids l' (by simp [hl']) l (by simp) ?_)
        intro e
        apply hxs
        have hm : l'.sym.key ∈ ls.map (·.sym.key) := List.mem_map_of_mem hl'
        rw [hls'.keys, e, hxl] at hm
        exact hm
      obtain ⟨m', out, reach⟩ := killsRun_halts hret xs ls hls' nodup hrest env hk m₁
        (fun l' hl' => henv l' (by simp [hl']))
        (fun l' hl' => ⟨(hlive l' (by simp [hl'])).1, TyActions.live_killed
          (TyActions.liveSz_focus kann (hlive l' (by simp [hl'])).2) l.id (ne l' hl')⟩)
        (fun a ha b hb => hids a (by simp [ha]) b (by simp [hb])) hu
      refine ⟨m', by rw [out]; simp [m₁, Locals.killed], ?_⟩
      exact (ReturnConst.sequence_reaches file labels ann _ _ rest env k m).trans (kill.trans
        ((ReturnConst.wildcard_sequence_reaches file labels pann ty .unit rest env k m₁).trans reach))

theorem retStmt_inv {f : File Codec.wireModel Unit Unit} {ret : Sym} {xs : Vars} {e : Eff}
    {t : Term} (h : retStmt f ret xs e = some t) :
    ∃ (ann pann : List Annot) (u : Sym) (ty : BaseType) (bann : List Annot) (e' kr : Eff)
      (r : IntegerType) (te : Term),
      e = .mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) kr) ∧
      isFresh xs u = true ∧ killsRun f ret u xs kr = some r ∧ term f e' = some te ∧
      t = convT r te := by
  unfold retStmt at h
  split at h
  · split at h
    · rename_i hf
      split at h
      · rename_i r te hk he
        cases h
        exact ⟨_, _, _, _, _, _, _, _, _, rfl, hf, hk, he, rfl⟩
      · cases h
    · cases h
  · cases h

theorem killsRun_supported {f : File Codec.wireModel Unit Unit} {ret u : Sym} :
    (xs : Vars) → {e : Eff} → {r : IntegerType} → killsRun f ret u xs e = some r → supported r = true
  | [], _, _, h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hr⟩ := killsRun_nil h
    exact hr
  | _ :: xs, _, _, h => by
    obtain ⟨_, _, _, _, _, _, _, hrest⟩ := killsRun_cons h
    exact killsRun_supported xs hrest

/-- **`return e;`** shows the value of the closed term, or undefined behaviour. -/
theorem ret_halts {ret : Sym} (hret : ReturnLabel labels ret) {xs : Vars} {e : Eff} {t : Term}
    (h : retStmt file ret xs e = some t) {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option Term} (inv : Inv env m ls ds) (hls : Keys ls xs)
    (nodup : (xs.map (·.1.key)).Nodup) (hd : Defined ds t = true) (ht : typedIn xs t = true)
    {k : List Frame} (hk : NoBoundary k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩
      ((close (defsOf ds) t).val zero) m.stdout := by
  obtain ⟨ann, pann, u, ty, bann, e', kr, r, te, rfl, hfresh, hkr, he, rfl⟩ := retStmt_inv h
  have hr := killsRun_supported xs hkr
  let σ := values (defsOf ds)
  let K := Frame.strongBind (.mk pann (.base (some u, ty))) kr env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) kr)) env,
        k, m⟩ ⟨.effectExpr e' env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
      (ReturnLit.bound_reaches bann _ env _ m)
  refine Shows.pre pre ?_
  have hd' : Defined ds te = true := by
    simpa [Defined, convT, Term.vars] using hd
  have ht' : typedIn xs te = true := by
    simpa [typedIn, convT, Term.vars] using ht
  have locs := inv.locs hd' (hls.typed ht')
  by_cases ok : te.Ok σ
  · left
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := TyExpr.term_runs (file := file) (labels := labels)
      te he ok (.bound :: K) m locs
    let v := spec (te.val σ)
    have inv₁ := (inv.touched tch).extend (x := u) (v := v) (hls.fresh hfresh)
    obtain ⟨m', out, reach⟩ := killsRun_halts hret xs ls hls nodup hkr (extendEnv [(u, v)] env) hk m₁
      inv₁.env inv₁.live (fun a ha b hb ne => (inv₁.apart a ha b hb ne).1) (ConvInt.lookup_one rfl)
    refine ⟨m', by rw [out, tch.stdout], ?_⟩
    rw [close_convT, convT_val hr, TyExpr.close_val]
    exact (Interleave.reaches_of_local file labels run).trans ((bound_pop hfr v K m₁).trans
      ((ReturnLit.bind_reaches pann u ty v kr env k m₁).trans reach))
  · right
    exact fails_overflows (TyExpr.term_fails (file := file) (labels := labels) te he ok
      (.bound :: K) m locs)

/-! ## Assignments -/

theorem term_sym_none (file' : File Codec.wireModel Unit Unit) (an pa : List Annot) (x : Sym) :
    term file' (.mk an (.pure (.mk pa () (.sym x)))) = none := by
  unfold term; rfl

/-- The resumption of an assignment: its weak bind, then `pure(conv_loaded_int(T, t))`. -/
theorem assign_resume (b1 : List Annot) (ty1 : BaseType) (an an₁ a1 c1 a3 : List Annot)
    (s t' : Sym) (env₁ : Env) (xs : List Access) (n : Nat) (m : Mem.Concrete.State) {ity : IntegerType}
    (hity : supported ity = true) {v : Int}
    (hs : isConvLoaded file s = true) (ht : env₁.lookup t' = some (spec v)) :
    ∃ m', Touched m m' ∧ TaskRuns file labels false
      ⟨.value .unit, excludeFrames n [.effectBind (.mk b1 (.base (none, ty1)))
        (.mk an (.pure (.mk an₁ () (.call (.sym s) [TyActions.tyVal a1 c1 ity, .mk a3 () (.sym t')])))) env₁,
        .annotations xs], m⟩
      (spec (cv ity v)) (xs.map fun x => {x with exclusions := n :: x.exclusions}) m' := by
  let CALL : PE := .mk an₁ () (.call (.sym s) [TyActions.tyVal a1 c1 ity, .mk a3 () (.sym t')])
  let ys := xs.map fun x => {x with exclusions := n :: x.exclusions}
  have hex : excludeFrames n [.effectBind (.mk b1 (.base (none, ty1))) (.mk an (.pure CALL)) env₁,
      .annotations xs] = [.effectBind (.mk b1 (.base (none, ty1))) (.mk an (.pure CALL)) env₁,
      .annotations ys] := rfl
  rw [hex]
  have s₁ : LocalReaches file labels false
      ⟨.value .unit, [.effectBind (.mk b1 (.base (none, ty1))) (.mk an (.pure CALL)) env₁,
        .annotations ys], m⟩
      ⟨.effectExpr (.mk an (.pure CALL)) env₁, [.annotations ys], m⟩ :=
    .single (.next (by simp [requestAux, awaitsScheduling, matchPattern, extendEnv])
      (LoadTask.plain_effectExpr _ _))
  obtain ⟨l, hr⟩ := LoadTask.requestAux_pure (file := file) (labels := labels) m an CALL env₁
    [.annotations ys] false
  obtain ⟨l', s₂⟩ := LoadTask.focus_local (LoadTask.plain_pureExpr CALL env₁) (by simpa using hr)
  let m₄ : Mem.Concrete.State := {m with currentLocation := l'}
  have heval : Ev file (tagsOf file m₄) env₁ (.inl CALL) (.inl (spec (cv ity v))) :=
    TyConv.convLoaded_ev (ann := c1) hs hity (.cons .val (.cons (.sym ht) .nil))
  have s₃ := PureEvalExt.ev_local file (tagsOf file m₄) (wc := false) (labels := labels) heval
    (.diagnosticLocation m.currentLocation :: [.annotations ys]) m₄ rfl
  refine ⟨m₄, ⟨l', m.lastUsed, rfl⟩, [.annotations ys], s₁.trans (s₂.trans (s₃.tail ?_)), ?_⟩
  · exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
      (LoadTask.plain_value _)
  · simp [annotationsOnly, ys]

theorem assignStmt_inv {f : File Codec.wireModel Unit Unit} {e : Eff} {x : Sym} {ity : IntegerType}
    {t : Term} (h : assignStmt f e = some (x, ity, t)) :
    ∃ (a0 a1 : List Annot) (ty0 : BaseType) (a2 a3 a4 a5 : List Annot) (p : Sym) (tp : BaseType)
      (a6 : List Annot) (t₀ : Sym) (tt : BaseType) (a7 a8 a9 : List Annot) (e' : Eff)
      (b0 b1 : List Annot) (ty1 : BaseType) (sann : List Annot) (l : Loc) (u : Unit)
      (b2 c1 b3 : List Annot) (p' : Sym) (b4 : List Annot) (s : Sym) (b5 c2 b6 : List Annot)
      (t' : Sym) (b7 b8 : List Annot) (s' : Sym) (b9 c3 d0 : List Annot) (t'' : Sym)
      (d1 d2 : List Annot),
      e = .mk a0 (.sseq (.mk a1 (.base (none, ty0)))
        (.mk a2 (.bound (.mk a3 (.wseq
          (.mk a4 (.ctor .tuple [.mk a5 (.base (some p, tp)), .mk a6 (.base (some t₀, tt))]))
          (.mk a7 (.unseq [.mk a8 (.pure (.mk a9 () (.sym x))), e']))
          (.mk b0 (.wseq (.mk b1 (.base (none, ty1)))
            (.mk sann (.action (.mk .neg (.mk l u (.store false (TyActions.tyVal b2 c1 ity)
              (.mk b3 () (.sym p'))
              (.mk b4 () (.call (.sym s) [TyActions.tyVal b5 c2 ity, .mk b6 () (.sym t')])) .na)))))
            (.mk b7 (.pure (.mk b8 () (.call (.sym s') [TyActions.tyVal b9 c3 ity,
              .mk d0 () (.sym t'')]))))))))))
        (.mk d1 (.pure (.mk d2 () (.val .unit))))) ∧
      p'.key = p.key ∧ t'.key = t₀.key ∧ t''.key = t₀.key ∧ t₀.key ≠ p.key ∧ noLoc sann = true ∧
      isConvLoaded f s = true ∧ isConvLoaded f s' = true ∧ supported ity = true ∧
      term f e' = some t := by
  unfold assignStmt at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨te, ht, rfl, rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, rfl, rfl, h10⟩ := hc
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, h1, h2, h3, h4, h5, h6, h7, h10, ht⟩
    · cases h
  · cases h

/-- `m'` keeps `m`'s allocation state: the last address, the next identifier and the dead
allocations (what a later `create` depends on). -/
def SameAlloc (m m' : Mem.Concrete.State) : Prop :=
  m'.lastAddress = m.lastAddress ∧ m'.nextId = m.nextId ∧ m'.dead = m.dead

theorem SameAlloc.refl (m : Mem.Concrete.State) : SameAlloc m m := ⟨rfl, rfl, rfl⟩

theorem SameAlloc.trans {m₁ m₂ m₃ : Mem.Concrete.State} (a : SameAlloc m₁ m₂) (b : SameAlloc m₂ m₃) :
    SameAlloc m₁ m₃ :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.trans a.2.2⟩

theorem sameAlloc_touched {m m' : Mem.Concrete.State} (h : Touched m m') : SameAlloc m m' := by
  obtain ⟨l, u, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

theorem sameAlloc_focus (ann : List Annot) (m : Mem.Concrete.State) :
    SameAlloc m (focusMemory ann m) := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]
  exact ⟨rfl, rfl, rfl⟩

theorem sameAlloc_stored (m : Mem.Concrete.State) (id addr : Int) (w : Nat) (n : Int) :
    SameAlloc m (stored m id addr w n) := by
  obtain ⟨b, pb, h⟩ := Mem.Concrete.writeRepresentation_shape addr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger w n)) m
  refine ⟨?_, ?_, ?_⟩ <;> simp [stored, h]

theorem sameAlloc_unstored (m : Mem.Concrete.State) (id addr : Int) (w : Nat) :
    SameAlloc m (TyMem.unstored m id addr w) := by
  obtain ⟨b, pb, h⟩ := Mem.Concrete.writeRepresentation_shape addr
    (Mem.Concrete.plainBytes (List.replicate w none)) m
  refine ⟨?_, ?_, ?_⟩ <;> simp [TyMem.unstored, h]

theorem sameAlloc_nextExcluded (m : Mem.Concrete.State) (n : Nat) :
    SameAlloc m {m with nextExcluded := n} := ⟨rfl, rfl, rfl⟩

/-- **`x = e;`**: undefined behaviour, or `x` holds the converted closed term of `e`. -/
theorem assign_runs {e : Eff} {x : Sym} {ity : IntegerType} {t : Term}
    (h : assignStmt file e = some (x, ity, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key) (hty : l.ity = ity)
    (hd : Defined ds t = true) (ht : Typed ls t) (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      ∃ m', m'.stdout = m.stdout ∧ SameAlloc m m' ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) (convT ity t)))) ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  obtain ⟨a0, a1, ty0, a2, a3, a4, a5, p, tp, a6, t₀, tt, a7, a8, a9, e', b0, b1, ty1, sann, lc, u,
    b2, c1, b3, p', b4, s, b5, c2, b6, t', b7, b8, s', b9, c3, d0, t'', d1, d2, rfl, hp', ht', ht'',
    htp, hann, hs, hs', hity, he⟩ := assignStmt_inv h
  subst hty
  let σ := values (defsOf ds)
  let PU : EE := .mk d1 (.pure (.mk d2 () (.val .unit)))
  let K0 := Frame.strongBind (.mk a1 (.base (none, ty0))) PU env :: k
  let PAT : Pattern Sym := .mk a4 (.ctor .tuple [.mk a5 (.base (some p, tp)), .mk a6 (.base (some t₀, tt))])
  let CONV : PE := .mk b8 () (.call (.sym s') [TyActions.tyVal b9 c3 l.ity, .mk d0 () (.sym t'')])
  let NEG : EE := .mk sann (.action (.mk .neg (.mk lc u (.store false (TyActions.tyVal b2 c1 l.ity)
    (.mk b3 () (.sym p')) (.mk b4 () (.call (.sym s) [TyActions.tyVal b5 c2 l.ity,
      .mk b6 () (.sym t')])) .na))))
  let BODY : EE := .mk b0 (.wseq (.mk b1 (.base (none, ty1))) NEG (.mk b7 (.pure CONV)))
  let PX : EE := .mk a8 (.pure (.mk a9 () (.sym x)))
  let KB := Frame.effectBind PAT BODY env :: .bound :: K0
  have pre : Reaches file labels ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (none, ty0)))
      (.mk a2 (.bound (.mk a3 (.wseq PAT (.mk a7 (.unseq [PX, e'])) BODY)))) PU)) env, k, m⟩
      ⟨.effectExpr (.mk a7 (.unseq [PX, e'])) env, KB, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      ((ReturnLit.bound_reaches a2 _ env _ m).trans (Locals.wseq_reaches a3 PAT _ BODY env _ m))
  have locs := inv.locs hd ht
  have hpx : env.lookup x = some (ptr l) := inv.lookup hl hx
  by_cases ok : t.Ok σ
  · right
    let I : Mem.Concrete.State → Prop := fun m => TyExpr.Locs env m σ t
    have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t => s.touched t
    obtain ⟨xs, m₁, -, tch, s₂⟩ := IntExpr.unseq_pair (file := file) (labels := labels) (k := KB)
      (annots := a7) I hI (sym_readTask I env a8 a9 x hpx)
      (TyExpr.term_task t he ok I fun _ hm => hm)
      (by intro eq; rw [← eq, term_sym_none] at he; cases he) m locs
    let v := t.val σ
    let env₁ := extendEnv [(p, ptr l), (t₀, spec v)] env
    have s₃ : Reaches file labels ⟨.value (.tuple [ptr l, spec v]), .annotations xs :: KB, m₁⟩
        ⟨.effectExpr BODY env₁, .annotations xs :: .bound :: K0, m₁⟩ :=
      Interleave.reaches_of_local file labels (.single (.next
        (IntExpr.requestAux_tuple_bind m₁ xs a4 a5 a6 p t₀ tp tt _ _ _ env _)
        (LoadTask.plain_effectExpr _ _)))
    let inner := [Frame.effectBind (.mk b1 (.base (none, ty1))) (.mk b7 (.pure CONV)) env₁,
      .annotations xs]
    have s₄ : Reaches file labels ⟨.effectExpr BODY env₁, .annotations xs :: .bound :: K0, m₁⟩
        ⟨.effectExpr NEG env₁, inner ++ .bound :: K0, m₁⟩ :=
      Locals.wseq_reaches b0 _ NEG _ env₁ _ m₁
    have ht₁ : env₁.lookup t'' = some (spec v) := lookup_two_snd ht'' htp
    obtain ⟨m₂, tch₂, resume⟩ := assign_resume (file := file) (labels := labels) b1 ty1 b7 b8 b9 c3 d0
      s' t'' env₁ xs m₁.nextExcluded {m₁ with nextExcluded := m₁.nextExcluded + 1} hity hs' ht₁
    have inv₁ : Inv env m₁ ls ds := inv.touched tch
    have live₁ := (inv₁.live l hl).2
    have s₅ := TyMem.lifted_store (file := file) (labels := labels) sann hann lc u
      (TyActions.tyVal b2 c1 l.ity) (.mk b3 () (.sym p'))
      (.mk b4 () (.call (.sym s) [TyActions.tyVal b5 c2 l.ity, .mk b6 () (.sym t')]))
      env₁ inner K0 m₁ c1 hity live₁ (TyConv.cv_fits hity v)
      (fun m' => .cons (TyActions.eval_tyVal _ env₁ b2 c1 l.ity |> PureEvalExt.Ev.of_eval file _)
        (.cons (.sym (lookup_two_fst hp'))
        (.cons (TyConv.convLoaded_ev (ann := c2) hs hity
          (.cons .val (.cons (.sym (lookup_two_snd ht' htp)) .nil))) .nil)))
      (by simp [inner, List.span, List.span.loop]) resume tch₂
      (by intro a ha; obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha; simp)
      (by simp [activeCall, excludeFrames, inner])
    let D := close (defsOf ds) (convT l.ity t)
    have hDv : D.val zero = cv l.ity v := by
      simp only [D, close_convT, convT_val hity, TyExpr.close_val]; rfl
    let m₃ := stored m₂ l.id l.addr (width l.ity) (cv l.ity v)
    have inv₃ : Inv env m₃ ls (update ds l.sym.key (some D)) := by
      have i₂ : Inv env m₂ ls ds := (inv₁.nextExcluded _).touched tch₂
      have okD : D.Ok zero := by
        refine ⟨TyExpr.close_ok _ t (inv.defs_ok hd) ok, trivial, trivial⟩
      have := i₂.store hl okD (by rw [hDv]; exact TyConv.cv_fits hity v)
      rwa [hDv] at this
    refine ⟨focusMemory d1 m₃, ?_, ?_, inv₃.focus d1, ?_⟩
    · simp [m₃, TyActions.stored_stdout, tch₂.stdout, tch.stdout]
    · exact (sameAlloc_touched tch).trans ((sameAlloc_nextExcluded m₁ _).trans
        ((sameAlloc_touched tch₂).trans ((sameAlloc_stored m₂ _ _ _ _).trans (sameAlloc_focus d1 m₃))))
    · exact pre.trans ((Interleave.reaches_of_local file labels s₂).trans (s₃.trans (s₄.trans
        (s₅.trans ((ReturnConst.wildcard_sequence_reaches file labels a1 ty0 _ PU env k m₃).trans
          (pure_unit_reaches d1 d2 env k m₃))))))
  · left
    refine StateStmt.Overflows.pre pre (fails_overflows (ArenaFail.fail_pair file labels (.inl ?_)))
    have flag : taskFlag false KB [(0, .effectExpr PX env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, PX, hasCCall]
    rw [flag]
    exact TyExpr.term_fails t he ok [] m locs

/-! ## Initialisations -/

theorem initStmt_inv {f : File Codec.wireModel Unit Unit} {e : Eff} {x : Sym} {ity : IntegerType}
    {t : Term} (h : initStmt f e = some (x, ity, t)) :
    ∃ (a0 a1 : List Annot) (t₀ : Sym) (ty : BaseType) (a2 : List Annot) (e' : Eff)
      (a3 : List Annot) (l : Loc) (u : Unit) (b1 c1 b2 b3 b4 c3 b5 : List Annot) (s t' : Sym),
      e = .mk a0 (.sseq (.mk a1 (.base (some t₀, ty))) (.mk a2 (.bound e'))
        (.mk a3 (.action (.mk .pos (.mk l u (.store false (TyActions.tyVal b1 c1 ity)
          (.mk b2 () (.sym x))
          (.mk b3 () (.call (.sym s) [TyActions.tyVal b4 c3 ity, .mk b5 () (.sym t')])) .na)))))) ∧
      t'.key = t₀.key ∧ t₀.key ≠ x.key ∧ isConvLoaded f s = true ∧ supported ity = true ∧
      term f e' = some t := by
  unfold initStmt at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨te, ht, rfl, rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, rfl, h5⟩ := hc
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, h1, h2, h3, h5, ht⟩
    · cases h
  · cases h

/-- **`T x = e;`**: undefined behaviour, or `x` holds the converted closed term of `e`. -/
theorem init_runs {e : Eff} {x : Sym} {ity : IntegerType} {t : Term}
    (h : initStmt file e = some (x, ity, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key) (hty : l.ity = ity)
    (hd : Defined ds t = true) (ht : Typed ls t) (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      ∃ m' xs, m'.stdout = m.stdout ∧ SameAlloc m m' ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) (convT ity t)))) ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, a1, t₀, ty, a2, e', a3, lc, u, b1, c1, b2, b3, b4, c3, b5, s, t', rfl, ht', htx, hs,
    hity, he⟩ := initStmt_inv h
  subst hty
  let σ := values (defsOf ds)
  let ST : EE := .mk a3 (.action (.mk .pos (.mk lc u (.store false (TyActions.tyVal b1 c1 l.ity)
    (.mk b2 () (.sym x)) (.mk b3 () (.call (.sym s) [TyActions.tyVal b4 c3 l.ity,
      .mk b5 () (.sym t')])) .na))))
  let K := Frame.strongBind (.mk a1 (.base (some t₀, ty))) ST env :: k
  have pre : Reaches file labels ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some t₀, ty)))
      (.mk a2 (.bound e')) ST)) env, k, m⟩ ⟨.effectExpr e' env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  have locs := inv.locs hd ht
  by_cases ok : t.Ok σ
  · right
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := TyExpr.term_runs (file := file) (labels := labels)
      t he ok (.bound :: K) m locs
    let v := t.val σ
    let env₁ := extendEnv [(t₀, spec v)] env
    have inv₁ : Inv env m₁ ls ds := inv.touched tch
    have hx₁ : env₁.lookup x = some (ptr l) := by
      rw [ConvInt.lookup_one_other (fun e => htx e.symm)]; exact inv.lookup hl hx
    have hev : Ev file (tagsOf file m₁) env₁
        (.inr [TyActions.tyVal b1 c1 l.ity, .mk b2 () (.sym x),
          .mk b3 () (.call (.sym s) [TyActions.tyVal b4 c3 l.ity, .mk b5 () (.sym t')])])
        (.inr [.ctype (tyType c1 l.ity), .object (.pointer (.allocated l.id l.addr)),
          .loaded (.specified (.integer (cv l.ity v)))]) :=
      .cons .val (.cons (.sym hx₁) (.cons (TyConv.convLoaded_ev (ann := c3) hs hity
        (.cons .val (.cons (.sym (ConvInt.lookup_one ht')) .nil))) .nil))
    obtain ⟨ys, hst⟩ := TyActions.store_apply (file := file) (labels := labels) c1 hity k
      (TyActions.liveSz_focus a3 (inv₁.live l hl).2) (TyConv.cv_fits hity v)
    let D := close (defsOf ds) (convT l.ity t)
    have hDv : D.val zero = cv l.ity v := by
      simp only [D, close_convT, convT_val hity, TyExpr.close_val]; rfl
    have okD : D.Ok zero := ⟨TyExpr.close_ok _ t (inv.defs_ok hd) ok, trivial, trivial⟩
    have inv₂ := (inv₁.focus a3).store hl okD (by rw [hDv]; exact TyConv.cv_fits hity v)
    rw [hDv] at inv₂
    refine ⟨_, ys, ?_, (sameAlloc_touched tch).trans ((sameAlloc_focus a3 m₁).trans
      (sameAlloc_stored _ _ _ _ _)), inv₂, ?_⟩
    · simp [TyActions.stored_stdout, tch.stdout]
    · exact pre.trans ((Interleave.reaches_of_local file labels run).trans ((bound_pop hfr _ K m₁).trans
        ((ReturnLit.bind_reaches a1 t₀ ty _ ST env k m₁).trans
          ((action_reaches Locals.request_store hev).trans hst))))
  · left
    exact StateStmt.Overflows.pre pre (fails_overflows (TyExpr.term_fails (file := file)
      (labels := labels) t he ok (.bound :: K) m locs))

/-! ## Declarations without initialiser -/

theorem uninitStmt_inv {e : Eff} {x : Sym} {ity : IntegerType} (h : uninitStmt e = some (x, ity)) :
    ∃ (a0 : List Annot) (l : Loc) (u : Unit) (b1 c1 b2 b3 c3 : List Annot),
      e = .mk a0 (.action (.mk .pos (.mk l u (.store false (TyActions.tyVal b1 c1 ity)
        (.mk b2 () (.sym x)) (.mk b3 () (.val (.loaded (.unspecified (tyType c3 ity))))) .na)))) ∧
      supported ity = true := by
  unfold uninitStmt at h
  split at h
  · split at h
    · rename_i hc
      cases h
      obtain ⟨rfl, hs⟩ := hc
      exact ⟨_, _, _, _, _, _, _, _, rfl, hs⟩
    · cases h
  · cases h

/-- **`T x;`**: `x` has no definition. -/
theorem uninit_runs {e : Eff} {x : Sym} {ity : IntegerType} (h : uninitStmt e = some (x, ity))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key) (hty : l.ity = ity)
    (k : List Frame) :
    ∃ m' xs, m'.stdout = m.stdout ∧ SameAlloc m m' ∧ Inv env m' ls (update ds l.sym.key none) ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, lc, u, b1, c1, b2, b3, c3, rfl, hs⟩ := uninitStmt_inv h
  subst hty
  refine ⟨_, _, ?_, (sameAlloc_focus a0 m).trans (sameAlloc_unstored _ _ _ _), (inv.focus a0).uninit hl, TyMem.uninit_reaches (file := file)
    (labels := labels) a0 b1 c1 b2 b3 c3 lc u x hs env k m (inv.lookup hl hx) (inv.live l hl).2⟩
  simp [TyMem.unstored_stdout]

/-! ## Selections -/

theorem ifRet_inv {f : File Codec.wireModel Unit Unit} {ret : Sym} {xs : Vars} {e : Eff}
    {tc ta : Term} (h : ifRet f ret xs e = some (tc, ta)) :
    ∃ (a0 a1 : List Annot) (c : Sym) (cty : BaseType) (a2 : List Annot) (ec : Eff) (a3 a4 : List Annot)
      (b : Sym) (bty : BaseType) (cb : Eff) (a5 a6 : List Annot) (b' : Sym) (ea : Eff)
      (a7 a8 : List Annot),
      e = .mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec))
        (.mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb
          (.mk a5 (.if_ (.mk a6 () (.sym b')) ea (.mk a7 (.pure (.mk a8 () (.val .unit))))))))) ∧
      b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ isFresh xs c = true ∧ isFresh xs b = true ∧
      term f ec = some tc ∧ retStmt f ret xs ea = some ta := by
  unfold ifRet at h
  split at h
  · split at h
    · rename_i hc
      split at h
      · rename_i tc' ta' h₁ h₂
        cases h
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2.1, hc.2.2.1,
          hc.2.2.2, h₁, h₂⟩
      · cases h
    · cases h
  · cases h

/-- **`if (c) return e;`**: undefined behaviour in the test, or the test is not `1` (`c ≠ 0`) and
the statement shows the return of `e`, or the test is `1` and the statement falls through. -/
theorem ifRet_runs {ret : Sym} (hret : ReturnLabel labels ret) {xs : Vars} {e : Eff}
    {tc ta : Term} (h : ifRet file ret xs e = some (tc, ta)) {env : Env} {m : Mem.Concrete.State}
    {ls : List Local} {ds : Key → Option Term} (inv : Inv env m ls ds) (hls : Keys ls xs)
    (nodup : (xs.map (·.1.key)).Nodup) (hdc : Defined ds tc = true) (htc : typedIn xs tc = true)
    (hda : Defined ds ta = true) (hta : typedIn xs ta = true) {k : List Frame} (hk : NoBoundary k) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    (tc.val (values (defsOf ds)) ≠ 1 ∧
      Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩
        ((close (defsOf ds) ta).val zero) m.stdout) ∨
    (tc.val (values (defsOf ds)) = 1 ∧ ∃ m', m'.stdout = m.stdout ∧
      Inv env m' ls ds ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩) := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', ea, a7, a8, rfl, hb', hcb, hfc,
    hfb, htc', hta'⟩ := ifRet_inv h
  let σ := values (defsOf ds)
  let PU : EE := .mk a7 (.pure (.mk a8 () (.val .unit)))
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) ea PU)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  have locs := inv.locs hdc (hls.typed htc)
  by_cases okc : tc.Ok σ
  · right
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := TyExpr.term_runs (file := file) (labels := labels)
      tc htc' okc (.bound :: K) m locs
    let cvl := tc.val σ
    let env₁ := extendEnv [(c, spec cvl)] env
    let KB := Frame.strongBind (.mk a4 (.base (some b, bty))) IF env₁ :: k
    obtain ⟨m₂, tch₂, conv⟩ := boolSource_touched (file := file) (labels := labels) hcb env₁ KB m₁ cvl
      (ConvInt.lookup_one rfl)
    let flag := decide (cvl ≠ 1)
    let env₂ := extendEnv [(b, boolean flag)] env₁
    have hp : SeqReach.PureEval file labels (.mk a6 () (.sym b')) env₂ (boolean flag) :=
      SeqReach.pure_symbol a6 b' env₂ _ (ConvInt.lookup_one hb')
    let m₃ := SeqReach.focusMemory a5 m₂
    have enter : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
        ⟨.effectExpr (if flag then ea else PU) env₂, k, m₃⟩ :=
      (Interleave.reaches_of_local file labels run).trans ((bound_pop hfr _ K m₁).trans
        ((ReturnLit.bind_reaches a1 c cty _ REST env k m₁).trans
          ((ReturnConst.sequence_reaches file labels a3 _ cb IF env₁ k m₁).trans
            (conv.trans ((ReturnLit.bind_reaches a4 b bty _ IF env₁ k m₂).trans
              (SeqReach.effect_if_reaches a5 flag hp k m₂))))))
    have tch₃ : Touched m m₃ := tch.trans (tch₂.trans (seqFocus_touched a5 m₂))
    have inv₃ : Inv env m₃ ls ds := inv.touched tch₃
    by_cases h1 : cvl = 1
    · right
      refine ⟨h1, ReturnConst.focusMemory a7 m₃, by simp [tch₃.stdout],
        inv₃.focus a7, ?_⟩
      have enter' : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
          ⟨.effectExpr PU env₂, k, m₃⟩ := by simpa [flag, h1] using enter
      exact pre.trans (enter'.trans (pure_unit_reaches a7 a8 env₂ k m₃))
    · left
      refine ⟨h1, ?_⟩
      have enter' : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
          ⟨.effectExpr ea env₂, k, m₃⟩ := by simpa [flag, h1] using enter
      have inv₂ : Inv env₂ m₃ ls ds := (inv₃.extend (hls.fresh hfc)).extend (hls.fresh hfb)
      have o := ret_halts hret hta' inv₂ hls nodup hda hta hk
      rw [tch₃.stdout] at o
      exact Shows.pre (pre.trans enter') o
  · left
    exact StateStmt.Overflows.pre pre (fails_overflows (TyExpr.term_fails (file := file)
      (labels := labels) tc htc' okc (.bound :: K) m locs))

end Silmaril.Compile.Core.Verified.TyStmt
