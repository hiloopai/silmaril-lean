module

public import Silmaril.Compiler.Core.Verified.TyState.Defs
public import Silmaril.Compiler.Core.Verified.GlobalsState.Defs
/-! # Startup with globals of every supported integer type, as typed slots

`GlobalsState` for globals of every supported integer type (`TyActions.supported`). A global
definition `T x = n;` (and the tentative `T x;`, `n = 0`) is
`let strong a = create(Ivalignof(T), T) in let strong t = bound(e) in
store(T, a, conv_loaded_int(T, t)) ; pure(a)`, `e` a closed expression folding to `n`
(`initTy`, `TyExpr.fold`): it allocates a `T` object below the
earlier ones and stores `cv T n` in it (`initTy_reaches`). The definitions run in order
(`globals_placed`), then the `errno` startup allocates below them; every global keeps its
object (`Held`: its slot, an id already allocated, an address at or above the last allocation).

`initial_reaches_state`: the dynamics reaches `main`'s body with the globals as `TyMem` slots
(`Inv`, each defined by its converted literal, `defs`, and `Fresh`), under one annotation frame,
with empty stdout.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyGlobals

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches tagsOf)
open Silmaril.Cerberus.Core.PureEvalExt (Ev)
open Mem.Concrete (LiveSz nextAddress nextIntAddress tyType)
open ReturnLit (Eff)
open ReturnConst (focusMemory)
open TyActions (supported width Fits TSlot created stored tyVal)
open TyConv (cv isConvLoaded)
open TyExpr (Key Term zero)
open TyStmt (convT)
open TyMem (Local ptr Inv Fresh)
open Globals (AnnOnly annOnly_cons definitions)
open LoadTask (Touched)
open StateStmt (bound_pop)

variable {file : Program} {labels : Labels}

/-! ## Objects above the next allocation -/

/-- A global's object: its typed slot, an id already allocated, and an address at or above the
last allocation. -/
structure Held (m : Mem.Concrete.State) (id addr : Int) (w : Nat) (n : Int) : Prop where
  slot : TSlot m id addr w n
  below : id < m.nextId
  above : m.lastAddress ≤ addr

theorem held_touched {m m' : Mem.Concrete.State} {id addr n : Int} {w : Nat} (t : Touched m m')
    (h : Held m id addr w n) : Held m' id addr w n := by
  obtain ⟨l, u, rfl⟩ := t
  exact ⟨TyActions.Touched.slot ⟨l, u, rfl⟩ h.slot, h.below, h.above⟩

theorem held_focus {m : Mem.Concrete.State} {id addr n : Int} {w : Nat} (ann : List Annot)
    (h : Held m id addr w n) : Held (focusMemory ann m) id addr w n :=
  held_touched (LoadTask.focusMemory_touched ann m) h

/-- Creating an object keeps the objects above it. -/
theorem held_created {m : Mem.Concrete.State} {id addr n : Int} {w : Nat} (pref : Prefix)
    (ann : List Annot) {ity : IntegerType} (hs : supported ity = true) (h : Held m id addr w n) :
    Held (created pref ann ity m) id addr w n := by
  have hle := TyActions.nextAddress_le m (TyActions.width_pos hs)
  have hb := h.below
  have ha := h.above
  refine ⟨TyActions.slot_created h.slot pref ann ity (by omega) (.inl (by omega)), ?_, ?_⟩
  · rw [TyActions.created_nextId]; omega
  · rw [TyActions.created_lastAddress]; omega

/-- What a store keeps. -/
theorem stored_same (m : Mem.Concrete.State) (id addr : Int) (w : Nat) (n : Int) :
    (stored m id addr w n).nextId = m.nextId ∧ (stored m id addr w n).lastAddress = m.lastAddress ∧
      (stored m id addr w n).dead = m.dead := by
  obtain ⟨b, pb, h⟩ := Mem.Concrete.writeRepresentation_shape addr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger w n)) m
  refine ⟨?_, ?_, ?_⟩ <;> simp [stored, h]

/-- A store into an object below keeps the objects above it. -/
theorem held_stored {m : Mem.Concrete.State} {id addr n : Int} {v : Nat} (j a : Int) (w : Nat)
    (x : Int) (ha : a + w ≤ addr) (h : Held m id addr v n) : Held (stored m j a w x) id addr v n := by
  obtain ⟨sn, sl, -⟩ := stored_same m j a w x
  exact ⟨TyActions.slot_stored h.slot j a w x (.inl ha), by rw [sn]; exact h.below,
    by rw [sl]; exact h.above⟩

/-! ## One global definition -/

/-- `let strong a = create(Ivalignof(T), T) in let strong t = bound(pure(n)) in
store(T, a, conv_loaded_int(T, t)) ; pure(a)`: a `T` global initialised by `n`; its type and
the term `convT T n` of its stored value `cv T n` (a term, so that nothing is converted at compile
time). -/
def initTy (file : File Codec.wireModel Unit Unit) : Eff → Option (IntegerType × Term)
  | .mk _ (.sseq (.mk _ (.base (some a, _))) cr
      (.mk _ (.sseq (.mk _ (.base (some t, _))) (.mk _ (.bound ei))
        (.mk _ (.sseq (.mk _ (.base (none, _)))
          (.mk _ (.action (.mk .pos (.mk _ _ (.store false
            (.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity))))))
            (.mk _ () (.sym a'))
            (.mk _ () (.call (.sym s) [.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity₂))))),
              .mk _ () (.sym t')])) .na)))))
          (.mk _ (.pure (.mk _ () (.sym a''))))))))) =>
      match TyExpr.fold file ei with
      | some n =>
        if TyState.createTy cr = some ity ∧ ity₂ = ity ∧ a'.key = a.key ∧ a''.key = a.key ∧
            t'.key = t.key ∧ t.key ≠ a.key ∧ isConvLoaded file s = true then some (ity, convT ity (.lit n))
        else none
      | none => none
  | _ => none

theorem initTy_inv {f : File Codec.wireModel Unit Unit} {e : Eff} {ity : IntegerType} {v : Term}
    (h : initTy f e = some (ity, v)) :
    ∃ (ann pann : List Annot) (a : Sym) (ty : BaseType) (cr : Eff) (sann tpann : List Annot) (t : Sym)
      (tty : BaseType) (bann : List Annot) (ei : Eff) (n : Int) (cann upann : List Annot)
      (uty : BaseType) (stann : List Annot) (l : Loc) (u : Unit) (a1 c1 a2 : List Annot) (a' : Sym)
      (a3 : List Annot) (s : Sym) (a4 c3 a5 : List Annot) (t' : Sym) (rann pann'' : List Annot)
      (a'' : Sym),
      e = .mk ann (.sseq (.mk pann (.base (some a, ty))) cr
        (.mk sann (.sseq (.mk tpann (.base (some t, tty))) (.mk bann (.bound ei))
          (.mk cann (.sseq (.mk upann (.base (none, uty)))
            (.mk stann (.action (.mk .pos (.mk l u (.store false (tyVal a1 c1 ity)
              (.mk a2 () (.sym a'))
              (.mk a3 () (.call (.sym s) [tyVal a4 c3 ity, .mk a5 () (.sym t')])) .na)))))
            (.mk rann (.pure (.mk pann'' () (.sym a''))))))))) ∧
      TyExpr.fold f ei = some n ∧
      TyState.createTy cr = some ity ∧ a'.key = a.key ∧ a''.key = a.key ∧ t'.key = t.key ∧
      t.key ≠ a.key ∧ isConvLoaded f s = true ∧ v = convT ity (.lit n) := by
  unfold initTy at h
  split at h
  · split at h
    · rename_i n hn
      split at h
      · rename_i hc
        obtain ⟨hcr, rfl, ha', ha'', ht', hta, hs⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, rfl, hn, hcr, ha', ha'', ht', hta, hs, rfl⟩
      · cases h
    · cases h
  · cases h

/-- A recognised initialiser returns a fresh `T` object holding its value, below every earlier
object, and leaves its store's annotation frame. -/
theorem initTy_reaches {e : Eff} {ity : IntegerType} {v : Term} (h : initTy file e = some (ity, v))
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (hpos : 0 < nextAddress m (width ity))
    (hdead : m.nextId ∉ m.dead) :
    supported ity = true ∧ v.Ok zero ∧ Fits ity (v.val zero) ∧ ∃ m' xs, m'.stdout = m.stdout ∧
      m'.nextId = m.nextId + 1 ∧
      m'.lastAddress = nextAddress m (width ity) ∧ m'.dead = m.dead ∧
      Held m' m.nextId (nextAddress m (width ity)) (width ity) (v.val zero) ∧
      (∀ id addr w x, Held m id addr w x → Held m' id addr w x) ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.value (.object (.pointer (.allocated m.nextId (nextAddress m (width ity))))),
          .annotations xs :: k, m'⟩ := by
  obtain ⟨ann, pann, a, ty, cr, sann, tpann, t, tty, bann, ei, n, cann, upann, uty, stann,
    l, u, a1, c1, a2, a', a3, s, a4, c3, a5, t', rann, pann'', a'', rfl, hfold, hcr, ha', ha'', ht',
    hta, hs, rfl⟩ := initTy_inv h
  obtain ⟨cann0, lc, u0, b1, b2, d1, b3, d2, pref, rfl, hsup⟩ := TyState.createTy_inv hcr
  have hv : (convT ity (.lit n)).val zero = cv ity n := by
    rw [TyStmt.convT_val hsup]; rfl
  rw [hv]
  refine ⟨hsup, ⟨trivial, trivial, trivial⟩, TyConv.cv_fits hsup n, ?_⟩
  let ad := nextAddress m (width ity)
  let pt : Val := .object (.pointer (.allocated m.nextId ad))
  let vl : Val := .loaded (.specified (.integer n))
  let PA : EE := .mk rann (.pure (.mk pann'' () (.sym a'')))
  let ST : EE := .mk stann (.action (.mk .pos (.mk l u (.store false (tyVal a1 c1 ity)
    (.mk a2 () (.sym a')) (.mk a3 () (.call (.sym s) [tyVal a4 c3 ity, .mk a5 () (.sym t')])) .na))))
  let C : EE := .mk cann (.sseq (.mk upann (.base (none, uty))) ST PA)
  let B : EE := .mk sann (.sseq (.mk tpann (.base (some t, tty))) (.mk bann (.bound ei)) C)
  have hcreate := TyActions.create_reaches (file := file) (labels := labels) cann0 b1 b2 b3 d1 d2 lc u0
    pref hsup env (.strongBind (.mk pann (.base (some a, ty))) B env :: k) m hpos
  let m₁ := created pref d2 ity (focusMemory cann0 m)
  have nfocus : (focusMemory cann0 m).nextId = m.nextId := TyActions.focus_nextId cann0 m
  have afocus : nextAddress (focusMemory cann0 m) (width ity) = ad := TyActions.nextAddress_focus cann0 m _
  have live₁ : LiveSz m₁ m.nextId ad (width ity) := by
    have := TyActions.created_live pref d2 ity (focusMemory cann0 m)
      (by rw [TyActions.focus_dead, nfocus]; exact hdead)
    rwa [afocus, nfocus] at this
  let env₁ := extendEnv [(a, pt)] env
  let env₂ := extendEnv [(t, vl)] env₁
  let KB := Frame.strongBind (.mk tpann (.base (some t, tty))) C env₁ :: k
  obtain ⟨li, fri, hfri, runi⟩ := ClosedEff.value_local file labels ei (Fold.EnvSub.empty env₁)
    (TyExpr.fold_inv hfold) (.bound :: KB) m₁
  let m₂ := {m₁ with currentLocation := li}
  have hx₂ : env₂.lookup a' = some pt := by
    rw [ConvInt.lookup_one_other (by rw [ha']; exact fun e => hta e.symm)]
    exact ConvInt.lookup_one ha'
  have ht₂ : env₂.lookup t' = some vl := ConvInt.lookup_one ht'
  have live₂ : LiveSz (focusMemory stann m₂) m.nextId ad (width ity) :=
    TyActions.liveSz_focus stann (TyActions.Touched.live ⟨li, m₁.lastUsed, rfl⟩ live₁)
  have hev : Ev file (tagsOf file m₂) env₂
      (.inr [tyVal a1 c1 ity, .mk a2 () (.sym a'),
        .mk a3 () (.call (.sym s) [tyVal a4 c3 ity, .mk a5 () (.sym t')])])
      (.inr [.ctype (tyType c1 ity), pt, .loaded (.specified (.integer (cv ity n)))]) :=
    .cons .val (.cons (.sym hx₂) (.cons (TyConv.convLoaded_ev (ann := c3) hs hsup
      (.cons .val (.cons (.sym ht₂) .nil))) .nil))
  obtain ⟨xs, hst⟩ := TyActions.store_apply (file := file) (labels := labels) c1 hsup
    (.strongBind (.mk upann (.base (none, uty))) PA env₂ :: k) live₂ (TyConv.cv_fits hsup n)
  let m₃ := stored (focusMemory stann m₂) m.nextId ad (width ity) (cv ity n)
  have hpa : env₂.lookup a'' = some pt := by
    rw [ConvInt.lookup_one_other (by rw [ha'']; exact fun e => hta e.symm)]
    exact ConvInt.lookup_one ha''
  obtain ⟨l', hpure⟩ := LoadTask.pure_sym_local (file := file) (labels := labels) (wc := false)
    rann pann'' a'' env₂ hpa (.annotations xs :: k) m₃
  obtain ⟨sn₃, sl₃, sd₃⟩ := stored_same (focusMemory stann m₂) m.nextId ad (width ity) (cv ity n)
  have hw := TyActions.width_pos hsup
  have hle := TyActions.nextAddress_le m hw
  have n₁ : m₁.nextId = m.nextId + 1 := by rw [TyActions.created_nextId, nfocus]
  have l₁ : m₁.lastAddress = ad := by rw [TyActions.created_lastAddress, afocus]
  have d₁ : m₁.dead = m.dead := by rw [TyActions.created_dead, TyActions.focus_dead]
  refine ⟨{m₃ with currentLocation := l'}, xs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change m₃.stdout = m.stdout
    simp [m₃, m₂, m₁, TyActions.stored_stdout, TyActions.created_stdout]
  · change m₃.nextId = m.nextId + 1
    rw [sn₃, TyActions.focus_nextId]; exact n₁
  · change m₃.lastAddress = ad
    rw [sl₃, TyActions.focus_lastAddress]; exact l₁
  · change m₃.dead = m.dead
    rw [sd₃, TyActions.focus_dead]; exact d₁
  · refine held_touched ⟨l', m₃.lastUsed, rfl⟩ ⟨TyActions.stored_slot live₂ _, ?_, ?_⟩
    · rw [sn₃, TyActions.focus_nextId]; change m₁.nextId > m.nextId; omega
    · rw [sl₃, TyActions.focus_lastAddress]; exact le_of_eq l₁
  · intro id addr w x hh
    have hb := hh.above
    exact held_touched ⟨l', m₃.lastUsed, rfl⟩ (held_stored _ _ _ _ (by omega)
      (held_focus stann (held_touched ⟨li, m₁.lastUsed, rfl⟩
        (held_created pref d2 hsup (held_focus cann0 hh)))))
  · refine (ReturnConst.sequence_reaches file labels ann _ _ B env k m).trans ?_
    refine hcreate.trans ?_
    rw [afocus] at *
    refine (ReturnLit.bind_reaches pann a ty pt B env k m₁).trans ?_
    refine (ReturnConst.sequence_reaches file labels sann _ _ C env₁ k m₁).trans ?_
    refine (ReturnLit.bound_reaches bann ei env₁ _ m₁).trans ?_
    refine (Interleave.reaches_of_local file labels runi).trans ?_
    refine (bound_pop hfri _ KB m₂).trans ?_
    refine (ReturnLit.bind_reaches tpann t tty vl C env₁ k m₂).trans ?_
    refine (ReturnConst.sequence_reaches file labels cann _ ST PA env₂ k m₂).trans ?_
    refine (TyStmt.action_reaches Locals.request_store hev).trans ?_
    refine hst.trans ?_
    refine (Locals.annotations_bind_reaches xs upann uty .unit PA env₂ k m₃).trans ?_
    exact Interleave.reaches_of_local file labels hpure

/-! ## The global definitions -/

/-- Every definition is an integer of a supported type initialised by a literal: the globals,
their types and their stored values. -/
def inits (file : File Codec.wireModel Unit Unit) :
    List (Sym × Eff) → Option (List (Sym × IntegerType × Term))
  | [] => some []
  | (x, e) :: ds => (initTy file e).bind fun p => (inits file ds).map fun gs => (x, p) :: gs

theorem inits_length : ∀ {ds : List (Sym × EE)} {gs : List (Sym × IntegerType × Term)},
    inits file ds = some gs → gs.length = ds.length
  | [], gs, h => by simp only [inits, Option.some.injEq] at h; subst h; rfl
  | (x, e) :: ds, gs, h => by
    cases hn : initTy file e with
    | none => simp [inits, hn] at h
    | some p =>
      cases hgs : inits file ds with
      | none => simp [inits, hn, hgs] at h
      | some gs' =>
        simp only [inits, hn, hgs, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        simp [inits_length hgs]

theorem inits_syms : ∀ {ds : List (Sym × EE)} {gs : List (Sym × IntegerType × Term)},
    inits file ds = some gs → gs.map (·.1) = ds.map (·.1)
  | [], gs, h => by simp only [inits, Option.some.injEq] at h; subst h; rfl
  | (x, e) :: ds, gs, h => by
    cases hn : initTy file e with
    | none => simp [inits, hn] at h
    | some p =>
      cases hgs : inits file ds with
      | none => simp [inits, hn, hgs] at h
      | some gs' =>
        simp only [inits, hn, hgs, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        simp [inits_syms hgs]

/-- The globals created so far, with their values: each pointed to by every symbol with its key,
of a supported type, holding a value of its type above the last allocation, with distinct ids and
disjoint objects for distinct keys. -/
structure Placed (env : Env) (m : Mem.Concrete.State) (gl : List (Local × Term)) : Prop where
  env : ∀ g ∈ gl, ∀ y : Sym, y.key = g.1.sym.key → env.lookup y = some (ptr g.1)
  held : ∀ g ∈ gl, supported g.1.ity = true ∧ g.2.Ok zero ∧ Fits g.1.ity (g.2.val zero) ∧
    Held m g.1.id g.1.addr (width g.1.ity) (g.2.val zero)
  apart : ∀ a ∈ gl, ∀ b ∈ gl, a.1.sym.key ≠ b.1.sym.key →
    a.1.id ≠ b.1.id ∧ Slots.Apart a.1.addr (width a.1.ity) b.1.addr (width b.1.ity)

/-- The last address of the initial memory. -/
abbrev top : Int := 281474976710655

/-- The global definitions run in order, each global below the previous ones, at most `15` bytes
lower. -/
theorem globals_placed (args : List String) :
    ∀ (ds : List (Sym × EE)) (gs : List (Sym × IntegerType × Term)),
    inits file ds = some gs → (ds.map fun d => d.1.key).Nodup →
    ∀ (env : Env) (k : List Frame) (m : Mem.Concrete.State) (gl : List (Local × Term)),
    AnnOnly k → m.dead = [] → top - 15 * gl.length ≤ m.lastAddress →
    gl.length + ds.length < 4096 → Placed env m gl →
    (∀ d ∈ ds, ∀ g ∈ gl, d.1.key ≠ g.1.sym.key) →
    ∃ env' m' k' new, new.map (fun g => (g.1.sym, g.1.ity, g.2)) = gs ∧ m'.stdout = m.stdout ∧
      m'.dead = [] ∧ top - 15 * (gl.length + new.length) ≤ m'.lastAddress ∧
      AnnOnly k' ∧ Placed env' m' (gl ++ new) ∧
      Reaches file labels ⟨.globals ds args env, k, m⟩ ⟨.globals [] args env', k', m'⟩
  | [], gs, h, _, env, k, m, gl, hk, hdead, hlast, _, pl, _ => by
    simp only [inits, Option.some.injEq] at h
    subst h
    exact ⟨env, m, k, [], rfl, rfl, hdead, by simpa using hlast, hk, by simpa using pl, .refl⟩
  | (x, e) :: ds, gs, h, nd, env, k, m, gl, hk, hdead, hlast, room, pl, fresh => by
    cases hn : initTy file e with
    | none => simp [inits, hn] at h
    | some p =>
      obtain ⟨ity, v⟩ := p
      cases hgs : inits file ds with
      | none => simp [inits, hn, hgs] at h
      | some gs' =>
        simp only [inits, hn, hgs, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        have nd' : (ds.map fun d => d.1.key).Nodup := (List.nodup_cons.mp nd).2
        have fx : ∀ d ∈ ds, d.1.key ≠ x.key := by
          intro d hd e'
          exact (List.nodup_cons.mp nd).1 (List.mem_map.mpr ⟨d, hd, e'⟩)
        have fg : ∀ g ∈ gl, g.1.sym.key ≠ x.key := fun g hg e' =>
          fresh (x, e) List.mem_cons_self g hg e'.symm
        simp only [List.length_cons] at room
        have hsup : supported ity = true := by
          obtain ⟨_, _, _, _, cr, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, hcr, -⟩ := initTy_inv hn
          obtain ⟨_, _, _, _, _, _, _, _, _, -, hs⟩ := TyState.createTy_inv hcr
          exact hs
        have hw := TyActions.width_pos hsup
        have hw8 := TyActions.width_le hsup
        have hge := TyActions.nextAddress_ge m hw
        have hle := TyActions.nextAddress_le m hw
        have hpos : 0 < nextAddress m (width ity) := by
          simp only [top] at hlast
          omega
        obtain ⟨-, hok, hfit, m₁, xs, out₁, -, last₁, dead₁, new₁, keep₁, hinit⟩ :=
          initTy_reaches (file := file) (labels := labels) hn env
            (.globalResult x ds args env (Map.ofList (saves e).reverse) :: k) m hpos
            (by rw [hdead]; simp)
        let l : Local := ⟨x, m.nextId, nextAddress m (width ity), ity⟩
        have pl₁ : Placed (env.insert x (ptr l)) m₁ (gl ++ [(l, v)]) := by
          refine ⟨?_, ?_, ?_⟩
          · intro g hg y hy
            rcases List.mem_append.mp hg with hg | hg
            · rw [Map.lookup_insert_of_key_ne _ _ (show y.key ≠ x.key by rw [hy]; exact fg g hg)]
              exact pl.env g hg y hy
            · obtain rfl := List.mem_singleton.mp hg
              rw [ReturnLit.lookup_key hy]
              simp [l]
          · intro g hg
            rcases List.mem_append.mp hg with hg | hg
            · obtain ⟨hs, ho, hf, hh⟩ := pl.held g hg
              exact ⟨hs, ho, hf, keep₁ _ _ _ _ hh⟩
            · obtain rfl := List.mem_singleton.mp hg
              exact ⟨hsup, hok, hfit, new₁⟩
          · intro a ha b hb ne
            have old : ∀ g ∈ gl, g.1.id < m.nextId ∧
                nextAddress m (width ity) + width ity ≤ g.1.addr := by
              intro g hg
              have hh := (pl.held g hg).2.2.2
              exact ⟨hh.below, by have := hh.above; omega⟩
            rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
            · exact pl.apart a ha b hb ne
            · obtain rfl := List.mem_singleton.mp hb
              obtain ⟨i, d⟩ := old a ha
              exact ⟨Int.ne_of_lt i, .inr d⟩
            · obtain rfl := List.mem_singleton.mp ha
              obtain ⟨i, d⟩ := old b hb
              exact ⟨Int.ne_of_gt i, .inl d⟩
            · obtain rfl := List.mem_singleton.mp ha
              obtain rfl := List.mem_singleton.mp hb
              exact absurd rfl ne
        have hlast₁ : top - 15 * ((gl ++ [(l, v)]).length : Int) ≤ m₁.lastAddress := by
          rw [last₁, List.length_append, List.length_singleton]
          push_cast
          omega
        have fresh₁ : ∀ d ∈ ds, ∀ g ∈ gl ++ [(l, v)], d.1.key ≠ g.1.sym.key := by
          intro d hd g hg
          rcases List.mem_append.mp hg with hg | hg
          · exact fresh d (List.mem_cons_of_mem _ hd) g hg
          · obtain rfl := List.mem_singleton.mp hg
            exact fx d hd
        obtain ⟨env', m', k', new, hnew, out, dead', last', hk', pl', reach⟩ :=
          globals_placed args ds gs' hgs nd' (env.insert x (ptr l)) (.annotations xs :: k) m₁
            (gl ++ [(l, v)]) (annOnly_cons hk) (by rw [dead₁, hdead]) hlast₁
            (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) pl₁ fresh₁
        refine ⟨env', m', k', (l, v) :: new, by simp [hnew, l], by rw [out, out₁], dead', ?_, hk',
          by simpa using pl', ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil] at last' ⊢
          push_cast at last' ⊢
          linarith
        · exact (Globals.global_reaches x e ds args env k m).trans (hinit.trans
            ((Globals.globalResult_reaches xs x ds args env _ (ptr l) k m₁).trans reach))

/-! ## Startup -/

theorem actions_created_eq (pref : Prefix) (ann : List Annot) (m : Mem.Concrete.State) :
    Actions.created pref ann m = created pref ann (.signed .int) m := by
  have hw : width (.signed .int) = 4 := rfl
  have hn : nextAddress m 4 = nextIntAddress m := by simp [nextAddress, nextIntAddress]
  simp only [Actions.created, created, hw, hn]
  rfl

/-- The `errno` startup from any memory with room below its last allocation keeps every global,
and drops the frames below it. -/
theorem startup_errno (c : Control) (k : List Frame) (m : Mem.Concrete.State)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ∃ m' xs, m'.stdout = m.stdout ∧ m'.dead = m.dead ∧ m'.lastAddress = nextIntAddress m ∧
      (∀ id addr w v, Held m id addr w v → Held m' id addr w v) ∧
      Reaches file labels ⟨.startup c, k, m⟩ ⟨c, [.annotations xs], m'⟩ := by
  let pt : Val := .object (.pointer (.allocated m.nextId (nextIntAddress m)))
  let m₁ := Actions.created (.other "errno") [] m
  have live₁ : Mem.Concrete.LiveInt m₁ m.nextId (nextIntAddress m) := Locals.created_live _ _ m hdead
  have hcreate : Reaches file labels ⟨.startup c, k, m⟩ ⟨.value pt, [.startupStore c], m₁⟩ :=
    Actions.memory_reaches (name := "Create") (by intro o h; cases h) (by
      simp only [request, requestAux, awaitsScheduling, memoryRequest]
      simp only [show Ctype.mk [] (.basic (.integer (.signed .int))) = Mem.Concrete.intType [] from rfl,
        integer, Mem.Concrete.allocate_int _ [] m hpos]
      simp [bind, Except.bind, pure, Except.pure, m₁, Actions.created, pt])
  obtain ⟨r, hr⟩ : ∃ r, request file labels ⟨.value pt, [.startupStore c], m₁⟩ = r := ⟨_, rfl⟩
  have hr' := hr
  simp [request, requestAux, awaitsScheduling, memoryRequest, toMemory, objectMemory, pt,
    show Ctype.mk [] (.basic (.integer (.signed .int))) = Mem.Concrete.intType [] from rfl,
    Mem.Concrete.store_int _ [] live₁ (show Mem.Concrete.IntRange 0 by unfold Mem.Concrete.IntRange; omega),
    Mem.Concrete.access_int _ [] live₁, bind, Except.bind, pure, Except.pure] at hr'
  subst hr'
  let m₂ := Locals.stored m₁ m.nextId (nextIntAddress m) 0
  have hstore : Reaches file labels ⟨.value pt, [.startupStore c], m₁⟩
      ⟨.value .unit, [.annotations [⟨none, [], true, nextIntAddress m, 4⟩], .startupEnter c], m₂⟩ :=
    Actions.memory_reaches (by intro o h; cases h) hr
  refine ⟨{m₂ with currentLocation := .other "Driver.drive"}, [⟨none, [], true, nextIntAddress m, 4⟩],
    ?_, ?_, ?_, ?_, hcreate.trans (hstore.trans ?_)⟩
  · change m₂.stdout = m.stdout
    rw [(Globals.stored_same m₁ _ _ _).2.2.2, Actions.created_stdout]
  · change m₂.dead = m.dead
    rw [(Globals.stored_same m₁ _ _ _).2.2.1, Locals.created_dead]
  · change m₂.lastAddress = nextIntAddress m
    rw [(Globals.stored_same m₁ _ _ _).2.1, Locals.created_lastAddress]
  · intro id addr w v hh
    have ha := hh.above
    have bnd := Globals.nextIntAddress_bounds m
    have h₁ : Held m₁ id addr w v := by
      rw [show m₁ = created (.other "errno") [] (.signed .int) m from actions_created_eq _ _ m]
      exact held_created _ _ (ity := .signed .int) rfl hh
    exact held_touched ⟨_, m₂.lastUsed, rfl⟩
      (held_stored (m := m₁) m.nextId (nextIntAddress m) 4 0 (by omega) h₁)
  · exact Straight.update_reaches (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])

/-- The definitions of the globals: each key defined by the term of the stored value of its
first global. -/
def defs (gs : List (Sym × IntegerType × Term)) : Key → Option Term :=
  fun q => (gs.find? fun g => g.1.key == q).map fun g => g.2.2

/-- **Startup with typed globals, as slots.** From the initial state of a file whose global
definitions are integer objects of supported types initialised by literals (`gs`), with distinct
symbols, whose `main` is a procedure without parameters, the dynamics reaches `main`'s body with
the globals as slots `lg` (`Inv`, each defined by its stored value, and `Fresh`), under one
annotation frame, with empty stdout. -/
theorem initial_reaches_state (file : Program) (enums : Map Sym IntegerType) (args : List String)
    {gs : List (Sym × IntegerType × Term)} (hgs : inits file (definitions file) = some gs)
    (nd : ((definitions file).map fun d => d.1.key).Nodup)
    (room : (definitions file).length < 1024)
    {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {body : EE}
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [] body)) :
    ∃ s m env xs lg, initial file enums args = .ok (s, Map.ofList (saves body).reverse) ∧
      m.stdout = "" ∧ lg.map (fun l => (l.sym, l.ity)) = gs.map (fun g => (g.1, g.2.1)) ∧
      Inv env m lg (defs gs) ∧ Fresh m lg ∧
      Reaches file (Map.ofList (saves body).reverse) s ⟨.effectExpr body env, [.annotations xs], m⟩ := by
  let labels : Labels := Map.ofList (saves body).reverse
  let m₀ : Mem.Concrete.State := {enumTypes := enums}
  have last₀ : top - 15 * (([] : List (Local × Term)).length : Int) ≤ m₀.lastAddress := by
    show top - 15 * 0 ≤ 281474976710655
    simp [top]
  obtain ⟨env, m₁, k₁, new, hnew, out₁, dead₁, last₁, -, pl, reach₁⟩ :=
    globals_placed (file := file) (labels := labels) args (definitions file) gs hgs nd ∅ [] m₀ []
      (by simp [AnnOnly]) rfl last₀ (by simp; omega) ⟨by simp, by simp, by simp⟩ (by simp)
  simp only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add] at pl last₁
  have hlen : new.length = (definitions file).length := by
    rw [← inits_length hgs, ← hnew, List.length_map]
  have bnd := Globals.nextIntAddress_bounds m₁
  have hpos : 0 < nextIntAddress m₁ := by
    simp only [top] at last₁
    omega
  obtain ⟨m₂, xs, out₂, dead₂, last₂, keep₂, reach₂⟩ := startup_errno (file := file)
    (labels := labels) (.effectExpr body env) k₁ m₁ hpos (by rw [dead₁]; simp)
  have held : ∀ g ∈ new, supported g.1.ity = true ∧ g.2.Ok zero ∧ Fits g.1.ity (g.2.val zero) ∧
      Held m₂ g.1.id g.1.addr (width g.1.ity) (g.2.val zero) := fun g hg =>
    ⟨(pl.held g hg).1, (pl.held g hg).2.1, (pl.held g hg).2.2.1, keep₂ _ _ _ _ (pl.held g hg).2.2.2⟩
  have mem : ∀ a ∈ new.map (·.1), ∃ g ∈ new, g.1 = a := fun a ha => List.mem_map.mp ha
  have keys : ((new.map (·.1)).map (·.sym.key)).Nodup := by
    have e1 : (new.map (·.1)).map (·.sym.key) = (gs.map (·.1)).map (·.key) := by
      rw [← hnew]; simp [Function.comp_def]
    rw [e1, inits_syms hgs, List.map_map]
    exact nd
  refine ⟨_, m₂, env, xs, new.map (·.1), ?_, by rw [out₂, out₁], ?_, ?_, ?_,
    reach₁.trans ((Globals.enter_main_reaches args env k₁ m₁ main decl).trans reach₂)⟩
  · simp [initial, definitions, main, decl]
    refine ⟨?_, rfl⟩
    congr 1
  · rw [← hnew]; simp [Function.comp_def]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a ha y hy
      obtain ⟨g, hg, rfl⟩ := mem a ha
      exact pl.env g hg y hy
    · intro a ha
      obtain ⟨g, hg, rfl⟩ := mem a ha
      exact ⟨(held g hg).1, (held g hg).2.2.2.slot.live⟩
    · intro a ha b hb e
      exact List.inj_on_of_nodup_map keys ha hb e
    · intro a ha b hb ne
      obtain ⟨g, hg, rfl⟩ := mem a ha
      obtain ⟨g', hg', rfl⟩ := mem b hb
      exact pl.apart g hg g' hg' ne
    · intro q d hd
      unfold defs at hd
      cases hf : gs.find? (fun g => g.1.key == q) with
      | none => simp [hf] at hd
      | some p =>
        simp only [hf, Option.map_some, Option.some.injEq] at hd
        subst hd
        have hp : p ∈ gs := List.mem_of_find?_eq_some hf
        have hk : p.1.key = q := by simpa using List.find?_some hf
        rw [← hnew] at hp
        obtain ⟨g, hg, hgp⟩ := List.mem_map.mp hp
        have r := held g hg
        rw [← hgp] at hk ⊢
        exact ⟨r.2.1, g.1, List.mem_map_of_mem hg, hk, r.2.2.1, r.2.2.2.slot⟩
  · refine ⟨by rw [dead₂, dead₁], ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨g, hg, rfl⟩ := mem a ha
      exact (held g hg).2.2.2.below
    · intro a ha
      obtain ⟨g, hg, rfl⟩ := mem a ha
      exact (held g hg).2.2.2.above
    · rw [last₂, List.length_map, hlen]
      have : (StartupReach.errnoAddr : Int) = top - 7 := by simp [StartupReach.errnoAddr, top]
      rw [this]
      rw [hlen] at last₁
      omega

end Silmaril.Compile.Core.Verified.TyGlobals
