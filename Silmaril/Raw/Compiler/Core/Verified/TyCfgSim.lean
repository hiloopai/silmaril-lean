module

public import Silmaril.Compiler.Core.Verified.TyCfg.Defs
public import Silmaril.Compiler.Core.Verified.CfgSound.Defs
/-! # `main` as a control-flow graph over typed slots: the derivations and the relation

The typed counterparts of `CfgSound`'s slot-dependent parts: the pending statements over typed
locals (`Pends`), rebinding slots at a `save` or `run`, the creation of typed locals and the
seeding of the globals' registers, the placement of the trees (`At`), the derivations of `walk`
(`Seg`) and the relation of the two runs at the root of a node (`Rel`), with the jump to a label
(`jump_iter`). The label table, the Core paths of a `run` and the Lir paths of a jump are
`CfgSound`'s.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyCfg

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Silmaril.Machine
open TyExpr (Key Term values close zero)
open TyMem (Local Inv Fresh Defined defsOf update ptr)
open TyStmt (Vars Keys isLocal isFresh typedIn)
open TyLoopStep (Layout Registers)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ReturnConst (focusMemory)
open LoopMain (regOf)
open Cfg (find symArgs labelDefs)
open Mem.Concrete (nextAddress)
open TyActions (width)
open Relation

variable {file : Program} {labels : Labels}

/-! ## Pending statements -/

/-- The frames `F` hold the pending statements `P` as wildcard strong sequences whose
environments point every slot to its object, among annotation frames, above frames without a
procedure boundary (`Cfg.Pends` over typed slots). -/
inductive Pends (ls : List Local) : List EE → List Frame → Prop where
  | base {F : List Frame} : NoBoundary F → Pends ls [] F
  | ann {P : List EE} {F : List Frame} (xs : List Access) : Pends ls P F →
      Pends ls P (.annotations xs :: F)
  | bind {P : List EE} {F : List Frame} (pann : List Annot) (ty : BaseType) (b : EE) (env : Env) :
      TyRun.EnvOk env ls → Pends ls P F →
      Pends ls (b :: P) (.strongBind (.mk pann (.base (none, ty))) b env :: F)

theorem Pends.noBoundary {ls : List Local} {P : List EE} {F : List Frame} (h : Pends ls P F) :
    NoBoundary F := by
  induction h with
  | base h => exact h
  | ann xs _ ih => exact noBoundary_cons ih trivial
  | bind pann ty b env _ _ ih => exact noBoundary_cons ih trivial

/-- **The value `unit` pops the next pending statement**, merging and floating annotation
frames as Core does. -/
theorem Pends.pop {ls : List Local} {b : EE} {P : List EE} :
    (F : List Frame) → Pends ls (b :: P) F → (m : Mem.Concrete.State) →
    ∃ env F', TyRun.EnvOk env ls ∧ Pends ls P F' ∧
      Reaches file labels ⟨.value .unit, F, m⟩ ⟨.effectExpr b env, F', m⟩
  | [], h, _ => by cases h
  | f :: F, h, m => by
    cases h with
    | bind pann ty b env hb h =>
      exact ⟨env, F, hb, h, ReturnConst.wildcard_sequence_reaches file labels pann ty .unit b env F m⟩
    | ann xs h =>
      cases h with
      | bind pann ty b env hb h' =>
        exact ⟨env, _, hb, .ann xs h', Locals.annotations_bind_reaches xs pann ty .unit b env _ m⟩
      | ann ys h' =>
        obtain ⟨env, F', hb, hp, r⟩ := Pends.pop (.annotations (xs ++ ys) :: _) (.ann (xs ++ ys) h') m
        exact ⟨env, F', hb, hp, (Locals.annotations_merge_reaches xs ys .unit _ m).trans r⟩
termination_by F => F.length

/-! ## Slots -/

theorem slot_of_keys {ls : List Local} {xs : Vars} (keys : Keys ls xs) {x : Sym}
    (h : isSlot xs x = true) : ∃ l ∈ ls, x.key = l.sym.key := by
  obtain ⟨y, hy, hk⟩ := List.any_eq_true.mp h
  have hm : (y.1.key, y.2) ∈ ls.map (fun l => (l.sym.key, l.ity)) := by
    rw [keys]; exact List.mem_map_of_mem (f := fun y => (y.1.key, y.2)) hy
  obtain ⟨l, hl, hlk⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at hlk
  exact ⟨l, hl, (beq_iff_eq.mp hk).symm.trans hlk.1.symm⟩

/-- The registers of the slots are distinct and below the temporaries. -/
theorem layout {xs : Vars} {ls : List Local} (keys : Keys ls xs) :
    Layout (regOf (xs.map (·.1.key))) xs.length ls := by
  have mem : ∀ l ∈ ls, l.sym.key ∈ xs.map (·.1.key) := fun l hl => by
    rw [← keys.keys]; exact List.mem_map_of_mem hl
  refine ⟨fun l hl => by simpa using LoopMain.regOf_lt (mem l hl), fun a ha b hb ne h => ne ?_⟩
  exact LoopMain.regOf_inj (mem a ha) (mem b hb) h

/-- Every key of `dk` has a definition. -/
def Covers (dk : List Key) (ds : Key → Option Term) : Prop := ∀ q ∈ dk, (ds q).isSome

theorem Covers.defined {dk : List Key} {ds : Key → Option Term} (cov : Covers dk ds)
    {t : Term} (h : covered dk t = true) : Defined ds t = true := by
  unfold covered at h
  unfold Defined
  rw [List.all_eq_true] at h ⊢
  intro q hq
  exact cov q.1 (by simpa using h q hq)

theorem usable_spec {xs : Vars} {dk : List Key} {t : Term} (h : usable xs dk t = true) :
    covered dk t = true ∧ typedIn xs t = true ∧ t.Wf := by
  simp only [usable, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, TyState.Term.wf_spec t h.2⟩

/-- Rebinding a symbol to the object of the slot with its key keeps `Inv`. -/
theorem rebind {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (q : Sym) (key : q.key = l.sym.key) :
    Inv (extendEnv [(q, ptr l)] env) m ls ds := by
  refine ⟨fun l' hl' y hy => ?_, inv.live, inv.uniq, inv.apart, inv.defs⟩
  by_cases e : y.key = q.key
  · have : l' = l := inv.uniq l' hl' l hl (hy.symm.trans (e.trans key))
    subst this
    exact ConvInt.lookup_one e
  · rw [ConvInt.lookup_one_other e]
    exact inv.env l' hl' y hy

/-- Rebinding parameters to the objects of their slots keeps `Inv`. -/
theorem rebinds {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option Term} (inv : Inv env m ls ds) {qs : List Sym} {vs : List Val}
    (h : List.Forall₂ (fun (q : Sym) (v : Val) => ∃ l ∈ ls, q.key = l.sym.key ∧ v = ptr l) qs vs) :
    Inv (extendEnv (qs.zip vs) env) m ls ds := by
  induction h with
  | nil => simpa [extendEnv] using inv
  | cons hqv _ ih =>
    obtain ⟨l, hl, key, hv⟩ := hqv
    subst hv
    rw [List.zip_cons_cons, Cfg.extendEnv_cons]
    exact rebind ih hl _ key

theorem forall₂_keys {ls : List Local} : (qs ys : List Sym) → (vs : List Val) →
    qs.map (·.key) = ys.map (·.key) →
    List.Forall₂ (fun (y : Sym) (v : Val) => ∃ l ∈ ls, y.key = l.sym.key ∧ v = ptr l) ys vs →
    List.Forall₂ (fun (q : Sym) (v : Val) => ∃ l ∈ ls, q.key = l.sym.key ∧ v = ptr l) qs vs
  | [], [], [], _, .nil => .nil
  | q :: qs, y :: ys, v :: vs, h, .cons ⟨l, hl, key, hv⟩ rest => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons ⟨l, hl, h.1.trans key, hv⟩ (forall₂_keys qs ys vs h.2 rest)
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h

/-- The symbol arguments of a `run` evaluate to the objects of their slots. -/
theorem symArgs_evals {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option Term} (inv : Inv env m ls ds) {xs : Vars} (keys : Keys ls xs) :
    (args : List PE) → (ys : List Sym) → symArgs args = some ys → ys.all (isSlot xs) = true →
    ∃ vs, List.Forall₂ (fun p v => SeqReach.PureEval file labels p env v) args vs ∧
      List.Forall₂ (fun (y : Sym) (v : Val) => ∃ l ∈ ls, y.key = l.sym.key ∧ v = ptr l) ys vs
  | [], ys, h, _ => by
    simp only [symArgs, Option.some.injEq] at h
    subst h
    exact ⟨[], .nil, .nil⟩
  | p :: ps, ys, h, hl => by
    obtain ⟨a, y, ys', rfl, h', rfl⟩ := Cfg.symArgs_cons h
    simp only [List.all_cons, Bool.and_eq_true] at hl
    obtain ⟨l, hlm, key⟩ := slot_of_keys keys hl.1
    obtain ⟨vs, ev, rel⟩ := symArgs_evals inv keys ps ys' h' hl.2
    exact ⟨ptr l :: vs, .cons (SeqReach.pure_symbol a y env _ (inv.lookup hlm key)) ev,
      .cons ⟨l, hlm, key, rfl⟩ rel⟩

theorem selfParams_evals {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option Term} (inv : Inv env m ls ds) {xs : Vars} (keys : Keys ls xs) :
    (ps : List (Sym × ((BaseType × Option (Ctype × PassBy)) × PE))) → selfParams xs ps = true →
    ∃ vs, List.Forall₂ (fun p v => SeqReach.PureEval file labels p env v) (ps.map (fun x => x.2.2)) vs ∧
      List.Forall₂ (fun (q : Sym) (v : Val) => ∃ l ∈ ls, q.key = l.sym.key ∧ v = ptr l)
        (ps.map Prod.fst) vs
  | [], _ => ⟨[], .nil, .nil⟩
  | (x, (i, p)) :: ps, h => by
    rcases p with ⟨a, u, node⟩
    cases u
    cases node <;> simp [selfParams] at h
    rename_i x'
    obtain ⟨⟨hk, hloc⟩, hrest⟩ := h
    obtain ⟨l, hl, key⟩ := slot_of_keys keys hloc
    obtain ⟨vs, ev, rel⟩ := selfParams_evals inv keys ps hrest
    exact ⟨ptr l :: vs, .cons (SeqReach.pure_symbol a x' env _ (inv.lookup hl (hk.trans key))) ev,
      .cons ⟨l, hl, key, rfl⟩ rel⟩

/-! ## Creating the locals and seeding the globals -/

/-- Creating typed locals keeps the earlier slots' definitions, `Inv` and `Fresh`
(`TyRun.block_halts`). -/
theorem creates_reaches_fresh (xs : Vars) (e : EE) {ys : Vars} {e' : EE}
    (h : creates xs e = some (ys, e')) (env : Env) (m : Mem.Concrete.State)
    (ls : List Local) {ds : Key → Option Term} (inv : Inv env m ls ds) (hls : Keys ls xs)
    (fresh : Fresh m ls) (k : List Frame) :
    ∃ env' m' ls', Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.effectExpr e' env', k, m'⟩ ∧
      Inv env' m' ls' ds ∧ Keys ls' ys ∧ m'.stdout = m.stdout ∧ Fresh m' ls' := by
  have hlen : ls.length = xs.length := by
    have := congrArg List.length hls; simpa using this
  unfold creates at h
  split at h
  next a p x ty cr rest =>
    split at h
    next ity hcr =>
      split at h
      next hc =>
        obtain ⟨hfx, hlt⟩ := hc
        obtain ⟨ann, lc, u, a1, a2, c1, a3, c2, pref, rfl, hs⟩ := TyState.createTy_inv hcr
        have hw := TyActions.width_pos hs
        have hw8 := TyActions.width_le hs
        have hge := TyActions.nextAddress_ge m hw
        have hle := TyActions.nextAddress_le m hw
        have hlast := fresh.last
        have herr := TyState.errno_large
        have hpos : 0 < nextAddress m (width ity) := by
          rw [hlen] at hlast
          have : (xs.length : Int) < 1024 := by exact_mod_cast hlt
          omega
        let REST := rest
        let K := Frame.strongBind (.mk p (.base (some x, ty))) REST env :: k
        have create := TyActions.create_reaches (file := file) (labels := labels) ann a1 a2 a3 c1 c2 lc u
          pref hs env K m hpos
        let nl : Local := ⟨x, m.nextId, nextAddress m (width ity), ity⟩
        let m₁ := TyActions.created pref c2 ity (focusMemory ann m)
        let env₁ := extendEnv [(x, ptr nl)] env
        have bind := ReturnLit.bind_reaches (file := file) (labels := labels) p x ty (ptr nl) REST env k m₁
        have fx : ∀ l ∈ ls, l.sym.key ≠ x.key := hls.fresh hfx
        have ids : ∀ l ∈ ls, l.id < m.nextId := fresh.ids
        have addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr := fresh.addrs
        have nfocus : (focusMemory ann m).nextId = m.nextId := TyActions.focus_nextId ann m
        have afocus : nextAddress (focusMemory ann m) (width ity) = nextAddress m (width ity) :=
          TyActions.nextAddress_focus ann m _
        have inv₁ : Inv env₁ m₁ (ls ++ [nl]) ds := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro l hl y hy
            rcases List.mem_append.mp hl with hl | hl
            · rw [ConvInt.lookup_one_other (by rw [hy]; exact fx l hl)]
              exact inv.env l hl y hy
            · obtain rfl := List.mem_singleton.mp hl
              exact ConvInt.lookup_one hy
          · intro l hl
            rcases List.mem_append.mp hl with hl | hl
            · refine ⟨(inv.live l hl).1, TyActions.live_created
                (TyActions.liveSz_focus ann (inv.live l hl).2) pref c2 ity ?_⟩
              rw [nfocus]; exact Int.ne_of_lt (ids l hl)
            · obtain rfl := List.mem_singleton.mp hl
              refine ⟨hs, ?_⟩
              have := TyActions.created_live pref c2 ity (focusMemory ann m)
                (by rw [TyActions.focus_dead, fresh.dead, nfocus]; simp)
              rwa [afocus, nfocus] at this
          · intro a ha b hb e
            rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
            · exact inv.uniq a ha b hb e
            · obtain rfl := List.mem_singleton.mp hb
              exact absurd e (fx a ha)
            · obtain rfl := List.mem_singleton.mp ha
              exact absurd e.symm (fx b hb)
            · obtain rfl := List.mem_singleton.mp ha
              obtain rfl := List.mem_singleton.mp hb
              rfl
          · intro a ha b hb ne
            rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
            · exact inv.apart a ha b hb ne
            · obtain rfl := List.mem_singleton.mp hb
              refine ⟨Int.ne_of_lt (ids a ha), ?_⟩
              have := addrs a ha
              show a.addr + width a.ity ≤ nextAddress m (width ity) ∨
                nextAddress m (width ity) + width ity ≤ a.addr
              omega
            · obtain rfl := List.mem_singleton.mp ha
              refine ⟨Int.ne_of_gt (ids b hb), ?_⟩
              have := addrs b hb
              show nextAddress m (width ity) + width ity ≤ b.addr ∨
                b.addr + width b.ity ≤ nextAddress m (width ity)
              omega
            · obtain rfl := List.mem_singleton.mp ha
              obtain rfl := List.mem_singleton.mp hb
              exact absurd rfl ne
          · intro q d hd
            obtain ⟨ok, l, hl, hkq, hf, slot⟩ := inv.defs q d hd
            refine ⟨ok, l, List.mem_append_left _ hl, hkq, hf, ?_⟩
            have := addrs l hl
            exact TyActions.slot_created (TyActions.slot_focus ann slot) pref c2 ity
              (by rw [nfocus]; exact Int.ne_of_lt (ids l hl)) (.inl (by rw [afocus]; omega))
        have hls₁ : Keys (ls ++ [nl]) (xs ++ [(x, ity)]) := by
          simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hls ⊢
          rw [hls]
        have last₁ : m₁.lastAddress = nextAddress m (width ity) := by
          rw [TyActions.created_lastAddress, afocus]
        have fresh₁ : Fresh m₁ (ls ++ [nl]) := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [TyActions.created_dead, TyActions.focus_dead, fresh.dead]
          · intro l hl
            rw [TyActions.created_nextId, nfocus]
            rcases List.mem_append.mp hl with hl | hl
            · have := ids l hl; omega
            · obtain rfl := List.mem_singleton.mp hl
              show m.nextId < m.nextId + 1
              omega
          · intro l hl
            rw [last₁]
            rcases List.mem_append.mp hl with hl | hl
            · have := addrs l hl; omega
            · obtain rfl := List.mem_singleton.mp hl
              exact le_refl _
          · rw [last₁, List.length_append, List.length_singleton]
            push_cast
            omega
        obtain ⟨env', m', ls', reach, inv', hls', out', fresh'⟩ :=
          creates_reaches_fresh (xs ++ [(x, ity)]) rest h env₁ m₁ (ls ++ [nl]) inv₁ hls₁ fresh₁ k
        have out : m₁.stdout = m.stdout := by
          simp [m₁, TyActions.created_stdout]
        exact ⟨env', m', ls', (ReturnConst.sequence_reaches file labels a _ _ REST env k m).trans
          (create.trans (bind.trans reach)), inv', hls', out'.trans out, fresh'⟩
      next => cases h
    next => cases h
  next =>
    cases h
    exact ⟨env, m, ls, .refl, inv, hls, rfl, fresh⟩
termination_by sizeOf e

/-- The slots returned by the creations start with the original ones. -/
theorem creates_prefix (xs : Vars) (e : EE) {ys : Vars} {e' : EE}
    (h : creates xs e = some (ys, e')) : xs <+: ys := by
  unfold creates at h
  split at h
  · split at h
    · split at h
      · exact (List.prefix_append xs [_]).trans (creates_prefix _ _ h)
      · cases h
    · cases h
  · cases h; exact List.prefix_refl _
termination_by sizeOf e

theorem creates_length (xs : Vars) (e : EE) {ys : Vars} {e' : EE}
    (h : creates xs e = some (ys, e')) (hx : xs.length ≤ 1024) : ys.length ≤ 1024 := by
  unfold creates at h
  split at h
  · split at h
    · split at h
      · rename_i hc
        exact creates_length _ _ h (by simp; omega)
      · cases h
    · cases h
  · cases h; exact hx
termination_by sizeOf e

/-- Seeding the globals' registers establishes the startup definitions. -/
theorem seed_exec (ks : List Key) (d : Nat) (hd : ks.length ≤ d) :
    (gs : List (Sym × IntegerType × Term)) → (∀ g ∈ gs, g.1.key ∈ ks) →
    (∀ g ∈ gs, g.2.2.Wf) → (∀ g ∈ gs, g.2.2.vars = []) → (fr : Lir.Frame Mir.Reg) →
    (mem : Lir.Memory) →
    ∃ fr', Lir.execOps (seedOps (regOf ks) d gs) fr mem = some (fr', mem) ∧
      Registers (regOf ks) (TyGlobals.defs gs) fr'
  | [], _, _, _, fr, mem => ⟨fr, rfl, fun _ _ h => by simp [TyGlobals.defs] at h⟩
  | (x, ity, t) :: gs, keys, wf, closed, fr, mem => by
    obtain ⟨fr', hx, hr⟩ := seed_exec ks d hd gs (fun g hg => keys g (List.mem_cons_of_mem _ hg))
      (fun g hg => wf g (List.mem_cons_of_mem _ hg)) (fun g hg => closed g (List.mem_cons_of_mem _ hg))
      fr mem
    have hxk : x.key ∈ ks := keys (x, ity, t) List.mem_cons_self
    have ht : t.vars = [] := closed (x, ity, t) List.mem_cons_self
    obtain ⟨fr'', exec, result, other⟩ := TyInput.assign_exec (regOf ks) zero
      (wf (x, ity, t) List.mem_cons_self) x.key d fr' mem (by intro p hp; simp [ht] at hp)
    refine ⟨fr'', by simp [seedOps, Lir.execOps_append, hx, exec], ?_⟩
    intro q a ha
    by_cases he : x.key = q
    · simp [TyGlobals.defs, he] at ha
      subst ha
      rw [← he]; exact result
    · have ha' : TyGlobals.defs gs q = some a := by simpa [TyGlobals.defs, he] using ha
      have hm : q ∈ ks := by
        unfold TyGlobals.defs at ha'
        obtain ⟨g, hg, _⟩ := Option.map_eq_some_iff.mp ha'
        have hq : g.1.key = q := by simpa using List.find?_some hg
        rw [← hq]
        exact keys g (List.mem_cons_of_mem _ (List.mem_of_find?_eq_some hg))
      have ne : regOf ks q ≠ regOf ks x.key := fun eq => he (LoopMain.regOf_inj hm hxk eq).symm
      rw [other _ (by have := LoopMain.regOf_lt hm; omega) ne]
      exact hr q a ha'

/-! ## Blocks -/

/-- The blocks of the nodes of a tree whose root is block `i`. -/
def At (bs : List (Lir.Block Mir.Reg)) (regs : Key → Mir.Reg) (d : Nat) (idx : Key → Nat) :
    Nat → Code → Prop
  | i, .atom (.set q ity t) c =>
    bs[i]? = some ⟨(TyInput.assign regs q d (TyStmt.convT ity t)).map .op, .jump (i + 1)⟩ ∧
      At bs regs d idx (i + 1) c
  | i, .atom (.clear _) c => bs[i]? = some ⟨[], .jump (i + 1)⟩ ∧ At bs regs d idx (i + 1) c
  | i, .test _ t y n =>
    bs[i]? = some (TyLoopCondition.testBlock regs d t (i + 1 + y.size) (i + 1)) ∧
      At bs regs d idx (i + 1) y ∧ At bs regs d idx (i + 1 + y.size) n
  | i, .goto l => bs[i]? = some ⟨[], .jump (idx l)⟩
  | i, .ret t => bs[i]? = some ⟨(TyInput.ops regs d t).map .op, .ret [.reg d]⟩
  | i, .abort => bs[i]? = some ⟨StateExitLink.abortOps.map .op, .trap⟩

theorem emit_length (regs : Key → Mir.Reg) (d : Nat) (idx : Key → Nat) :
    (c : Code) → (i : Nat) → (c.emit regs d idx i).length = c.size
  | .atom (.set _ _ _) c, i => by simp [Code.emit, Code.size, emit_length regs d idx c (i + 1)]
  | .atom (.clear _) c, i => by simp [Code.emit, Code.size, emit_length regs d idx c (i + 1)]
  | .test _ _ y n, i => by
    simp [Code.emit, Code.size, emit_length regs d idx y, emit_length regs d idx n]
  | .goto _, _ => rfl
  | .ret _, _ => rfl
  | .abort, _ => rfl

/-- The emitted tree is where `At` says, wherever it is placed. -/
theorem emit_at (regs : Key → Mir.Reg) (d : Nat) (idx : Key → Nat) :
    (c : Code) → (i : Nat) → (pre post : List (Lir.Block Mir.Reg)) → pre.length = i →
    At (pre ++ c.emit regs d idx i ++ post) regs d idx i c
  | .atom (.set q ity t) c, i, pre, post, h => by
    refine ⟨?_, ?_⟩
    · subst h; simp [Code.emit]
    · have := emit_at regs d idx c (i + 1)
        (pre ++ [⟨(TyInput.assign regs q d (TyStmt.convT ity t)).map .op, .jump (i + 1)⟩]) post
        (by simp [h])
      simpa [Code.emit, List.append_assoc] using this
  | .atom (.clear q) c, i, pre, post, h => by
    refine ⟨?_, ?_⟩
    · subst h; simp [Code.emit]
    · have := emit_at regs d idx c (i + 1) (pre ++ [⟨[], .jump (i + 1)⟩]) post (by simp [h])
      simpa [Code.emit, List.append_assoc] using this
  | .test direct t y n, i, pre, post, h => by
    let tb := TyLoopCondition.testBlock regs d t (i + 1 + y.size) (i + 1)
    refine ⟨?_, ?_, ?_⟩
    · subst h; simp [Code.emit]
    · have := emit_at regs d idx y (i + 1) (pre ++ [tb]) (n.emit regs d idx (i + 1 + y.size) ++ post)
        (by simp [h])
      simpa [Code.emit, List.append_assoc, tb] using this
    · have := emit_at regs d idx n (i + 1 + y.size) (pre ++ [tb] ++ y.emit regs d idx (i + 1)) post
        (by simp [h, emit_length]; omega)
      simpa [Code.emit, List.append_assoc, tb] using this
  | .goto l, i, pre, post, h => by subst h; simp [Code.emit, At]
  | .ret t, i, pre, post, h => by subst h; simp [Code.emit, At]
  | .abort, i, pre, post, h => by subst h; simp [Code.emit, At]

/-- Each label's tree is at its first block. -/
theorem emitAll_at (regs : Key → Mir.Reg) (d : Nat) (idx : Key → Nat) :
    (cs : List (Key × Code)) → (cs.map (·.1)).Nodup → (i : Nat) → (pre : List (Lir.Block Mir.Reg)) →
    pre.length = i → ∀ l c, (l, c) ∈ cs → At (pre ++ emitAll regs d idx i cs) regs d idx (pos i cs l) c
  | [], _, _, _, _, _, _, hm => by cases hm
  | (l', c') :: cs, nd, i, pre, h, l, c, hm => by
    simp only [List.map_cons, List.nodup_cons] at nd
    rcases List.mem_cons.mp hm with eq | hm
    · simp only [Prod.mk.injEq] at eq
      obtain ⟨rfl, rfl⟩ := eq
      have := emit_at regs d idx c i pre (emitAll regs d idx (i + c.size) cs) h
      simpa [pos, emitAll, List.append_assoc] using this
    · have hne : l' ≠ l := by
        rintro rfl
        exact nd.1 (List.mem_map.mpr ⟨(l', c), hm, rfl⟩)
      have := emitAll_at regs d idx cs nd.2 (i + c'.size) (pre ++ c'.emit regs d idx i)
        (by simp [h, emit_length]) l c hm
      simpa [pos, hne, emitAll, List.append_assoc] using this

/-! ## The derivations of `walk` -/

/-- `c` is the code of `e` followed by the pending statements `P`, with `dk` defined. -/
inductive Seg (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : Vars)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) (T : List Key) :
    List Key → EE → List EE → Code → Prop where
  | retn {dk : List Key} {e : EE} {P : List EE} {t : Term} :
      retStmt file ret xs e = some t → usable xs dk t = true → Seg file ret xs tbl D T dk e P (.ret t)
  | op {dk dk' : List Key} {e b : EE} {P : List EE} {a : Atom} {c : Code} :
      atom file xs dk e = some (a, dk') → Seg file ret xs tbl D T dk' b P c →
      Seg file ret xs tbl D T dk e (b :: P) (.atom a c)
  | voidCall {dk : List Key} {e b : EE} {P : List EE} {c : Code} :
      VoidCall.recognize file e = true → Seg file ret xs tbl D T dk b P c →
      Seg file ret xs tbl D T dk e (b :: P) c
  | test {dk : List Key} {e yes no : EE} {P : List EE} {t : Term} {cy cn : Code} :
      TyRun.ifParts file xs e = some (t, yes, no) → usable xs dk t = true →
      TyState.Term.bool01 t = true →
      Seg file ret xs tbl D T dk no P cy → Seg file ret xs tbl D T dk yes P cn →
      Seg file ret xs tbl D T dk e P (.test false t cy cn)
  | dtest {dk : List Key} {e yes no : EE} {P : List EE} {t : Term} {cy cn : Code} :
      TyDoCondition.recognize file xs e = some (t, yes, no) → usable xs dk t = true →
      TyState.Term.bool01 t = true →
      Seg file ret xs tbl D T dk yes P cy → Seg file ret xs tbl D T dk no P cn →
      Seg file ret xs tbl D T dk e P (.test true t cy cn)
  | seq {dk : List Key} {P : List EE} {c : Code} (ann pann : List Annot) (ty : BaseType) (a b : EE) :
      Seg file ret xs tbl D T dk a (b :: P) c →
      Seg file ret xs tbl D T dk (.mk ann (.sseq (.mk pann (.base (none, ty))) a b)) P c
  | unit {dk : List Key} {b : EE} {P : List EE} {c : Code} (ann pann : List Annot) :
      Seg file ret xs tbl D T dk b P c →
      Seg file ret xs tbl D T dk (.mk ann (.pure (.mk pann () (.val .unit)))) (b :: P) c
  | save {dk : List Key} {P : List EE} {c : Code} (ann : List Annot) (l : Sym) (lty : BaseType)
      (ps : List (Sym × ((BaseType × Option (Ctype × PassBy)) × PE))) (body : EE) :
      selfParams xs ps = true → Seg file ret xs tbl D T dk body P c →
      Seg file ret xs tbl D T dk (.mk ann (.save (l, lty) ps body)) P c
  | goto {dk : List Key} {P : List EE} (ann : List Annot) (l : Sym) (args : List PE) :
      jump ret xs tbl D T dk l args = true →
      Seg file ret xs tbl D T dk (.mk ann (.run () l args)) P (.goto l.key)
  | abort {dk : List Key} {e : EE} {P : List EE} :
      AbortCall.abortStmt file e = true → Seg file ret xs tbl D T dk e P .abort
  | exit {dk : List Key} {e : EE} {P : List EE} {v : Int} :
      ExitCall.recognizeBody file e = some v → -2147483648 ≤ v ∧ v ≤ 2147483647 →
      Seg file ret xs tbl D T dk e P (.ret (.lit v))

theorem walk_seg {file : File Codec.wireModel Unit Unit} {ret : Sym} {xs : Vars}
    {tbl : List (Sym × (List Sym × EE))} {D : Key → List Key} {T : List Key} :
    (fuel : Nat) → {dk : List Key} → {e : EE} → {P : List EE} → {seen : List (Key × List Key)} →
    {c : Code} → {f : Nat} → {s : List (Key × List Key)} →
    walk file ret xs tbl D T fuel dk e P seen = some (c, f, s) → Seg file ret xs tbl D T dk e P c
  | 0, _, _, _, _, _, _, _, h => by simp [walk] at h
  | fuel + 1, dk, e, P, seen, c, f, s, h => by
    unfold walk at h
    split at h
    · rename_i hab
      cases h
      exact .abort hab
    split at h
    · rename_i v hv
      split at h
      · rename_i hr
        cases h
        exact .exit hv hr
      · cases h
    split at h
    · rename_i t ht
      split at h
      · rename_i hc
        cases h
        exact .retn ht hc
      · cases h
    · split at h
      · rename_i a dk' ha
        split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨⟨c', r⟩, h', eq⟩ := h
          cases eq
          exact .op ha (walk_seg fuel h')
        · cases h
      · split at h
        · rename_i hv
          split at h
          · exact .voidCall hv (walk_seg fuel h)
          · cases h
        · split at h
          · rename_i t yes no ht
            split at h
            · rename_i hc
              split at h
              · rename_i cy f' s' hy
                split at h
                · rename_i hlt
                  simp only [Option.map_eq_some_iff] at h
                  obtain ⟨⟨cn, r⟩, hn, eq⟩ := h
                  cases eq
                  exact .test ht hc.1 hc.2 (walk_seg fuel hy) (walk_seg f' hn)
                · cases h
              · cases h
            · cases h
          · split at h
            · rename_i t yes no ht
              split at h
              · rename_i hc
                split at h
                · rename_i cy f' s' hy
                  split at h
                  · rename_i hlt
                    simp only [Option.map_eq_some_iff] at h
                    obtain ⟨⟨cn, r⟩, hn, eq⟩ := h
                    cases eq
                    exact .dtest ht hc.1 hc.2 (walk_seg fuel hy) (walk_seg f' hn)
                  · cases h
                · cases h
              · cases h
            · split at h
              all_goals first
                | cases h
                | exact .seq _ _ _ _ _ (walk_seg fuel h)
                | (split at h
                   all_goals first
                    | exact .unit _ _ (walk_seg fuel h)
                    | (rename_i hs; exact .save _ _ _ _ _ hs (walk_seg fuel h))
                    | (rename_i hj; cases h; exact .goto _ _ _ hj)
                    | cases h)
termination_by fuel => fuel
decreasing_by all_goals omega

/-! ## The relation -/

/-- The two runs at the root of a node: Lir at its block, Core at an expression it is the code
of, with the pending statements in the frames, the slots and registers holding the definitions
`ds` of the defined slots. -/
def Rel (file : Program) (ret : Sym) (xs : Vars)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) (T : List Key)
    (bs : List (Lir.Block Mir.Reg)) (idx : Key → Nat) (mem : Lir.Memory) (ts : Lir.State Mir.Reg)
    (cs : Spec.CState) : Prop :=
  ∃ (dk : List Key) (e : EE) (P : List EE) (F : List Frame) (c : Code) (i : Nat) (env : Env)
    (m : Mem.Concrete.State) (ls : List Local) (ds : Key → Option Term)
    (fr : Lir.Frame Mir.Reg),
    Seg file ret xs tbl D T dk e P c ∧ At bs (regOf (xs.map (·.1.key))) xs.length idx i c ∧
    ts = ⟨⟨0, i, 0⟩, fr, [], mem⟩ ∧ cs = ⟨.effectExpr e env, F, m⟩ ∧ Pends ls P F ∧
    Inv env m ls ds ∧ Keys ls xs ∧ Covers dk ds ∧ Registers (regOf (xs.map (·.1.key))) ds fr ∧
    m.stdout = "" ∧ ExitCall.Budget m

/-- **A jump** to a label of the stable set: the `run` is a nonempty Core path to the label's body
under no frames, and a Lir path that reaches the label's first block relates the two runs again. -/
theorem jump_iter {ret : Sym} {xs : Vars} {tbl : List (Sym × (List Sym × EE))}
    {D : Key → List Key} {T : List Key} {bs : List (Lir.Block Mir.Reg)} {idx : Key → Nat}
    {mem : Lir.Memory}
    (hlook : ∀ s qs b, (s, qs, b) ∈ tbl → labels.lookup s = some (qs, b))
    (hcodes : ∀ s qs b, (s, qs, b) ∈ tbl → s.key ∈ T →
      ∃ c, Seg file ret xs tbl D T (D s.key) b [] c ∧
        At bs (regOf (xs.map (·.1.key))) xs.length idx (idx s.key) c)
    {dk : List Key} {l : Sym} {args : List PE} (hj : jump ret xs tbl D T dk l args = true)
    {ann : List Annot} {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option Term} {F : List Frame} {fr : Lir.Frame Mir.Reg}
    (inv : Inv env m ls ds) (keys : Keys ls xs) (cov : Covers dk ds) (hF : NoBoundary F)
    (matched : Registers (regOf (xs.map (·.1.key))) ds fr) (out : m.stdout = "")
    (hb : ExitCall.Budget m) {ts : Lir.State Mir.Reg}
    (lir : TransGen (Lir.Step (LoopLink.link bs).prog) ts ⟨⟨0, idx l.key, 0⟩, fr, [], mem⟩) :
    ∃ ts' cs', TransGen (Lir.Step (LoopLink.link bs).prog) ts ts' ∧
      TransGen (Spec.coreStep file labels) ⟨.effectExpr (.mk ann (.run () l args)) env, F, m⟩ cs' ∧
      Rel file ret xs tbl D T bs idx mem ts' cs' := by
  unfold jump at hj
  split at hj
  · rename_i ys qs b' hys hf
    obtain ⟨-, hT, hkeys, hloc, hdef⟩ := of_decide_eq_true hj
    obtain ⟨s, hmem, hsk⟩ := Cfg.find_mem hf
    have hlk : labels.lookup l = some (qs, b') := by
      rw [ReturnLit.lookup_key hsk.symm]; exact hlook s qs b' hmem
    obtain ⟨c', seg', hat'⟩ := hcodes s qs b' hmem (by rw [hsk]; exact hT)
    obtain ⟨vs, ev, rel⟩ := symArgs_evals (file := file) (labels := labels) inv keys args ys hys hloc
    have relq := forall₂_keys qs ys vs hkeys rel
    have arity : qs.length = vs.length := relq.length_eq
    have core : TransGen (Spec.coreStep file labels)
        ⟨.effectExpr (.mk ann (.run () l args)) env, F, m⟩
        ⟨.effectExpr b' (extendEnv (qs.zip vs) env), [], focusMemory ann m⟩ := by
      cases ev with
      | nil =>
        have hqs : qs = [] := List.eq_nil_of_length_eq_zero arity
        subst qs
        simpa [extendEnv] using Cfg.run_nil_strict ann l env F hF b' hlk m
      | @cons p0 v ps vs' hp rest =>
        exact Cfg.run_strict ann l env p0 ps v vs' hp rest F hF qs b' hlk arity m
    refine ⟨_, _, lir, core, ?_⟩
    refine ⟨D l.key, b', [], [], c', idx l.key, _, _, ls, ds, fr, ?_, ?_, rfl, rfl, .base rfl,
      rebinds (inv.focus ann) relq, keys, ?_, matched, by simpa using out, hb.focus ann⟩
    · rw [← hsk]; exact seg'
    · rw [← hsk]; exact hat'
    · intro q hq; exact cov q (hdef q hq)
  · cases hj

end Silmaril.Compile.Core.Verified.TyCfg
