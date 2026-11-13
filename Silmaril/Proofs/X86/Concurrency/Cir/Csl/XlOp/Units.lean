module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp.Thread
public import Silmaril.X86.MemoryModel.Xl.Thms

/-!
# The XL bridge: the units of a uniform, thread-free program

Proofs for `Csl.Task.cirXlOpAx`. Every label of such a run lowers to a short list
of **roles** (`labRoles`): a plain load or store of a cell, the two halves of a locked
read-modify-write, or a fence. Thread `i`'s units are its roles in order, the `p`-th at program
position `p` (`rolesUnits`). `H` collects what the bridge knows about a candidate execution
over these units; from it follow the shape of each unit (`H.unit`, `H.ofPos`), uniqueness of a
unit's thread and position (`H.uniq`), and the pairing of locked reads and writes
(`H.partnerR`, `H.partnerW`).
-/

@[expose] public section

-- Some `try`/`all_goals` combinators below are needed on some goals only.
set_option linter.unusedTactic false

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace Loc actUnits threadUnits accUnits units
  rmwPairs annOf)
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec Act)
open Silmaril.X86.Atomic9 (FenceKind)
open Silmaril.Proofs.X86.Concurrency.Cir.Domain (LocsFacts cellsOf threadUnits_append WfFacts
  length_natBytes)

/-! ## Roles -/

/-- What a unit does: a plain load or store of `sz` bytes at `a` with value `v`, the locked
read or write half of a read-modify-write, or a fence. -/
inductive Role where
  | ld (a sz v : Nat)
  | st (a sz v : Nat)
  | lr (a sz v : Nat)
  | lw (a sz v : Nat)
  | fn (k : FenceKind)
  deriving DecidableEq

/-- The unit of a role, of thread `i` at position `p`. -/
def Role.ev (i p : Nat) : Role → Ev
  | .ld a sz _ => { tid := i, pos := p, act := .read, addr := a, size := sz }
  | .st a sz v => { tid := i, pos := p, act := .write, addr := a, size := sz, data := natBytes v sz }
  | .lr a sz _ => { tid := i, pos := p, act := .read, addr := a, size := sz, locked := true }
  | .lw a sz v =>
    { tid := i, pos := p, act := .write, addr := a, size := sz, locked := true,
      data := natBytes v sz }
  | .fn k => { tid := i, pos := p, act := .fence k }

/-- The bytes a role's unit must read. -/
def Role.exp : Role → List Byte
  | .ld _ sz v | .lr _ sz v => natBytes v sz
  | _ => []

/-- The units of a list of roles of thread `i` from position `p`. -/
def rolesUnits (i : Nat) : Nat → List Role → List (Ev × List Byte)
  | _, [] => []
  | p, r :: rs => (r.ev i p, r.exp) :: rolesUnits i (p + 1) rs

/-- The roles of a label. -/
def labRoles : Lab → List Role
  | .rd _ _ a sz v => [.ld a sz v]
  | .wr _ _ a sz v => [.st a sz v]
  | .rmw _ a sz o n => [.lr a sz o, .lw a sz n]
  | .fence k => [.fn k]
  | .fwait a e s r =>
    if s = e then
      [.fn .mfence, .st (qAddr a) 1 1, .fn .mfence, .ld a 4 s, .lr (qAddr a) 1 r, .lw (qAddr a) 1 0]
    else [.fn .mfence, .ld a 4 s, .fn .mfence]
  | .fwake a _ q => [.fn .mfence, .lr (qAddr a) 1 q, .lw (qAddr a) 1 0, .fn .mfence]
  | .blk _ ins outs _ =>
    ins.map (fun c => .ld c.1 c.2.1 c.2.2) ++ outs.map fun c => .st c.1 c.2.1 c.2.2
  | _ => []

@[simp] theorem Role.ev_tid (i p : Nat) (r : Role) : (r.ev i p).tid = i := by cases r <;> rfl
@[simp] theorem Role.ev_pos (i p : Nat) (r : Role) : (r.ev i p).pos = p := by cases r <;> rfl

theorem rolesUnits_length (i : Nat) : ∀ (p : Nat) (rs : List Role), (rolesUnits i p rs).length = rs.length
  | _, [] => rfl
  | p, _ :: rs => by simp [rolesUnits, rolesUnits_length i (p + 1) rs]

theorem rolesUnits_append (i : Nat) : ∀ (p : Nat) (rs ts : List Role),
    rolesUnits i p (rs ++ ts) = rolesUnits i p rs ++ rolesUnits i (p + rs.length) ts
  | p, [], ts => by simp [rolesUnits]
  | p, r :: rs, ts => by
    simp only [List.cons_append, rolesUnits, List.length_cons]
    rw [rolesUnits_append i (p + 1) rs ts, show p + 1 + rs.length = p + (rs.length + 1) by omega]

theorem rolesUnits_get (i : Nat) : ∀ (p : Nat) (rs : List Role) (k : Nat) (hk : k < rs.length),
    (rolesUnits i p rs)[k]'(by rw [rolesUnits_length]; exact hk) = (rs[k].ev i (p + k), rs[k].exp)
  | p, [], k, hk => by simp at hk
  | p, r :: rs, 0, _ => by simp [rolesUnits]
  | p, r :: rs, k + 1, hk => by
    simp only [rolesUnits, List.getElem_cons_succ]
    rw [rolesUnits_get i (p + 1) rs k (by simpa using hk)]
    simp [show p + 1 + k = p + (k + 1) by omega]

theorem mem_rolesUnits {i p : Nat} {rs : List Role} {u : Ev × List Byte}
    (h : u ∈ rolesUnits i p rs) : ∃ k, ∃ hk : k < rs.length, u = (rs[k].ev i (p + k), rs[k].exp) := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  rw [rolesUnits_length] at hk
  exact ⟨k, hk, rolesUnits_get i p rs k hk⟩

theorem rolesUnits_pairwise (i : Nat) : ∀ (p : Nat) (rs : List Role),
    (rolesUnits i p rs).Pairwise fun a b => (a.1.tid, a.1.pos) ≠ (b.1.tid, b.1.pos) := by
  intro p rs
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab
  rw [rolesUnits_length] at ha hb
  rw [rolesUnits_get i p rs a ha, rolesUnits_get i p rs b hb]
  simp only [Role.ev_tid, Role.ev_pos, ne_eq, Prod.mk.injEq, true_and]
  omega

/-! ## Labels to roles -/

theorem tu_ld (i p : Nat) : ∀ (cs : List (Nat × Nat × Nat)),
    threadUnits i p (cs.map fun c => ldAct .wb c.1 c.2.1 c.2.2) =
      rolesUnits i p (cs.map fun c => .ld c.1 c.2.1 c.2.2)
  | [] => rfl
  | c :: cs => by
    simp only [List.map_cons, threadUnits, rolesUnits]
    have := tu_ld i (p + 1) cs
    simp only [actUnits, ldAct, flavOf, annOf] at this ⊢
    simp [this, Role.ev, Role.exp]

theorem tu_st (i p : Nat) : ∀ (cs : List (Nat × Nat × Nat)),
    threadUnits i p (cs.map fun c => stAct .wb c.1 c.2.1 c.2.2) =
      rolesUnits i p (cs.map fun c => .st c.1 c.2.1 c.2.2)
  | [] => rfl
  | c :: cs => by
    simp only [List.map_cons, threadUnits, rolesUnits]
    have := tu_st i (p + 1) cs
    simp only [actUnits, stAct, flavOf, annOf] at this ⊢
    simp [this, Role.ev, Role.exp]

theorem tu_length (i p : Nat) (as : List XAct) (rs : List Role) (h : threadUnits i p as = rolesUnits i p rs) :
    (threadUnits i p as).length = rs.length := by rw [h, rolesUnits_length]

/-- **A label's units are its roles' units.** -/
theorem tu_lab (i p : Nat) {l : Lab} (hl : LabG l) : threadUnits i p l.acts = rolesUnits i p (labRoles l) := by
  cases l with
  | rd m fl a sz v =>
    simp only [LabG] at hl; subst hl
    simp [Lab.acts, labRoles, threadUnits, actUnits, ldAct, flavOf, annOf, rolesUnits, Role.ev, Role.exp]
  | wr m fl a sz v =>
    simp only [LabG] at hl; subst hl
    simp [Lab.acts, labRoles, threadUnits, actUnits, stAct, flavOf, annOf, rolesUnits, Role.ev, Role.exp]
  | rmw m a sz o n =>
    simp [Lab.acts, labRoles, threadUnits, actUnits, rmwAct, annOf, rolesUnits, Role.ev, Role.exp]
  | fence k => simp [Lab.acts, labRoles, threadUnits, actUnits, fenceAct, rolesUnits, Role.ev, Role.exp]
  | fwait a e s r =>
    simp only [Lab.acts, labRoles]
    split <;> simp [threadUnits, actUnits, rmwAct, ldAct, stAct, fenceAct, flavOf, annOf, rolesUnits,
      Role.ev, Role.exp]
  | fwake a n q =>
    simp [Lab.acts, labRoles, threadUnits, actUnits, rmwAct, fenceAct, annOf, rolesUnits, Role.ev,
      Role.exp]
  | fblock a e => simp [LabG] at hl
  | spawn t => simp [LabG] at hl
  | join t => simp [LabG] at hl
  | blk nm ins outs rvs =>
    simp only [Lab.acts, labRoles]
    rw [threadUnits_append, rolesUnits_append, tu_ld, tu_st, rolesUnits_length]

theorem tu_labs (i : Nat) : ∀ (p : Nat) (L : List Lab), (∀ l ∈ L, LabG l) →
    threadUnits i p (L.flatMap Lab.acts) = rolesUnits i p (L.flatMap labRoles)
  | p, [], _ => rfl
  | p, l :: L, h => by
    simp only [List.flatMap_cons]
    rw [threadUnits_append, rolesUnits_append, tu_lab i p (h l List.mem_cons_self),
      rolesUnits_length, tu_labs i _ L fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]

/-! ## Locked pairs within a label -/

theorem blk_roles {nm : String} {ins outs : List (Nat × Nat × Nat)} {rvs : List Nat} {r : Role}
    (h : r ∈ labRoles (.blk nm ins outs rvs)) : (∃ a sz v, r = .ld a sz v) ∨ ∃ a sz v, r = .st a sz v := by
  simp only [labRoles, List.mem_append, List.mem_map] at h
  rcases h with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
  · exact .inl ⟨_, _, _, rfl⟩
  · exact .inr ⟨_, _, _, rfl⟩

/-- A locked read is followed, in its label, by the locked write of the same cell. -/
theorem roles_lr {l : Lab} {k a sz v : Nat} (h : (labRoles l)[k]? = some (.lr a sz v)) :
    ∃ w, (labRoles l)[k + 1]? = some (.lw a sz w) := by
  cases l with
  | blk nm ins outs rvs =>
    rcases blk_roles (List.mem_of_getElem? h) with ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ <;> cases he
  | fwait a' e s r =>
    simp only [labRoles] at h ⊢
    split at h <;> simp only [↓reduceIte, *] at h ⊢
    all_goals rcases k with _ | _ | _ | _ | _ | _ | k
    all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
      Role.lr.injEq, Role.lw.injEq, reduceCtorEq, List.getElem?_nil] at h ⊢
    all_goals (try obtain ⟨rfl, rfl, rfl⟩ := h)
    all_goals simp
  | _ =>
    simp only [labRoles] at h ⊢
    rcases k with _ | _ | _ | _ | k
    all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
      Role.lr.injEq, Role.lw.injEq, reduceCtorEq, List.getElem?_nil] at h ⊢
    all_goals (try obtain ⟨rfl, rfl, rfl⟩ := h)
    all_goals simp

/-- A locked write is preceded, in its label, by the locked read of the same cell. -/
theorem roles_lw {l : Lab} {k a sz v : Nat} (h : (labRoles l)[k]? = some (.lw a sz v)) :
    ∃ k', k = k' + 1 ∧ ∃ w, (labRoles l)[k']? = some (.lr a sz w) := by
  cases l with
  | blk nm ins outs rvs =>
    rcases blk_roles (List.mem_of_getElem? h) with ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ <;> cases he
  | fwait a' e s r =>
    simp only [labRoles] at h ⊢
    split at h <;> simp only [↓reduceIte, *] at h ⊢
    all_goals rcases k with _ | _ | _ | _ | _ | _ | k
    all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
      Role.lw.injEq, reduceCtorEq, List.getElem?_nil] at h ⊢
    all_goals (try obtain ⟨rfl, rfl, rfl⟩ := h)
    all_goals simp
  | _ =>
    simp only [labRoles] at h ⊢
    rcases k with _ | _ | _ | _ | k
    all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
      Role.lw.injEq, reduceCtorEq, List.getElem?_nil] at h ⊢
    all_goals (try obtain ⟨rfl, rfl, rfl⟩ := h)
    all_goals simp


/-! ## The hypotheses -/

/-- The roles of thread `i`, in program order. -/
def RL (L : Nat → List Lab) (i : Nat) : List Role := (L i).flatMap labRoles

/-- The expected bytes of unit `u`. -/
def ex (U : List (Ev × List Byte)) (u : Nat) : List Byte := (U.map Prod.snd).getD u []

/-- What the bridge knows about a candidate `x` over the units `U` of the runs `L` of a uniform,
thread-free program `P`. -/
structure H (P : Prog) (L : Nat → List Lab) (x : Exec) (U : List (Ev × List Byte)) : Prop where
  lf : LocsFacts P.locs
  lout : ∀ i, P.threads.length ≤ i → L i = []
  lab : ∀ i, ∀ l ∈ L i, LabG l ∧
    ∃ bs, Silmaril.Proofs.X86.Concurrency.Cir.Domain.LabOk (cellsOf P.locs) bs l
  ueq : U = ((List.range P.threads.length).map fun i => rolesUnits i 0 (RL L i)).flatten
  evs : x.evs = U.map Prod.fst
  rmw : x.rmw = rmwPairs (U.map Prod.fst)
  wf : WfFacts x
  cells : Silmaril.X86.MemoryModel.Litmus.cellsOk x.evs = true
  tso : x.Tso
  reads : ∀ r < x.n, (x.evN r).isR = true → x.readBytes P.memTest.initB r = ex U r

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)}

theorem H.memU (h : H P L x U) {u : Ev × List Byte} :
    u ∈ U ↔ ∃ i < P.threads.length, u ∈ rolesUnits i 0 (RL L i) := by
  rw [h.ueq]; simp [List.mem_flatten, List.mem_map, List.mem_range]

theorem H.pw (h : H P L x U) : U.Pairwise fun a b => (a.1.tid, a.1.pos) ≠ (b.1.tid, b.1.pos) := by
  rw [h.ueq, List.pairwise_flatten]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hl
    exact rolesUnits_pairwise i 0 _
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_range).imp ?_
    intro i j hij a ha b hb
    obtain ⟨k, hk, rfl⟩ := mem_rolesUnits ha
    obtain ⟨k', hk', rfl⟩ := mem_rolesUnits hb
    simp only [Role.ev_tid, Role.ev_pos, ne_eq, Prod.mk.injEq, not_and]
    omega

theorem H.n_eq (h : H P L x U) : x.n = U.length := by simp [Exec.n, h.evs]

theorem H.evN_eq (h : H P L x U) {u : Nat} (hu : u < U.length) : x.evN u = (U[u]).1 := by
  simp [Exec.evN, h.evs, List.getD_eq_getElem?_getD, hu]

theorem ex_eq {u : Nat} (hu : u < U.length) : ex U u = U[u].2 := by
  simp [ex, List.getD_eq_getElem?_getD, hu]

/-- Units are determined by their thread and position. -/
theorem H.uniq (h : H P L x U) {a b : Nat} (ha : a < x.n) (hb : b < x.n)
    (ht : (x.evN a).tid = (x.evN b).tid) (hp : (x.evN a).pos = (x.evN b).pos) : a = b := by
  have hpw := h.pw
  rw [List.pairwise_iff_getElem] at hpw
  rw [h.n_eq] at ha hb
  rw [h.evN_eq ha, h.evN_eq hb] at ht hp
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact hpw a b ha hb hlt (by rw [ht, hp])
  · exact hpw b a hb ha hlt (by rw [ht, hp])

/-- **Every unit is a role of its thread**, at its position. -/
theorem H.unit (h : H P L x U) {u : Nat} (hu : u < x.n) :
    ∃ i < P.threads.length, ∃ p, ∃ hp : p < (RL L i).length,
      x.evN u = (RL L i)[p].ev i p ∧ ex U u = (RL L i)[p].exp := by
  rw [h.n_eq] at hu
  obtain ⟨i, hi, hm⟩ := h.memU.mp (List.getElem_mem hu)
  obtain ⟨k, hk, he⟩ := mem_rolesUnits hm
  refine ⟨i, hi, k, hk, ?_, ?_⟩
  · rw [h.evN_eq hu, he]; simp
  · rw [ex_eq hu, he]

/-- **Every role is a unit.** -/
theorem H.ofPos (h : H P L x U) {i p : Nat} (hi : i < P.threads.length) (hp : p < (RL L i).length) :
    ∃ u < x.n, x.evN u = (RL L i)[p].ev i p ∧ ex U u = (RL L i)[p].exp := by
  have hm : ((RL L i)[p].ev i p, (RL L i)[p].exp) ∈ U := by
    refine h.memU.mpr ⟨i, hi, ?_⟩
    have := List.getElem_mem (l := rolesUnits i 0 (RL L i)) (by rw [rolesUnits_length]; exact hp)
    rw [rolesUnits_get i 0 _ p hp] at this
    simpa using this
  obtain ⟨u, hu, hue⟩ := List.getElem_of_mem hm
  refine ⟨u, by rw [h.n_eq]; exact hu, ?_, ?_⟩
  · rw [h.evN_eq hu, hue]
  · rw [ex_eq hu, hue]

/-- The index of the unit of thread `i` at position `p`. -/
def pidx (x : Exec) (i p : Nat) : Nat := x.evs.findIdx fun e => e.tid == i && e.pos == p

theorem H.pidx_eq (h : H P L x U) {u : Nat} (hu : u < x.n) :
    pidx x (x.evN u).tid (x.evN u).pos = u := by
  set q := (fun e : Ev => e.tid == (x.evN u).tid && e.pos == (x.evN u).pos) with hq
  have hex : ∃ e ∈ x.evs, q e = true :=
    ⟨x.evN u, by
      simp only [Exec.evN, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem hu]; simp, by simp [hq]⟩
  have hlt : x.evs.findIdx q < x.evs.length := List.findIdx_lt_length_of_exists hex
  have hp := List.findIdx_getElem (w := hlt)
  simp only [hq, Bool.and_eq_true, beq_iff_eq] at hp
  have hev : x.evN (pidx x (x.evN u).tid (x.evN u).pos) = x.evs[x.evs.findIdx q] := by
    show x.evs.getD (x.evs.findIdx q) _ = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
  exact h.uniq hlt hu (by rw [hev]; exact hp.1) (by rw [hev]; exact hp.2)

/-- The unit of thread `i` at position `p`. -/
theorem H.atPos (h : H P L x U) {i p : Nat} (hi : i < P.threads.length) (hp : p < (RL L i).length) :
    pidx x i p < x.n ∧ x.evN (pidx x i p) = (RL L i)[p].ev i p ∧
      ex U (pidx x i p) = (RL L i)[p].exp := by
  obtain ⟨u, hu, he, hx⟩ := h.ofPos hi hp
  have := h.pidx_eq hu
  rw [he, Role.ev_tid, Role.ev_pos] at this
  rw [this]; exact ⟨hu, he, hx⟩

theorem H.tid_lt (h : H P L x U) {u : Nat} (hu : u < x.n) : (x.evN u).tid < P.threads.length := by
  obtain ⟨i, hi, p, hp, he, -⟩ := h.unit hu
  rw [he, Role.ev_tid]; exact hi

theorem H.pos_lt (h : H P L x U) {u : Nat} (hu : u < x.n) :
    (x.evN u).pos < (RL L (x.evN u).tid).length := by
  obtain ⟨i, hi, p, hp, he, -⟩ := h.unit hu
  rw [he, Role.ev_tid, Role.ev_pos]; exact hp

/-- The unit and its role, at its own thread and position. -/
theorem H.role (h : H P L x U) {u : Nat} (hu : u < x.n) :
    x.evN u = ((RL L (x.evN u).tid)[(x.evN u).pos]'(h.pos_lt hu)).ev (x.evN u).tid (x.evN u).pos ∧
      ex U u = ((RL L (x.evN u).tid)[(x.evN u).pos]'(h.pos_lt hu)).exp := by
  obtain ⟨i, hi, p, hp, he, hx⟩ := h.unit hu
  have ht : (x.evN u).tid = i := by rw [he, Role.ev_tid]
  have hpp : (x.evN u).pos = p := by rw [he, Role.ev_pos]
  simp only [ht, hpp]
  exact ⟨he, hx⟩

end

/-! ## Labels and positions -/

/-- The position of the first unit of label `c` of thread `i`. -/
def base (L : Nat → List Lab) (i c : Nat) : Nat := (((L i).take c).flatMap labRoles).length

theorem base_succ {L : Nat → List Lab} {i c : Nat} (hc : c < (L i).length) :
    base L i (c + 1) = base L i c + (labRoles (L i)[c]).length := by
  simp only [base, List.take_add_one, List.getElem?_eq_getElem hc, Option.toList_some,
    List.flatMap_append, List.length_append, List.flatMap_singleton]

theorem base_mono {L : Nat → List Lab} {i c c' : Nat} (h : c ≤ c') : base L i c ≤ base L i c' := by
  unfold base
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.flatMap_append, List.length_append]; omega

theorem base_le {L : Nat → List Lab} {i c : Nat} : base L i c ≤ (RL L i).length := by
  unfold base RL
  conv_rhs => rw [← List.take_append_drop c (L i)]
  rw [List.flatMap_append, List.length_append]; omega

theorem RL_get {L : Nat → List Lab} {i c k : Nat} (hc : c < (L i).length)
    (hk : k < (labRoles (L i)[c]).length) :
    ∃ h : base L i c + k < (RL L i).length, (RL L i)[base L i c + k] = (labRoles (L i)[c])[k] := by
  have hsplit : RL L i = ((L i).take c).flatMap labRoles ++
      (labRoles (L i)[c] ++ ((L i).drop (c + 1)).flatMap labRoles) := by
    unfold RL
    conv_lhs => rw [← List.take_append_drop c (L i), List.drop_eq_getElem_cons hc]
    rw [List.flatMap_append, List.flatMap_cons]
  have hlen : base L i c + k < (RL L i).length := by
    rw [hsplit]; simp only [base, List.length_append] at *; omega
  refine ⟨hlen, ?_⟩
  simp only [hsplit, base]
  rw [List.getElem_append_right (by omega), List.getElem_append_left (by simp; omega)]
  simp

/-- **Every position lies in one label.** -/
theorem pos_lab {L : Nat → List Lab} {i p : Nat} (hp : p < (RL L i).length) :
    ∃ c, ∃ hc : c < (L i).length, ∃ k, k < (labRoles (L i)[c]).length ∧ p = base L i c + k := by
  -- the last label whose base is at most `p`
  have key : ∀ c ≤ (L i).length, base L i c ≤ p → ∃ c', ∃ hc : c' < (L i).length,
      ∃ k, k < (labRoles (L i)[c']).length ∧ p = base L i c' + k := by
    intro c hc hb
    induction h : (L i).length - c generalizing c with
    | zero =>
      exfalso
      have : c = (L i).length := by omega
      subst this
      have : base L i (L i).length = (RL L i).length := by simp [base, RL, List.take_length]
      omega
    | succ d ih =>
      have hcl : c < (L i).length := by omega
      by_cases hn : p < base L i (c + 1)
      · rw [base_succ hcl] at hn
        exact ⟨c, hcl, p - base L i c, by omega, by omega⟩
      · exact ih (c + 1) (by omega) (by omega) (by omega)
  exact key 0 (Nat.zero_le _) (by simp [base])

/-- Labels occupy disjoint position ranges. -/
theorem lab_unique {L : Nat → List Lab} {i c c' k k' : Nat} (hc : c < (L i).length)
    (hc' : c' < (L i).length) (hk : k < (labRoles (L i)[c]).length)
    (hk' : k' < (labRoles (L i)[c']).length) (he : base L i c + k = base L i c' + k') :
    c = c' ∧ k = k' := by
  rcases Nat.lt_trichotomy c c' with h | rfl | h
  · have := base_mono (L := L) (i := i) (show c + 1 ≤ c' by omega)
    rw [base_succ hc] at this; omega
  · exact ⟨rfl, by omega⟩
  · have := base_mono (L := L) (i := i) (show c' + 1 ≤ c by omega)
    rw [base_succ hc'] at this; omega

/-- Units of earlier labels come earlier. -/
theorem lab_lt {L : Nat → List Lab} {i c c' k k' : Nat} (hc : c < (L i).length)
    (hk : k < (labRoles (L i)[c]).length) (hcc : c < c') : base L i c + k < base L i c' + k' := by
  have := base_mono (L := L) (i := i) (show c + 1 ≤ c' by omega)
  rw [base_succ hc] at this; omega

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp
