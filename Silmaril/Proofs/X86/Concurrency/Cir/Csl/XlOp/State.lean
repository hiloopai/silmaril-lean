module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp.Clock

/-!
# The XL bridge: the machine state at each tick, in closed form

Proofs for `Csl.Task.cirXlOpAx`. At tick `T`, when thread `i` has executed its
first `cnt i` labels, the CIR-native store-buffer configuration is `cfg`:

* thread `i` is in the state `S i (cnt i)` of its run's cut;
* each location's cell holds the value of the coherence-last write whose block started before
  `T` (`nMem`), else its initial value;
* thread `i`'s buffer holds the native stores of its executed labels whose clock is not before
  `T`, oldest first, with each `sfence` barrier behind them (`nBuf`; barriers at the front are
  flushed at once).

`H.readOK` is the heart: a read of a location's cell by a thread that has executed exactly the
labels before it sees, at any tick from its own clock on at which no write it reads before is
visible yet (`NI`), the value the candidate's `rf` gives it.
-/

@[expose] public section

-- Some `try`/`all_goals` combinators below are needed on some goals only.
set_option linter.unusedTactic false

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte Loc)
open Silmaril.Proofs.X86.Concurrency.Cir.Domain (covers_iff WfFacts mem_touched natBytes_succ
  length_natBytes natBytes_inj cellsOf LocsFacts)
open Relation

/-! ## Values -/

/-- The little-endian value of a list of bytes. -/
def bval : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bval bs

theorem bval_natBytes : ∀ (sz v : Nat), v < 2 ^ (8 * sz) → bval (natBytes v sz) = v
  | 0, v, h => by simp at h; subst h; simp [natBytes, bval]
  | sz + 1, v, h => by
    rw [natBytes_succ, bval, bval_natBytes sz (v / 256) (by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      calc v < 2 ^ (8 * (sz + 1)) := h
        _ = 2 ^ (8 * sz) * 256 := by rw [Nat.mul_succ, Nat.pow_add])]
    simp only [BitVec.toNat_ofNat]
    omega

/-- The value a write unit writes. -/
def wval (x : Exec) (w : Nat) : Nat := bval (x.evN w).data

/-! ## Native stores and triggers of a label -/

/-- Indexed cells: the offset, address and value of each cell from offset `k`. -/
def idxd : Nat → List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | _, [] => []
  | k, c :: cs => (k, c.1, c.2.2) :: idxd (k + 1) cs

/-- The native (buffered) stores of a label: offset, cell and value. -/
def nsts : Lab → List (Nat × Nat × Nat)
  | .wr _ _ a _ v => [(0, a, v)]
  | .blk _ ins outs _ => idxd ins.length outs
  | _ => []

/-- The trigger of a label: the offset of the unit at whose tick it runs (`none`: it runs when
its thread catches up). -/
def trig : Lab → Option Nat
  | .rd .. => some 0
  | .rmw .. => some 0
  | .fwait _ e s _ => if s = e then some 3 else some 1
  | .fwake .. => some 1
  | .blk _ ins _ _ => if ins = [] then none else some (ins.length - 1)
  | _ => none

theorem mem_idxd : ∀ (k : Nat) (cs : List (Nat × Nat × Nat)) (e : Nat × Nat × Nat),
    e ∈ idxd k cs ↔ ∃ j, ∃ hj : j < cs.length, e = (k + j, cs[j].1, cs[j].2.2)
  | k, [], e => by simp [idxd]
  | k, c :: cs, e => by
    simp only [idxd, List.mem_cons, mem_idxd (k + 1) cs e, List.length_cons]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · exact ⟨j + 1, by omega, by simp [Nat.add_assoc, Nat.add_comm 1 j]⟩
    · rintro ⟨j, hj, rfl⟩
      rcases j with _ | j
      · exact .inl (by simp)
      · exact .inr ⟨j, by omega, by simp [Nat.add_assoc, Nat.add_comm 1 j]⟩

theorem idxd_pairwise : ∀ (k : Nat) (cs : List (Nat × Nat × Nat)),
    (idxd k cs).Pairwise fun a b => a.1 < b.1
  | k, [] => by simp [idxd]
  | k, c :: cs => by
    simp only [idxd, List.pairwise_cons]
    refine ⟨fun e he => ?_, idxd_pairwise (k + 1) cs⟩
    obtain ⟨j, -, rfl⟩ := (mem_idxd _ _ _).mp he
    simp only; omega

theorem nsts_pairwise (l : Lab) : (nsts l).Pairwise fun a b => a.1 < b.1 := by
  cases l <;> simp [nsts, idxd_pairwise]

/-- A native store is a store role of its label. -/
theorem nsts_role {l : Lab} {e : Nat × Nat × Nat} (he : e ∈ nsts l) :
    ∃ hk : e.1 < (labRoles l).length, ∃ sz, (labRoles l)[e.1] = .st e.2.1 sz e.2.2 := by
  cases l with
  | wr m fl a sz v =>
    simp only [nsts, List.mem_singleton] at he; subst he
    exact ⟨by simp [labRoles], sz, by simp [labRoles]⟩
  | blk nm ins outs rvs =>
    simp only [nsts] at he
    obtain ⟨j, hj, rfl⟩ := (mem_idxd _ _ _).mp he
    refine ⟨by simp [labRoles]; omega, outs[j].2.1, ?_⟩
    simp only [labRoles]
    rw [List.getElem_append_right (by simp)]
    simp
  | _ => simp [nsts] at he

/-- A store role below the ghost bytes is a native store. -/
theorem role_nsts {l : Lab} {k a sz v : Nat} (hk : k < (labRoles l).length)
    (h : (labRoles l)[k] = .st a sz v) (ha : a < ctlAddr 0) : (k, a, v) ∈ nsts l := by
  cases l with
  | wr m fl a' sz' v' =>
    simp only [labRoles, List.length_singleton] at hk
    obtain rfl : k = 0 := by omega
    simp only [labRoles, List.getElem_singleton, Role.st.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [nsts]
  | blk nm ins outs rvs =>
    simp only [nsts, mem_idxd]
    simp only [labRoles, List.length_append, List.length_map] at hk h
    by_cases hki : k < ins.length
    · rw [List.getElem_append_left (by simpa using hki)] at h; simp at h
    · rw [List.getElem_append_right (by simpa using hki)] at h
      simp only [List.getElem_map, Role.st.injEq] at h
      obtain ⟨h1, -, h3⟩ := h
      refine ⟨k - ins.length, by omega, ?_⟩
      simp [← h1, ← h3]; omega
  | fwait a' e s r =>
    have hq : ctlAddr 0 ≤ qAddr a' := Silmaril.Proofs.X86.Concurrency.Cir.Domain.ghost_q a'
    have hm := List.getElem_mem hk
    rw [h] at hm
    simp only [labRoles] at hm
    split at hm
    all_goals simp at hm
    all_goals omega
  | _ =>
    have hm := List.getElem_mem hk
    rw [h] at hm
    simp [labRoles] at hm


/-- Within a label, no write of a location's cell precedes a read. -/
theorem roles_write_after {l : Lab} {j k : Nat} (hjk : j < k) (hk : k < (labRoles l).length)
    {a sz v : Nat} (hw : (labRoles l)[j] = .st a sz v ∨ (labRoles l)[j] = .lw a sz v)
    (ha : a < ctlAddr 0) {b sz' v' : Nat}
    (hr : (labRoles l)[k] = .ld b sz' v' ∨ (labRoles l)[k] = .lr b sz' v') : False := by
  have hj : j < (labRoles l).length := by omega
  cases l with
  | blk nm ins outs rvs =>
    simp only [labRoles, List.length_append, List.length_map] at hk hj hw hr
    by_cases hki : k < ins.length
    · by_cases hji : j < ins.length
      · rw [List.getElem_append_left (by simpa using hji)] at hw; simp at hw
      · omega
    · rw [List.getElem_append_right (by simpa using hki)] at hr; simp at hr
  | fwait a' e s r =>
    have hq : ctlAddr 0 ≤ qAddr a' := Silmaril.Proofs.X86.Concurrency.Cir.Domain.ghost_q a'
    simp only [labRoles] at hk hj hw hr
    split at hk <;> simp only [List.length_cons, List.length_nil] at hk hj <;>
      rename_i hse <;> simp only [hse, ↓reduceIte] at hw hr <;>
      rcases j with _ | _ | _ | _ | _ | _ | j <;> simp_all <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp_all <;> omega
  | fwake a' n q =>
    have hq : ctlAddr 0 ≤ qAddr a' := Silmaril.Proofs.X86.Concurrency.Cir.Domain.ghost_q a'
    simp only [labRoles, List.length_cons, List.length_nil] at hk hj hw hr
    rcases j with _ | _ | _ | _ | j <;> simp_all <;>
      rcases k with _ | _ | _ | _ | k <;> simp_all <;> omega
  | rmw m a' sz'' o n =>
    simp only [labRoles, List.length_cons, List.length_nil] at hk hj hw hr
    rcases j with _ | _ | j <;> rcases k with _ | _ | k <;> simp_all <;> omega
  | rd => simp only [labRoles, List.length_singleton] at hk; omega
  | wr => simp only [labRoles, List.length_singleton] at hk; omega
  | fence => simp only [labRoles, List.length_singleton] at hk; omega
  | _ => simp [labRoles] at hk

/-! ## The configuration at a tick -/

/-- Write unit `w` covers byte `a` and its block started before tick `T`. -/
noncomputable def vis (x : Exec) (T a w : Nat) : Bool :=
  decide (w < x.n) && (x.evN w).isW && (x.evN w).covers a && decide (κ x (fstU x w) < T)

/-- The value of the cell at `a` at tick `T` (`none`: no write yet). -/
noncomputable def cval (x : Exec) (T a : Nat) : Option Nat :=
  (((x.co a).filter (vis x T a)).getLast?).map (wval x)

/-- **The memory at tick `T`.** -/
noncomputable def nMem (P : Prog) (x : Exec) (T : Nat) : Heap := fun a =>
  (P.locs.find? fun l => l.addr == a).map fun l => (cval x T a).getD l.init

/-- The buffer entries of label `c` of thread `i` at tick `T`, tagged with their positions. -/
noncomputable def labEnts (L : Nat → List Lab) (x : Exec) (T i c : Nat) : List (Nat × Ent) :=
  match (L i)[c]? with
  | none => []
  | some l =>
    if l = .fence .sfence then [(base L i c, .bar)] else
      ((nsts l).filter fun e => decide (T ≤ κ x (pidx x i (base L i c + e.1)))).map
        fun e => (base L i c + e.1, .st e.2.1 e.2.2 false)

/-- The tagged entries of thread `i`'s executed labels. -/
noncomputable def rawP (L : Nat → List Lab) (x : Exec) (T : Nat) (cnt : Nat → Nat) (i : Nat) :
    List (Nat × Ent) :=
  (List.range (cnt i)).flatMap (labEnts L x T i)

/-- **Thread `i`'s buffer at tick `T`**: leading barriers are flushed. -/
noncomputable def nBuf (L : Nat → List Lab) (x : Exec) (T : Nat) (cnt : Nat → Nat) (i : Nat) : List Ent :=
  ((rawP L x T cnt i).map Prod.snd).dropWhile (· == .bar)

/-- **The configuration at tick `T`** when thread `i` has executed `cnt i` labels. -/
noncomputable def cfg (P : Prog) (L : Nat → List Lab) (x : Exec) (S : Nat → Nat → Stmt × Regs) (T : Nat)
    (cnt : Nat → Nat) : OCfg :=
  ⟨fun i => S i (cnt i), nMem P x T, nBuf L x T cnt⟩

/-! ## Newest buffered values -/

theorem newest_append (a : Nat) : ∀ (l₁ l₂ : List Ent),
    newest (l₁ ++ l₂) a = (newest l₂ a).or (newest l₁ a)
  | [], l₂ => by simp [newest]
  | e :: l₁, l₂ => by
    simp only [List.cons_append, newest, newest_append a l₁ l₂, Option.or_assoc]

theorem newest_none {a : Nat} : ∀ {l : List Ent}, (∀ e ∈ l, e.val a = none) → newest l a = none
  | [], _ => rfl
  | e :: l, h => by
    simp only [newest, newest_none fun e' he' => h e' (List.mem_cons_of_mem _ he'),
      h e List.mem_cons_self, Option.or_none]

theorem newest_dropWhile (a : Nat) : ∀ (l : List Ent),
    newest (l.dropWhile (· == .bar)) a = newest l a
  | [] => rfl
  | e :: l => by
    simp only [List.dropWhile_cons]
    split
    · rename_i he
      simp only [beq_iff_eq] at he; subst he
      rw [newest_dropWhile a l]; simp [newest, Ent.val]
    · rfl

theorem newest_sorted {a v : Nat} {wk : Bool} {l : List (Nat × Ent)}
    (hs : l.Pairwise fun p q => p.1 < q.1) {q : Nat × Ent} (hq : q ∈ l) (hqe : q.2 = .st a v wk)
    (hmax : ∀ q' ∈ l, (q'.2.val a).isSome → q'.1 ≤ q.1) : newest (l.map Prod.snd) a = some v := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hq
  rw [List.pairwise_append, List.pairwise_cons] at hs
  have h2 : newest (l₂.map Prod.snd) a = none := by
    apply newest_none
    intro e he
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp he
    cases hv : q'.2.val a with
    | none => rfl
    | some _ =>
      have := hmax q' (List.mem_append_right _ (List.mem_cons_of_mem _ hq')) (by simp [hv])
      have := hs.2.1.1 q' hq'
      omega
  simp only [List.map_append, List.map_cons, newest_append, newest, h2, hqe, Ent.val, ↓reduceIte,
    Option.none_or, Option.some_or]

theorem dropWhile_nil_of {l : List Ent} (h : ∀ e ∈ l, e = .bar) : l.dropWhile (· == .bar) = [] := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.dropWhile_cons, h e List.mem_cons_self, beq_self_eq_true, ↓reduceIte]
    exact ih fun e' he' => h e' (List.mem_cons_of_mem _ he')


/-! ## Cells of roles -/

/-- A role on a location's cell (with a value that fits) or on a ghost byte. -/
def RoleOk (cs : List (Nat × Nat)) : Role → Prop
  | .ld a sz v | .st a sz v | .lr a sz v | .lw a sz v =>
    ((a, sz) ∈ cs ∧ v < 2 ^ (8 * sz)) ∨ (sz = 1 ∧ ctlAddr 0 ≤ a)
  | .fn _ => True

theorem labRoles_ok {cs : List (Nat × Nat)} {bs : List Block} {l : Lab}
    (hl : Silmaril.Proofs.X86.Concurrency.Cir.Domain.LabOk cs bs l) :
    ∀ r ∈ labRoles l, RoleOk cs r := by
  have hq := Silmaril.Proofs.X86.Concurrency.Cir.Domain.ghost_q
  intro r hr
  cases l with
  | rd => simp only [labRoles, List.mem_singleton] at hr; subst hr; exact .inl hl
  | wr => simp only [labRoles, List.mem_singleton] at hr; subst hr; exact .inl hl
  | rmw m a sz o n =>
    simp only [labRoles, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨hl.1, hl.2.1⟩
    · exact .inl ⟨hl.1, hl.2.2⟩
  | fence => simp only [labRoles, List.mem_singleton] at hr; subst hr; trivial
  | fwait a e s q =>
    simp only [labRoles] at hr
    split at hr <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | trivial | exact .inr ⟨rfl, hq _⟩ | exact .inl ⟨hl.1, hl.2.1⟩
  | fwake a n q =>
    simp only [labRoles, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> first | trivial | exact .inr ⟨rfl, hq _⟩
  | blk nm ins outs rvs =>
    simp only [labRoles, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · exact .inl (hl.1 c (List.mem_append_left _ hc))
    · exact .inl (hl.1 c (List.mem_append_right _ hc))
  | _ => simp [labRoles] at hr

/-! ## Units with their labels -/

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)}

/-- A unit, its label and its role. -/
theorem H.labOf (h : H P L x U) {u : Nat} (hu : u < x.n) :
    ∃ c, ∃ hc : c < (L (x.evN u).tid).length, ∃ k, ∃ hk : k < (labRoles (L (x.evN u).tid)[c]).length,
      (x.evN u).pos = base L (x.evN u).tid c + k ∧
      x.evN u = ((labRoles (L (x.evN u).tid)[c])[k]).ev (x.evN u).tid (x.evN u).pos ∧
      ex U u = ((labRoles (L (x.evN u).tid)[c])[k]).exp := by
  obtain ⟨he, hx⟩ := h.role hu
  obtain ⟨c, hc, k, hk, hp⟩ := pos_lab (h.pos_lt hu)
  obtain ⟨_, hget⟩ := RL_get (L := L) hc hk
  refine ⟨c, hc, k, hk, hp, ?_, ?_⟩
  · conv_lhs => rw [he]
    simp only [hp, hget]
  · rw [hx]; simp only [hp, hget]

/-- The unit of label `c`, offset `k`, of thread `i`. -/
theorem H.at (h : H P L x U) {i c k : Nat} (hi : i < P.threads.length) (hc : c < (L i).length)
    (hk : k < (labRoles (L i)[c]).length) :
    pidx x i (base L i c + k) < x.n ∧
      x.evN (pidx x i (base L i c + k)) = ((labRoles (L i)[c])[k]).ev i (base L i c + k) ∧
      ex U (pidx x i (base L i c + k)) = ((labRoles (L i)[c])[k]).exp := by
  obtain ⟨hp, hget⟩ := RL_get (L := L) hc hk
  obtain ⟨h1, h2, h3⟩ := h.atPos hi hp
  rw [hget] at h2 h3
  exact ⟨h1, h2, h3⟩

theorem H.roleOk (h : H P L x U) {i c k : Nat} (hc : c < (L i).length)
    (hk : k < (labRoles (L i)[c]).length) :
    RoleOk (cellsOf P.locs) ((labRoles (L i)[c])[k]) := by
  obtain ⟨-, bs, hok⟩ := h.lab i _ (List.getElem_mem hc)
  exact labRoles_ok hok _ (List.getElem_mem hk)

theorem H.coMem (h : H P L x U) {u y w : Nat} (hu : u < x.n) (huM : (x.evN u).isM = true)
    (hcu : (x.evN u).covers y = true) (hw : w ∈ x.co y) :
    w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true := by
  have ht : y ∈ x.touched := mem_touched.mpr ⟨x.evN u, by rw [h.evs_get hu]; exact List.getElem_mem _,
    huM, by rw [Silmaril.Proofs.X86.Concurrency.Cir.Domain.mem_bytes]; rwa [covers_iff] at hcu⟩
  obtain ⟨hn, hW, hC⟩ := h.wf.coMem y ht w hw
  have hev : x.ev ⟨w, hn⟩ = x.evN w := by rw [h.evs_get hn]; rfl
  rw [hev] at hW hC
  exact ⟨hn, hW, hC⟩

theorem H.coNodup (h : H P L x U) {u y : Nat} (hu : u < x.n) (huM : (x.evN u).isM = true)
    (hcu : (x.evN u).covers y = true) : (x.co y).Nodup :=
  h.wf.coNodup y (mem_touched.mpr ⟨x.evN u, by rw [h.evs_get hu]; exact List.getElem_mem _,
    huM, by rw [Silmaril.Proofs.X86.Concurrency.Cir.Domain.mem_bytes]; rwa [covers_iff] at hcu⟩)

theorem H.dataLen (h : H P L x U) {w : Nat} (hw : w < x.n) (hW : (x.evN w).isW = true) :
    (x.evN w).data.length = (x.evN w).size := by
  obtain ⟨i, hi, p, hp, he, -⟩ := h.unit hw
  rw [he] at hW ⊢
  generalize (RL L i)[p] = r at hW ⊢
  cases r <;> simp_all [Role.ev, Ev.isW, length_natBytes]

theorem H.fst_inj (h : H P L x U) {u w : Nat} (hu : u < x.n) (hw : w < x.n)
    (huW : (x.evN u).isW = true) (hwW : (x.evN w).isW = true) (he : fstU x u = fstU x w) :
    u = w := by
  cases hlu : isLW (x.evN u) <;> cases hlw : isLW (x.evN w)
  · rwa [fst_of hlu, fst_of hlw] at he
  · obtain ⟨r, hr, ht, hp, hlr, -⟩ := h.partnerW hw hlw
    rw [fst_of hlu, h.fst_lw hlw hr ht hp] at he
    subst he
    simp only [isLR, Ev.isR, Bool.and_eq_true, beq_iff_eq] at hlr
    simp [Ev.isW, hlr.1] at huW
  · obtain ⟨r, hr, ht, hp, hlr, -⟩ := h.partnerW hu hlu
    rw [fst_of hlw, h.fst_lw hlu hr ht hp] at he
    subst he
    simp only [isLR, Ev.isR, Bool.and_eq_true, beq_iff_eq] at hlr
    simp [Ev.isW, hlr.1] at hwW
  · obtain ⟨r, hr, ht, hp, -, -⟩ := h.partnerW hu hlu
    obtain ⟨r', hr', ht', hp', -, -⟩ := h.partnerW hw hlw
    rw [h.fst_lw hlu hr ht hp, h.fst_lw hlw hr' ht' hp'] at he
    subst he
    exact h.uniq hu hw (by rw [← ht, ← ht']) (by rw [hp, hp'])

theorem bit_le (x : Exec) (u : Nat) : bit x u ≤ 1 := by simp only [bit]; split <;> omega

/-- A write coherence-after `u` starts its block after `u`'s. -/
theorem H.co_after (h : H P L x U) {u w y : Nat} (hu : u < x.n)
    (huW : (x.evN u).isW = true) (hcu : (x.evN u).covers y = true) (hw : w ∈ x.co y)
    (hb : before (x.co y) u w = true) : κ x (fstU x u) < κ x (fstU x w) := by
  have huM : (x.evN u).isM = true := by simp [Ev.isM, huW]
  obtain ⟨hw, hwW, hcw⟩ := h.coMem hu huM hcu hw
  have hg := h.κ_ghb hu hw (ghb_of_coR (coR_mk (a := ⟨u, hu⟩) (b := ⟨w, hw⟩) huW hwW hcu hcw hb))
  have h1 := h.κ_fst hu
  have h2 := h.κ_fst hw
  have h3 := bit_le x u
  have h4 := bit_le x w
  have hne : κ x (fstU x w) ≠ κ x (fstU x u) := by
    intro he
    have := h.fst_inj hw hu hwW huW
      (h.κ_inj (h.fst_spec hw).1 (h.fst_spec hu).1 he)
    rw [this, Silmaril.Proofs.X86.Concurrency.Cir.Domain.before_irrefl (h.coNodup hu huM hcu)] at hb
    cases hb
  omega

/-! ## Memory -/

theorem H.cval_write (h : H P L x U) {u T a : Nat} (hu : u < x.n) (huW : (x.evN u).isW = true)
    (hc : (x.evN u).covers a = true) (hκ : κ x (fstU x u) = T) :
    cval x (T + 1) a = some (wval x u) := by
  simp only [cval]
  rw [last_filter (s := u) (h.coIn hu huW hc) (by simp [vis, hu, huW, hc, hκ])]
  · rfl
  intro w hw hb
  have := h.co_after hu huW hc hw hb
  simp only [vis, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  right; omega

theorem H.cval_same (_h : H P L x U) {T a : Nat}
    (hn : ∀ w < x.n, (x.evN w).isW = true → (x.evN w).covers a = true → κ x (fstU x w) ≠ T) :
    cval x (T + 1) a = cval x T a := by
  simp only [cval]
  congr 2
  apply List.filter_congr
  intro w _
  simp only [vis]
  by_cases hw : w < x.n
  · by_cases hW : (x.evN w).isW = true
    · by_cases hC : (x.evN w).covers a = true
      · have := hn w hw hW hC
        simp only [hw, decide_true, hW, hC, Bool.and_self, Bool.true_and, decide_eq_decide]; omega
      · simp [hC]
    · simp [hW]
  · simp [hw]

/-- `cval` is the value of the coherence-last visible write. -/
theorem H.cval_of (h : H P L x U) {T a w : Nat} (hw : w < x.n) (hW : (x.evN w).isW = true)
    (hc : (x.evN w).covers a = true) (hvis : κ x (fstU x w) < T)
    (hlater : ∀ w' < x.n, (x.evN w').isW = true → (x.evN w').covers a = true →
      before (x.co a) w w' = true → T ≤ κ x (fstU x w')) :
    cval x T a = some (wval x w) := by
  simp only [cval]
  rw [last_filter (s := w) (h.coIn hw hW hc) (by simp [vis, hw, hW, hc, hvis])]
  · rfl
  intro w' hw' hb
  have hwM : (x.evN w).isM = true := by simp [Ev.isM, hW]
  obtain ⟨h1, h2, h3⟩ := h.coMem hw hwM hc hw'
  have := hlater w' h1 h2 h3 hb
  simp only [vis, Bool.and_eq_false_iff, decide_eq_false_iff_not]; right; omega

theorem cval_none' {x : Exec} {T a : Nat}
    (hn : ∀ w < x.n, (x.evN w).isW = true → (x.evN w).covers a = true → T ≤ κ x (fstU x w)) :
    cval x T a = none := by
  simp only [cval]
  rw [last_filter_none]
  · rfl
  intro w _
  simp only [vis]
  by_cases hw : w < x.n
  · by_cases hW : (x.evN w).isW = true
    · by_cases hC : (x.evN w).covers a = true
      · have := hn w hw hW hC
        simp only [hw, decide_true, hW, hC, Bool.and_self, Bool.true_and, decide_eq_false_iff_not]
        omega
      · simp [hC]
    · simp [hW]
  · simp [hw]

end


/-! ## Edges on `Nat` indices -/

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)}

theorem isM_W {e : Ev} (h : e.isW = true) : e.isM = true := by simp [Ev.isM, h]
theorem isM_R {e : Ev} (h : e.isR = true) : e.isM = true := by simp [Ev.isM, h]
theorem RW_false {e : Ev} (h1 : e.isR = true) (h2 : e.isW = true) : False := by
  simp only [Ev.isR, Ev.isW, beq_iff_eq] at h1 h2; rw [h1] at h2; cases h2

theorem H.κ_ppoW (h : H P L x U) {a b : Nat} (ha : a < x.n) (hb : b < x.n)
    (ht : (x.evN a).tid = (x.evN b).tid) (hp : (x.evN a).pos < (x.evN b).pos)
    (hwa : (x.evN a).isW = true) (hwb : (x.evN b).isW = true) : κ x a < κ x b :=
  h.κ_ghb ha hb (ghb_of_ppo (po_iff.mpr ⟨ht, hp⟩) (.inl ⟨hwa, hwb⟩))

theorem H.κ_ppoR (h : H P L x U) {a b : Nat} (ha : a < x.n) (hb : b < x.n)
    (ht : (x.evN a).tid = (x.evN b).tid) (hp : (x.evN a).pos < (x.evN b).pos)
    (hra : (x.evN a).isR = true) (hmb : (x.evN b).isM = true) : κ x a < κ x b :=
  h.κ_ghb ha hb (ghb_of_ppo (po_iff.mpr ⟨ht, hp⟩) (.inr ⟨hra, hmb⟩))

theorem H.κ_impl (h : H P L x U) {a b : Nat} (ha : a < x.n) (hb : b < x.n)
    (ht : (x.evN a).tid = (x.evN b).tid) (hp : (x.evN a).pos < (x.evN b).pos)
    (hwa : (x.evN a).isW = true) (hrb : (x.evN b).isR = true)
    (hl : (x.evN a).isA = true ∨ (x.evN b).isA = true) : κ x a < κ x b :=
  h.κ_ghb ha hb (ghb_of_implied (po_iff.mpr ⟨ht, hp⟩) hwa hrb hl)

theorem H.κ_mf (h : H P L x U) {a b f : Nat} (ha : a < x.n) (hb : b < x.n) (hf : f < x.n)
    (hff : (x.evN f).isFence .mfence = true)
    (ht1 : (x.evN a).tid = (x.evN f).tid) (hp1 : (x.evN a).pos < (x.evN f).pos)
    (ht2 : (x.evN f).tid = (x.evN b).tid) (hp2 : (x.evN f).pos < (x.evN b).pos) : κ x a < κ x b :=
  h.κ_ghb ha hb (ghb_of_mfence (f := ⟨f, hf⟩) hff (po_iff.mpr ⟨ht1, hp1⟩) (po_iff.mpr ⟨ht2, hp2⟩))

theorem H.κ_fr (h : H P L x U) {r w : Nat} (hr : r < x.n) (hw : w < x.n)
    (hfr : x.frR ⟨r, hr⟩ ⟨w, hw⟩ = true) : κ x r < κ x w :=
  h.κ_ghb hr hw (ghb_of_frR hfr)

theorem H.κ_co (h : H P L x U) {a b y : Nat} (ha : a < x.n) (hb : b < x.n)
    (hwa : (x.evN a).isW = true) (hwb : (x.evN b).isW = true) (hca : (x.evN a).covers y = true)
    (hcb : (x.evN b).covers y = true) (hbe : before (x.co y) a b = true) : κ x a < κ x b :=
  h.κ_ghb ha hb (ghb_of_coR (coR_mk (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) hwa hwb hca hcb hbe))

theorem H.κ_rfe (h : H P L x U) {w r y : Nat} (hw : w < x.n) (hr : r < x.n)
    (hwW : (x.evN w).isW = true) (hrR : (x.evN r).isR = true) (hcr : (x.evN r).covers y = true)
    (hcw : (x.evN w).covers y = true) (hrf : x.rf r y = some w)
    (ht : (x.evN w).tid ≠ (x.evN r).tid) : κ x w < κ x r :=
  h.κ_ghb hw hr (ghb_of_rfe (rfR_mk (w := ⟨w, hw⟩) (r := ⟨r, hr⟩) hwW hrR hcr hcw hrf) ht)

/-- A read does not read before a write of its own thread that precedes it. -/
theorem H.cyc_fr (h : H P L x U) {r w : Nat} (hr : r < x.n) (hw : w < x.n)
    (ht : (x.evN w).tid = (x.evN r).tid) (hp : (x.evN w).pos < (x.evN r).pos)
    (hwW : (x.evN w).isW = true) (hrR : (x.evN r).isR = true) {y : Nat}
    (hcr : (x.evN r).covers y = true) (hcw : (x.evN w).covers y = true)
    (hfr : x.frR ⟨r, hr⟩ ⟨w, hw⟩ = true) : False :=
  h.unip2 (a := ⟨w, hw⟩) (b := ⟨r, hr⟩)
    (uniproc_of_poLoc (po_iff.mpr ⟨ht, hp⟩) (isM_W hwW) (isM_R hrR) hcw hcr)
    (uniproc_of_com (com_of_frR hfr))

/-- Coherence follows program order within a thread. -/
theorem H.cyc_co (h : H P L x U) {a b : Nat} (ha : a < x.n) (hb : b < x.n)
    (ht : (x.evN a).tid = (x.evN b).tid) (hp : (x.evN a).pos < (x.evN b).pos)
    (hwa : (x.evN a).isW = true) (hwb : (x.evN b).isW = true) {y : Nat}
    (hca : (x.evN a).covers y = true) (hcb : (x.evN b).covers y = true)
    (hbe : before (x.co y) b a = true) : False :=
  h.unip2 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    (uniproc_of_poLoc (po_iff.mpr ⟨ht, hp⟩) (isM_W hwa) (isM_W hwb) hca hcb)
    (uniproc_of_com (com_of_coR (coR_mk (a := ⟨b, hb⟩) (b := ⟨a, ha⟩) hwb hwa hcb hca hbe)))

/-- A read does not read from a later write of its own thread. -/
theorem H.cyc_rf (h : H P L x U) {r w : Nat} (hr : r < x.n) (hw : w < x.n)
    (ht : (x.evN r).tid = (x.evN w).tid) (hp : (x.evN r).pos < (x.evN w).pos)
    (hwW : (x.evN w).isW = true) (hrR : (x.evN r).isR = true) {y : Nat}
    (hcr : (x.evN r).covers y = true) (hcw : (x.evN w).covers y = true)
    (hrf : x.rf r y = some w) : False :=
  h.unip2 (a := ⟨r, hr⟩) (b := ⟨w, hw⟩)
    (uniproc_of_poLoc (po_iff.mpr ⟨ht, hp⟩) (isM_R hrR) (isM_W hwW) hcr hcw)
    (uniproc_of_com (com_of_rfR (rfR_mk (w := ⟨w, hw⟩) (r := ⟨r, hr⟩) hwW hrR hcr hcw hrf)))

/-- `fr` from a read to a write: by `rf` and `co` at one byte. -/
theorem frR_of {r w : Nat} (hr : r < x.n) (hw : w < x.n) (hrR : (x.evN r).isR = true)
    (hwW : (x.evN w).isW = true) {y : Nat} (hcr : (x.evN r).covers y = true)
    (hcw : (x.evN w).covers y = true)
    (hm : match x.rf r y with
      | none => True
      | some v => before (x.co y) v w = true) : x.frR ⟨r, hr⟩ ⟨w, hw⟩ = true :=
  frR_mk hrR hwW hcr hcw hm

end

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp
