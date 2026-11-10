module

public import Silmaril.Proofs.X86.Concurrency.Cir.Seq.Trace

/-!
# The single-threaded lift for CIR

* `val_iff`: a flat memory holds the value `v` (that fits) at `[a, a + sz)` exactly when its bytes
  are `natBytes v sz`;
* `replay_eq`: on `ok` labels, CIR's sequential `replay` is the replay of their lowered actions;
* `actOk_of_ok`: the lowered actions of `ok` labels are `ActOk`;
* `run_ok`: every run of a thread-free statement with positive sizes has only `ok` labels;
* `solo_behav_iff`: **the single-threaded lift**: under every `M` with `SC ⊑ M ⊑ XL`, the
  behaviours of a one-thread, thread-free CIR program with positive sizes are exactly its
  sequential runs.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Seq

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace Test Final AxReach finalOf leValue seqL initByte)
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec)

/-! ## Values and bytes -/

theorem leValue_some (m : Mem) : ∀ a sz, ∃ r, leValue (fun y => some ((m y).getD 0)) a sz = some r
  | _, 0 => ⟨0, rfl⟩
  | a, sz + 1 => by
    obtain ⟨r, hr⟩ := leValue_some m (a + 1) sz
    exact ⟨_, by unfold leValue; rw [hr]; rfl⟩

theorem natBytes_succ (v sz : Nat) :
    natBytes v (sz + 1) = BitVec.ofNat 8 v :: natBytes (v / 256) sz := by
  simp only [natBytes, List.range_succ_eq_map, List.map_cons, List.map_map, pow_zero, Nat.div_one]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp [Function.comp, pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem bytesAt_succ (m : Mem) (a sz : Nat) :
    bytesAt m a (sz + 1) = (m a).getD 0 :: bytesAt m (a + 1) sz := by
  simp [bytesAt, List.range'_succ]

theorem length_natBytes (v sz : Nat) : (natBytes v sz).length = sz := by simp [natBytes]

/-- **Values are bytes.** -/
theorem val_iff (m : Mem) : ∀ (a sz v : Nat), v < 2 ^ (8 * sz) →
    (m.val a sz = some v ↔ bytesAt m a sz = natBytes v sz)
  | a, 0, v, hv => by
    have : v = 0 := by simpa using hv
    subst this; simp [Mem.val, leValue, bytesAt, natBytes]
  | a, sz + 1, v, hv => by
    obtain ⟨r, hr⟩ := leValue_some m (a + 1) sz
    have hv' : v / 256 < 2 ^ (8 * sz) := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      calc v < 2 ^ (8 * (sz + 1)) := hv
        _ = 2 ^ (8 * sz) * 256 := by rw [Nat.mul_succ, Nat.pow_add]
    have ih := val_iff m (a + 1) sz (v / 256) hv'
    simp only [Mem.val] at ih ⊢
    rw [natBytes_succ, bytesAt_succ, List.cons.injEq, ← ih]
    simp only [leValue, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq]
    have hb := ((m a).getD 0).isLt
    constructor
    · intro h
      refine ⟨BitVec.eq_of_toNat_eq ?_, by omega⟩
      simp only [BitVec.toNat_ofNat]; omega
    · rintro ⟨h1, h2⟩
      have : ((m a).getD 0).toNat = v % 2 ^ 8 := by rw [h1, BitVec.toNat_ofNat]
      omega

theorem putBytes_natBytes (m : Mem) (a sz v : Nat) : putBytes m a sz (natBytes v sz) = m.put a sz v := by
  funext y
  simp only [putBytes, Mem.put]
  split
  · rename_i h
    simp [natBytes, List.getElem?_map, List.getElem?_range (show y - a < sz by omega)]
  · rfl

/-! ## Replay of lowered labels -/

theorem actsReplay_append (m : Mem) (l l' : List XAct) :
    actsReplay m (l ++ l') = (actsReplay m l).bind fun m' => actsReplay m' l' := by
  induction l generalizing m with
  | nil => simp [actsReplay]
  | cons a l ih =>
    simp only [List.cons_append, actsReplay]
    cases actStep m a <;> simp [ih]

theorem actsReplay_loads (m : Mem) (L : List XAct) :
    ∀ ins : List (Nat × Nat × Nat), (∀ c ∈ ins, c.2.2 < 2 ^ (8 * c.2.1)) →
      actsReplay m (ins.map (fun c => ldAct .wb c.1 c.2.1 c.2.2) ++ L) =
        if ins.all (fun c => m.val c.1 c.2.1 == some c.2.2) then actsReplay m L else none
  | [], _ => by simp
  | c :: ins, h => by
    simp only [List.map_cons, List.cons_append, actsReplay, actStep, ldAct, List.all_cons]
    have hv := val_iff m c.1 c.2.1 c.2.2 (h c List.mem_cons_self)
    by_cases hc : bytesAt m c.1 c.2.1 = natBytes c.2.2 c.2.1
    · simp only [hc, ite_true, Option.bind_some, hv.mpr hc, beq_self_eq_true, Bool.true_and]
      exact actsReplay_loads m L ins fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    · have : (m.val c.1 c.2.1 == some c.2.2) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h' => hc (hv.mp h')
      simp [hc, this]

theorem actsReplay_stores (m : Mem) :
    ∀ outs : List (Nat × Nat × Nat),
      actsReplay m (outs.map fun c => stAct .wb c.1 c.2.1 c.2.2) =
        some (outs.foldl (fun m c => m.put c.1 c.2.1 c.2.2) m)
  | [] => rfl
  | c :: outs => by
    simp only [List.map_cons, actsReplay, actStep, stAct, Option.bind_some, List.foldl_cons,
      putBytes_natBytes]
    exact actsReplay_stores _ outs

/-- **CIR's sequential replay is the replay of the lowered actions** (on `ok` labels). -/
theorem replay_lab (m : Mem) (l : Lab) (hl : l.ok) : l.replay m = actsReplay m l.acts := by
  cases l with
  | rd md fl a sz v =>
    have hv := val_iff m a sz v hl.2
    simp only [Lab.replay, Lab.acts, ldAct, actsReplay, actStep]
    by_cases h : bytesAt m a sz = natBytes v sz
    · simp [h, hv.mpr h]
    · have : m.val a sz ≠ some v := fun h' => h (hv.mp h')
      simp [h, this]
  | wr md fl a sz v =>
    simp [Lab.replay, Lab.acts, stAct, actsReplay, actStep, putBytes_natBytes]
  | rmw md a sz o n =>
    have hv := val_iff m a sz o hl.2
    simp only [Lab.replay, Lab.acts, rmwAct, actsReplay, actStep]
    by_cases h : bytesAt m a sz = natBytes o sz
    · simp [h, hv.mpr h, putBytes_natBytes]
    · have : m.val a sz ≠ some o := fun h' => h (hv.mp h')
      simp [h, this]
  | fence k => rfl
  | fwait a e seen r =>
    by_cases he : seen = e
    · subst he
      simp only [Lab.replay, Lab.acts, ite_true, ldAct, stAct, rmwAct, fenceAct, actsReplay,
        actStep, Option.bind_some, putBytes_natBytes]
      have hv := val_iff (m.put (qAddr a) 1 1) a 4 seen hl.1
      have hq := val_iff (m.put (qAddr a) 1 1) (qAddr a) 1 r hl.2
      by_cases h : bytesAt (m.put (qAddr a) 1 1) a 4 = natBytes seen 4
      · by_cases h' : bytesAt (m.put (qAddr a) 1 1) (qAddr a) 1 = natBytes r 1
        · simp [h, h', hv.mpr h, hq.mpr h']
        · have : (m.put (qAddr a) 1 1).val (qAddr a) 1 ≠ some r := fun h'' => h' (hq.mp h'')
          simp [h, h', hv.mpr h, this]
      · have : (m.put (qAddr a) 1 1).val a 4 ≠ some seen := fun h' => h (hv.mp h')
        simp [h, this]
    · have hv := val_iff m a 4 seen hl.1
      simp only [Lab.replay, Lab.acts, he, ite_false, ldAct, fenceAct, actsReplay, actStep,
        Option.bind_some]
      by_cases h : bytesAt m a 4 = natBytes seen 4
      · simp [h, hv.mpr h]
      · have : m.val a 4 ≠ some seen := fun h' => h (hv.mp h')
        simp [h, this]
  | fwake a n q =>
    have hq := val_iff m (qAddr a) 1 q hl
    simp only [Lab.replay, Lab.acts, rmwAct, fenceAct, actsReplay, actStep, Option.bind_some]
    by_cases h : bytesAt m (qAddr a) 1 = natBytes q 1
    · simp [h, hq.mpr h, putBytes_natBytes]
    · have : m.val (qAddr a) 1 ≠ some q := fun h' => h (hq.mp h')
      simp [h, this]
  | fblock a e => exact hl.elim
  | spawn t => exact hl.elim
  | join t => exact hl.elim
  | blk nm ins outs rvs =>
    simp only [Lab.replay, Lab.acts]
    rw [actsReplay_loads m _ ins fun c hc => (hl.1 c hc).2, actsReplay_stores]

theorem replay_eq (m : Mem) : ∀ tr : List Lab, (∀ l ∈ tr, l.ok) →
    replay m tr = actsReplay m (tr.flatMap Lab.acts)
  | [], _ => rfl
  | l :: tr, h => by
    simp only [replay, List.flatMap_cons, actsReplay_append, ← replay_lab m l (h l List.mem_cons_self)]
    cases l.replay m with
    | none => rfl
    | some m' => exact replay_eq m' tr fun l' hl' => h l' (List.mem_cons_of_mem _ hl')

/-- The lowered actions of `ok` labels are `ActOk`. -/
theorem actOk_of_ok {l : Lab} (hl : l.ok) : ∀ a ∈ l.acts, ActOk a := by
  cases l with
  | rd md fl a sz v => simp [Lab.acts, ldAct, ActOk, length_natBytes, hl.1]
  | wr md fl a sz v => simp only [Lab.ok] at hl; simp [Lab.acts, stAct, ActOk, length_natBytes, hl]
  | rmw md a sz o n => simp [Lab.acts, rmwAct, ActOk, length_natBytes, hl.1]
  | fence k => simp [Lab.acts, fenceAct, ActOk]
  | fwait a e seen r =>
    by_cases he : seen = e
    · simp [Lab.acts, he, ldAct, stAct, rmwAct, fenceAct, ActOk, length_natBytes]
    · simp [Lab.acts, he, ldAct, fenceAct, ActOk, length_natBytes]
  | fwake a n q => simp [Lab.acts, rmwAct, fenceAct, ActOk, length_natBytes]
  | fblock a e => exact hl.elim
  | spawn t => exact hl.elim
  | join t => exact hl.elim
  | blk nm ins outs rvs =>
    intro a ha
    simp only [Lab.acts, List.mem_append, List.mem_map] at ha
    rcases ha with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · simp [ldAct, ActOk, length_natBytes, (hl.1 c hc).1]
    · simp [stAct, ActOk, length_natBytes, hl.2 c hc]

/-! ## Runs have `ok` labels -/

theorem mem_pick {dom : List Nat} {sz v : Nat} (h : v ∈ pick dom sz) : v < 2 ^ (8 * sz) := by
  simp only [pick, List.mem_filter, decide_eq_true_eq] at h; exact h.2

theorem mem_qpick {dom : List Nat} {v : Nat} (h : v ∈ qpick dom) : v < 2 ^ (8 * 1) := by
  simp only [qpick, List.mem_filter, decide_eq_true_eq] at h; exact mem_pick h.1

theorem mem_seqL {α β : Type} (g : β → List α) :
    ∀ (cs : List β) (vs : List α), vs ∈ seqL (cs.map g) → List.Forall₂ (fun c v => v ∈ g c) cs vs
  | [], vs, h => by simp [seqL] at h; subst h; exact .nil
  | c :: cs, vs, h => by
    simp only [List.map_cons, seqL, List.mem_flatMap, List.mem_map] at h
    obtain ⟨v, hv, ws, hws, rfl⟩ := h
    exact .cons hv (mem_seqL g cs ws hws)

theorem mem_cellVals {cs : List (Nat × Nat)} {vs : List Nat} {c : Nat × Nat × Nat}
    (h : c ∈ cellVals cs vs) : (c.1, c.2.1) ∈ cs ∧ ∃ v ∈ vs, c.2.2 = v := by
  induction cs generalizing vs with
  | nil => simp [cellVals] at h
  | cons d cs ih =>
    cases vs with
    | nil => simp [cellVals] at h
    | cons v vs =>
      simp only [cellVals, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨List.mem_cons_self, v, List.mem_cons_self, rfl⟩
      · obtain ⟨h1, w, hw, h2⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ h1, w, List.mem_cons_of_mem _ hw, h2⟩

theorem mem_cellVals_pick {dom : List Nat} {cs : List (Nat × Nat)} {vs : List Nat}
    (hvs : List.Forall₂ (fun c v => v ∈ pick dom c.2) cs vs) {c : Nat × Nat × Nat}
    (h : c ∈ cellVals cs vs) : (c.1, c.2.1) ∈ cs ∧ c.2.2 < 2 ^ (8 * c.2.1) := by
  induction hvs with
  | nil => simp [cellVals] at h
  | cons hv _ ih =>
    simp only [cellVals, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨List.mem_cons_self, mem_pick hv⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem iter_ok {P : Lab → Prop} {body : Regs → Res} {c : Expr}
    (hb : ∀ rs p, p ∈ body rs → ∀ l ∈ p.1, P l) :
    ∀ n rs p, p ∈ iter body c n rs → ∀ l ∈ p.1, P l
  | 0, rs, p, h => by
    simp only [iter] at h
    split at h
    · simp at h
    · simp only [List.mem_singleton] at h; subst h; simp
  | n + 1, rs, p, h => by
    simp only [iter] at h
    split at h
    · simp only [Res.bind, List.mem_flatMap, List.mem_map] at h
      obtain ⟨a, ha, b, hb', rfl⟩ := h
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact hb rs a ha l hl
      · exact iter_ok hb n a.2 b hb' l hl
    · simp only [List.mem_singleton] at h; subst h; simp

/-- **Runs of thread-free statements with positive sizes have `ok` labels.** -/
theorem run_ok (dom : List Nat) : ∀ (s : Stmt), s.threadFree = true → s.posSizes = true →
    ∀ rs p, p ∈ run dom s rs → ∀ l ∈ p.1, l.ok
  | .skip, _, _, rs, p, h => by simp [run] at h; subst h; simp
  | .assign d e, _, _, rs, p, h => by simp [run] at h; subst h; simp
  | .load d md sz fl a, _, hp, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [Stmt.posSizes, decide_eq_true_eq] at hp
    simp [Lab.ok, hp, mem_pick hv]
  | .store md sz fl a v, _, hp, rs, p, h => by
    simp only [run, List.mem_singleton] at h; subst h
    simp only [Stmt.posSizes, decide_eq_true_eq] at hp
    simp [Lab.ok, hp]
  | .rmw d md sz op a arg, _, hp, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [Stmt.posSizes, decide_eq_true_eq] at hp
    simp [Lab.ok, hp, mem_pick hv]
  | .fence k, _, _, rs, p, h => by simp [run] at h; subst h; simp [Lab.ok]
  | .futexWait d a v, _, _, rs, p, h => by
    simp only [run, List.mem_flatMap] at h
    obtain ⟨w, hw, h⟩ := h
    have := mem_pick hw
    split at h
    · simp only [List.mem_map] at h
      obtain ⟨r, hr, rfl⟩ := h
      have := mem_qpick hr
      simp only [List.mem_singleton, forall_eq, Lab.ok]
      constructor <;> simpa
    · simp only [List.mem_singleton] at h; subst h
      simp only [List.mem_singleton, forall_eq, Lab.ok]
      exact ⟨by simpa using this, by simp⟩
  | .futexWake a n, _, _, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨q, hq, rfl⟩ := h
    have := mem_qpick hq
    simp only [List.mem_singleton, forall_eq, Lab.ok]
    simpa using this
  | .spawn t, ht, _, _, _, _ => by simp [Stmt.threadFree] at ht
  | .join t, ht, _, _, _, _ => by simp [Stmt.threadFree] at ht
  | .local b, _, hp, rs, p, h => by
    simp only [run, runBlock, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨ivs, hivs, rvs, -, ovs, hovs, h⟩ := h
    split at h
    · cases h
      have hi := mem_seqL _ _ _ hivs
      simp only [Stmt.posSizes, List.all_eq_true, List.mem_append, decide_eq_true_eq] at hp
      simp only [List.mem_singleton, forall_eq, Lab.ok]
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · obtain ⟨h1, h2⟩ := mem_cellVals_pick hi hc
        exact ⟨hp _ (.inl h1), h2⟩
      · exact hp _ (.inr (mem_cellVals hc).1)
    · cases h
  | .seq s t, ht, hp, rs, p, h => by
    simp only [Stmt.threadFree, Stmt.posSizes, Bool.and_eq_true] at ht hp
    simp only [run, Res.bind, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact run_ok dom s ht.1 hp.1 rs a ha l hl
    · exact run_ok dom t ht.2 hp.2 a.2 b hb l hl
  | .ite c s t, ht, hp, rs, p, h => by
    simp only [Stmt.threadFree, Stmt.posSizes, Bool.and_eq_true] at ht hp
    simp only [run] at h
    split at h
    · exact run_ok dom s ht.1 hp.1 rs p h
    · exact run_ok dom t ht.2 hp.2 rs p h
  | .loop n c body, ht, hp, rs, p, h => by
    simp only [Stmt.threadFree, Stmt.posSizes] at ht hp
    exact iter_ok (fun rs p h => run_ok dom body ht hp rs p h) n rs p h

/-! ## One-thread CIR programs -/

theorem solo_traces (locs : List Silmaril.X86.MemoryModel.Litmus.Loc) (s : Stmt) (dom : List Nat) :
    (solo locs s).traces dom = [(run dom s Regs.zero).map (Thread.xtrace ⟨s, false⟩ 0)] := by
  simp [Prog.traces, solo]

theorem xtrace_acts (s : Stmt) (p : List Lab × Regs) :
    (Thread.xtrace ⟨s, false⟩ 0 p).acts = p.1.flatMap Lab.acts := by
  simp [Thread.xtrace, Thread.acts, Silmaril.X86.Litmus.Trace.acts]

theorem finalOf_solo (s : Stmt) (p : List Lab × Regs) (m : Mem) :
    finalOf [Thread.xtrace ⟨s, false⟩ 0 p] m = soloFinal p.2 m := by
  simp only [finalOf, soloFinal]
  congr 1
  funext i r
  cases i with
  | zero => simp [Thread.xtrace, coreOf, Silmaril.X86.State.read]
  | succ i => simp

/-- **The single-threaded lift for CIR.** -/
theorem solo_behav_iff (locs : List Silmaril.X86.MemoryModel.Litmus.Loc) (s : Stmt)
    (ht : s.threadFree = true) (hp : s.posSizes = true) {M : Exec → Prop}
    (hsc : ∀ x, x.Sc → M x) (hxl : ∀ x, M x → x.Xl) (f : Final) :
    Behav (solo locs s) M f ↔
      ∃ tr rs m, SeqRun s Regs.zero (initByte locs) tr rs m ∧ f = soloFinal rs m := by
  have hok : ∀ dom, ∀ xt ∈ (run dom s Regs.zero).map (Thread.xtrace ⟨s, false⟩ 0),
      ∀ a ∈ xt.acts, ActOk a := by
    intro dom xt hxt a ha
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hxt
    rw [xtrace_acts] at ha
    obtain ⟨l, hl, ha⟩ := List.mem_flatMap.mp ha
    exact actOk_of_ok (run_ok dom s ht hp _ p hp' l hl) a ha
  constructor
  · rintro ⟨dom, h⟩
    simp only [BehavIn, solo_traces] at h
    obtain ⟨xt, hxt, m, hm, rfl⟩ := axReach_one_sound _ _ (hok dom) hxl h
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hxt
    refine ⟨p.1, p.2, m, ⟨⟨dom, hp'⟩, ?_⟩, finalOf_solo s p m⟩
    rw [replay_eq _ _ (run_ok dom s ht hp _ p hp'), ← xtrace_acts s p]
    exact hm
  · rintro ⟨tr, rs, m, ⟨⟨dom, hrun⟩, hrep⟩, rfl⟩
    refine ⟨dom, ?_⟩
    simp only [BehavIn, solo_traces]
    have := axReach_one_complete (solo locs s).memTest _ (hok dom) hsc (List.mem_map_of_mem (f := Thread.xtrace ⟨s, false⟩ 0) hrun)
      (m := m) (by
        rw [xtrace_acts, ← replay_eq _ _ (run_ok dom s ht hp _ _ hrun)]
        exact hrep)
    rwa [finalOf_solo] at this

end Silmaril.Proofs.X86.Concurrency.Cir.Seq
