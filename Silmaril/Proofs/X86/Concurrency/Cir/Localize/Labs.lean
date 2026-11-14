module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Run

/-!
# Localisation: labels, their actions and their sequential replay

* `val_lt`, `natBytes_val`: the value of `sz` bytes fits, and its bytes are the memory's;
* `replay_eq`, `actOk_of_ok`: on `ok` labels, CIR's `replay` is the replay of the lowered
  actions, which are `ActOk` (**copied** from `Silmaril/Proofs/X86/Concurrency/Cir/Seq/Lab.lean`,
  whose header does not export them, with `val_iff`, `putBytes_natBytes`,
  `actsReplay_loads`, `actsReplay_stores`, `replay_lab`);
* `frag_acts`, `frag_ok`: the actions of a fragment label are on its cells, its writes on the
  out cells, and the label is `ok`;
* `lab_lock`: only read-modify-write actions are locked;
* `run_wb`: the stores of a statement with write-back stores are plain.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.MemoryModel.Litmus (Byte XAct leValue)

/-! ## Values and bytes -/

theorem leValue_some (m : Mem) : ∀ a sz, ∃ r, leValue (fun y => some ((m y).getD 0)) a sz = some r
  | _, 0 => ⟨0, rfl⟩
  | a, sz + 1 => by
    obtain ⟨r, hr⟩ := leValue_some m (a + 1) sz
    exact ⟨_, by unfold leValue; rw [hr]; rfl⟩

theorem val_lt (m : Mem) : ∀ a sz r, m.val a sz = some r → r < 2 ^ (8 * sz)
  | a, 0, r, h => by simp [Mem.val, leValue] at h; subst h; simp
  | a, sz + 1, r, h => by
    simp only [Mem.val, leValue] at h
    obtain ⟨r', hr'⟩ := leValue_some m (a + 1) sz
    simp only [hr', Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    have := val_lt m (a + 1) sz r' hr'
    have hb := ((m a).getD 0).isLt
    subst h
    have h2 : 2 ^ (8 * (sz + 1)) = 256 * 2 ^ (8 * sz) := by
      rw [show 8 * (sz + 1) = 8 + 8 * sz by omega, Nat.pow_add]
    have hb' : BitVec.toNat ((m a).getD 0) < 256 := hb
    rw [h2]; omega

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

/-- The bytes of a memory value are the memory's bytes. -/
theorem natBytes_val (m : Mem) (a sz : Nat) :
    natBytes ((m.val a sz).getD 0) sz = bytesAt m a sz := by
  obtain ⟨r, hr⟩ := leValue_some m a sz
  have hr' : m.val a sz = some r := hr
  rw [hr', Option.getD_some]
  exact ((val_iff m a sz r (val_lt m a sz r hr')).mp hr').symm

theorem getD_val_lt (m : Mem) (a sz : Nat) : (m.val a sz).getD 0 < 2 ^ (8 * sz) := by
  obtain ⟨r, hr⟩ := leValue_some m a sz
  have hr' : m.val a sz = some r := hr
  rw [hr', Option.getD_some]; exact val_lt m a sz r hr'

theorem putBytes_natBytes (m : Mem) (a sz v : Nat) :
    putBytes m a sz (natBytes v sz) = m.put a sz v := by
  funext y
  simp only [putBytes, Mem.put]
  split
  · rename_i h
    simp [natBytes, List.getElem?_map, List.getElem?_range (show y - a < sz by omega)]
  · rfl

/-! ## Replay of lowered labels (copied) -/

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
    simp only [replay, List.flatMap_cons, Seq.actsReplay_append,
      ← replay_lab m l (h l List.mem_cons_self)]
    cases l.replay m with
    | none => rfl
    | some m' => exact replay_eq m' tr fun l' hl' => h l' (List.mem_cons_of_mem _ hl')

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

/-! ## Fragment labels -/

theorem frag_ok {cs outs : List (Nat × Nat)} (hpos : ∀ c ∈ cs, 0 < c.2) {l : Lab}
    (h : FragLab cs outs l) : l.ok := by
  cases l with
  | rd md fl a sz v => exact ⟨hpos _ h.2.1, h.2.2⟩
  | wr md fl a sz v => exact hpos _ h.2.1
  | rmw md a sz o n => exact ⟨hpos _ h.1, h.2.2⟩
  | fence k => trivial
  | blk nm ins os rvs =>
    exact ⟨fun c hc => ⟨hpos _ (h.1 c hc).1, (h.1 c hc).2⟩, fun c hc => hpos _ (h.2 c hc).1⟩
  | _ => exact h.elim

/-- The actions of a fragment label are on its cells, and its writes on the out cells. -/
theorem frag_acts {cs outs : List (Nat × Nat)} {l : Lab} (h : FragLab cs outs l) :
    ∀ a ∈ l.acts, ((∃ f, a.ev.kind = .fence f) ∨ (a.ev.addr, a.ev.size) ∈ cs) ∧
      ((a.ev.kind = .store ∨ a.ev.kind = .rmw) → (a.ev.addr, a.ev.size) ∈ outs) := by
  cases l with
  | rd md fl a sz v =>
    intro x hx; simp only [Lab.acts, List.mem_singleton] at hx; subst hx
    exact ⟨.inr h.2.1, by simp [ldAct]⟩
  | wr md fl a sz v =>
    intro x hx; simp only [Lab.acts, List.mem_singleton] at hx; subst hx
    exact ⟨.inr h.2.1, fun _ => h.2.2⟩
  | rmw md a sz o n =>
    intro x hx; simp only [Lab.acts, List.mem_singleton] at hx; subst hx
    exact ⟨.inr h.1, fun _ => h.2.1⟩
  | fence k =>
    intro x hx; simp only [Lab.acts, List.mem_singleton] at hx; subst hx
    exact ⟨.inl ⟨k, rfl⟩, by simp [fenceAct]⟩
  | blk nm ins os rvs =>
    intro x hx
    simp only [Lab.acts, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · exact ⟨.inr (h.1 c hc).1, by simp [ldAct]⟩
    · exact ⟨.inr (h.2 c hc).1, fun _ => (h.2 c hc).2⟩
  | _ => exact h.elim

/-- The shape of a lowered action. -/
theorem lab_shape (l : Lab) : ∀ a ∈ l.acts,
    (∃ fl x sz v, a = ldAct fl x sz v) ∨ (∃ x sz v, a = stAct .wb x sz v) ∨
      (∃ x sz o n, a = rmwAct x sz o n) ∨ (∃ k, a = fenceAct k) ∨
      (∃ md fl x sz v, l = .wr md fl x sz v ∧ a = stAct fl x sz v) := by
  intro a ha
  cases l with
  | rd md fl x sz v =>
    simp only [Lab.acts, List.mem_singleton] at ha; exact .inl ⟨_, _, _, _, ha⟩
  | wr md fl x sz v =>
    simp only [Lab.acts, List.mem_singleton] at ha
    exact .inr (.inr (.inr (.inr ⟨md, fl, x, sz, v, rfl, ha⟩)))
  | rmw md x sz o n =>
    simp only [Lab.acts, List.mem_singleton] at ha; exact .inr (.inr (.inl ⟨_, _, _, _, ha⟩))
  | fence k =>
    simp only [Lab.acts, List.mem_singleton] at ha; exact .inr (.inr (.inr (.inl ⟨_, ha⟩)))
  | fwait x e seen r =>
    simp only [Lab.acts] at ha
    split at ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl
      · exact .inr (.inr (.inr (.inl ⟨_, rfl⟩)))
      · exact .inr (.inl ⟨_, _, _, rfl⟩)
      · exact .inr (.inr (.inr (.inl ⟨_, rfl⟩)))
      · exact .inl ⟨_, _, _, _, rfl⟩
      · exact .inr (.inr (.inl ⟨_, _, _, _, rfl⟩))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact .inr (.inr (.inr (.inl ⟨_, rfl⟩)))
      · exact .inl ⟨_, _, _, _, rfl⟩
      · exact .inr (.inr (.inr (.inl ⟨_, rfl⟩)))
  | fwake x n q =>
    simp only [Lab.acts, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact .inr (.inr (.inr (.inl ⟨_, rfl⟩)))
    · exact .inr (.inr (.inl ⟨_, _, _, _, rfl⟩))
    · exact .inr (.inr (.inr (.inl ⟨_, rfl⟩)))
  | fblock x e =>
    simp only [Lab.acts, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact .inr (.inr (.inr (.inl ⟨_, rfl⟩)))
    · exact .inr (.inl ⟨_, _, _, rfl⟩)
    · exact .inr (.inr (.inr (.inl ⟨_, rfl⟩)))
    · exact .inl ⟨_, _, _, _, rfl⟩
  | spawn t =>
    simp only [Lab.acts, List.mem_singleton] at ha; exact .inr (.inr (.inl ⟨_, _, _, _, ha⟩))
  | join t =>
    simp only [Lab.acts, List.mem_singleton] at ha; exact .inr (.inr (.inl ⟨_, _, _, _, ha⟩))
  | blk nm ins os rvs =>
    simp only [Lab.acts, List.mem_append, List.mem_map] at ha
    rcases ha with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
    · exact .inl ⟨_, _, _, _, rfl⟩
    · exact .inr (.inl ⟨_, _, _, rfl⟩)

/-- Only read-modify-write actions are locked. -/
theorem lab_lock (l : Lab) : ∀ a ∈ l.acts, a.ev.locked = true → a.ev.kind = .rmw := by
  intro a ha hl
  rcases lab_shape l a ha with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ |
    ⟨_, rfl⟩ | ⟨_, _, _, _, _, -, rfl⟩
  all_goals simp_all [ldAct, stAct, rmwAct, fenceAct]

/-- The stores of a label are plain (write-back), given its own store flavour is. -/
def WbLab : Lab → Prop
  | .wr _ fl _ _ _ => fl = .wb
  | _ => True

theorem wb_acts {l : Lab} (h : WbLab l) : ∀ a ∈ l.acts, a.ev.kind = .store → a.flavor = .plain := by
  intro a ha hk
  rcases lab_shape l a ha with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ |
    ⟨_, rfl⟩ | ⟨_, fl, _, _, _, rfl, rfl⟩
  · simp [ldAct] at hk
  · rfl
  · simp [rmwAct] at hk
  · simp [fenceAct] at hk
  · simp only [WbLab] at h; subst h; rfl

/-- **Runs of a statement with write-back stores have write-back labels.** -/
theorem run_wb (dom : List Nat) : ∀ (s : Stmt), s.wbStores = true → ∀ rs p, p ∈ run dom s rs →
    ∀ l ∈ p.1, WbLab l
  | .store md sz fl a v, hw, rs, p, h => by
    simp only [run, List.mem_singleton] at h; subst h
    simp only [Stmt.wbStores, beq_iff_eq] at hw
    simp [WbLab, hw]
  | .seq s t, hw, rs, p, h => by
    simp only [Stmt.wbStores, Bool.and_eq_true] at hw
    simp only [run] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := bind_mem h
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact run_wb dom s hw.1 rs a ha l hl
    · exact run_wb dom t hw.2 a.2 b hb l hl
  | .ite c s t, hw, rs, p, h => by
    simp only [Stmt.wbStores, Bool.and_eq_true] at hw
    simp only [run] at h
    split at h
    · exact run_wb dom s hw.1 rs p h
    · exact run_wb dom t hw.2 rs p h
  | .loop n c body, hw, rs, p, h => by
    simp only [Stmt.wbStores] at hw
    simp only [run] at h
    exact iter_all (fun rs p h => run_wb dom body hw rs p h) n rs p h
  | .skip, _, rs, p, h => by simp [run] at h; subst h; simp
  | .assign .., _, rs, p, h => by simp [run] at h; subst h; simp
  | .load .., _, rs, p, h => by
    simp only [run, List.mem_map] at h; obtain ⟨_, _, rfl⟩ := h; simp [WbLab]
  | .rmw .., _, rs, p, h => by
    simp only [run, List.mem_map] at h; obtain ⟨_, _, rfl⟩ := h; simp [WbLab]
  | .fence _, _, rs, p, h => by simp [run] at h; subst h; simp [WbLab]
  | .futexWait .., _, rs, p, h => by
    simp only [run, List.mem_flatMap] at h
    obtain ⟨w, -, h⟩ := h
    split at h
    · simp only [List.mem_map] at h; obtain ⟨_, _, rfl⟩ := h; simp [WbLab]
    · simp only [List.mem_singleton] at h; subst h; simp [WbLab]
  | .futexWake .., _, rs, p, h => by
    simp only [run, List.mem_map] at h; obtain ⟨_, _, rfl⟩ := h; simp [WbLab]
  | .spawn _, _, rs, p, h => by simp [run] at h; subst h; simp [WbLab]
  | .join _, _, rs, p, h => by simp [run] at h; subst h; simp [WbLab]
  | .local b, _, rs, p, h => by
    simp only [run, runBlock, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨_, -, _, -, _, -, h⟩ := h
    split at h
    · cases h; simp [WbLab]
    · cases h

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
