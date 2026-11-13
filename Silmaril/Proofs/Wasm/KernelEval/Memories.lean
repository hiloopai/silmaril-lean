module

public import Silmaril.Wasm.KernelEval.Memories
public import Silmaril.Proofs.Wasm.KernelEval.Basic

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: memory representations, proofs

Statements in `Silmaril.Wasm.KernelEval.MemThms`.
-/

namespace Silmaril.Proofs.Wasm.KernelEval

open Silmaril.Wasm.KernelEval

/-! ## Runs under a validity condition -/

section Sim

variable {M : Type} [MemOps M] {N : Type} [MemOps N] {g : M → N} {inv : M → Prop}

theorem step_mapMem_on (h : MemSimOn inv g) (c : Config M) (hc : inv c.mem) :
    step (c.mapMem g) = (step c).mapMem g := by
  rcases c with ⟨code, stk, labels, locals, mem⟩
  have hl := h.load mem hc
  have hs := h.store mem hc
  cases code with
  | nil => cases labels <;> rfl
  | cons i rest =>
    cases i <;> (rcases stk with _ | ⟨v, _ | ⟨w, _ | ⟨u, stk⟩⟩⟩) <;>
      simp only [step, Config.mapMem, hl, hs] <;> (try rfl) <;>
      first
      | (cases MemOps.store mem _ _ _ <;> simp [Result.mapMem, Config.mapMem]; done)
      | (cases MemOps.load mem _ _ <;> simp [Result.mapMem, Config.mapMem]; done)
      | (cases setLocal? locals _ _ <;> simp [Result.mapMem, Config.mapMem]; done)
      | (cases locals[_]? <;> simp [Result.mapMem, Config.mapMem]; done)
      | exact branch_mapMem (g := g) ⟨_, _, _, _, _⟩ _
      | (split <;> (first
          | (simp [Result.mapMem, Config.mapMem]; done)
          | exact branch_mapMem (g := g) ⟨_, _, _, _, _⟩ _))
      | (simp [Result.mapMem, Config.mapMem]; done)

/-- The memory of a result satisfies `inv`. -/
def resultMemInv (inv : M → Prop) : Result M → Prop
  | .running c => inv c.mem
  | .done _ _ m => inv m
  | _ => True

omit [MemOps M] in
theorem branch_memInv (c : Config M) (l : Nat) (hc : inv c.mem) :
    resultMemInv inv (branch c l) := by
  simp only [branch]; split <;> simp_all [resultMemInv]

theorem step_memInv (h : MemSimOn inv g) (c : Config M) (hc : inv c.mem) :
    resultMemInv inv (step c) := by
  rcases c with ⟨code, stk, labels, locals, mem⟩
  change inv mem at hc
  cases code with
  | nil => cases labels <;> exact hc
  | cons i rest =>
    cases i <;> (rcases stk with _ | ⟨v, _ | ⟨w, _ | ⟨u, stk⟩⟩⟩) <;>
      simp only [step] <;> (try exact hc) <;> (try trivial) <;>
      first
      | (rcases hm : MemOps.store mem _ _ _ with _ | m' <;> simp only [resultMemInv] <;>
          first | trivial | exact h.store_inv mem hc _ _ _ _ hm)
      | (cases MemOps.load mem _ _ <;> simp [resultMemInv, hc]; done)
      | (cases setLocal? locals _ _ <;> simp [resultMemInv, hc]; done)
      | (cases locals[_]? <;> simp [resultMemInv, hc]; done)
      | exact branch_memInv _ _ hc
      | (split <;> (first
          | (simp [resultMemInv, hc]; done)
          | exact branch_memInv _ _ hc))
      | (simp [resultMemInv, hc]; done)

theorem run_mapMem_on (h : MemSimOn inv g) (n : Nat) (c : Config M) (hc : inv c.mem) :
    run n (c.mapMem g) = (run n c).mapMem g := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [run, step_mapMem_on h c hc]
    have hi := step_memInv h c hc
    cases hs : step c with
    | running c' => rw [hs] at hi; simp [Result.mapMem, ih c' hi]
    | _ => simp [Result.mapMem]

theorem returns_mapMem_on (h : MemSimOn inv g) (fuel : Nat) (body : List Instr)
    (locals : List (BitVec 32)) (m : M) (hm : inv m) (v : BitVec 32) :
    returns fuel body locals (g m) v = returns fuel body locals m v := by
  have : Config.init body locals (g m) = (Config.init body locals m).mapMem g := rfl
  simp only [returns, runRec_eq_run, this, run_mapMem_on h fuel (Config.init body locals m) hm,
    top?_mapMem]

theorem memSimOn_of_memSim (h : MemSim g) : MemSimOn (fun _ => True) g where
  load m _ := h.load m
  store m _ := h.store m
  store_inv _ _ _ _ _ _ _ := trivial

end Sim

/-! ## Byte views -/

theorem iteT {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem iteF {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem loadBytes_congr {f g : Nat → BitVec 8} {a b : Nat} :
    ∀ {k : Nat}, (∀ j, j < k → f (a + j) = g (b + j)) → loadBytes f a k = loadBytes g b k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [loadBytes]
    rw [show f a = g b by simpa using h 0 (by omega)]
    congr 2
    exact loadBytes_congr fun j hj => by
      rw [show a + 1 + j = a + (j + 1) by omega, show b + 1 + j = b + (j + 1) by omega]
      exact h (j + 1) (by omega)

theorem pack_take_drop (L : List (BitVec 8)) (f : Nat → BitVec 8)
    (hf : ∀ i (h : i < L.length), L[i] = f i) :
    ∀ (a k : Nat), a + k ≤ L.length → ListMem.pack ((L.drop a).take k) = loadBytes f a k
  | _, 0, _ => by simp [ListMem.pack, loadBytes]
  | a, k + 1, h => by
    rw [List.drop_eq_getElem_cons (by omega), List.take_succ_cons, ListMem.pack, loadBytes,
      hf a (by omega), pack_take_drop L f hf (a + 1) k (by omega)]

theorem getElem_encode : ∀ (k v j : Nat) (h : j < (ListMem.encode k v).length),
    (ListMem.encode k v)[j] = encByte v j
  | 0, _, _, h => by simp [ListMem.encode] at h
  | k + 1, v, 0, _ => by simp [ListMem.encode, encByte]
  | k + 1, v, j + 1, h => by
    simp only [ListMem.encode, List.getElem_cons_succ]
    rw [getElem_encode k (v / 256) j (by simpa [ListMem.encode] using h)]
    simp only [encByte, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem splice_eq (n : Nat) (f : Nat → BitVec 8) (a k v : Nat) (h : a + k ≤ n) :
    ((List.range n).map f).take a ++ ListMem.encode k v ++ ((List.range n).map f).drop (a + k) =
      (List.range n).map fun i => if a ≤ i ∧ i < a + k then encByte v (i - a) else f i := by
  apply List.ext_getElem
  · simp [length_encode]; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_append, List.length_take, List.length_map, List.length_range,
      length_encode, List.length_drop] at h1
    by_cases ha : i < a
    · rw [List.getElem_append_left (by simp [length_encode]; omega),
        List.getElem_append_left (by simp; omega)]
      simp; omega
    · by_cases hk : i < a + k
      · rw [List.getElem_append_left (by simp [length_encode]; omega),
          List.getElem_append_right (by simp; omega)]
        simp only [List.length_take, List.length_map, List.length_range]
        rw [getElem_encode]
        · simp only [Nat.min_eq_left (show a ≤ n by omega)]; rw [iteT (by omega)]
      · rw [List.getElem_append_right (by simp [length_encode]; omega)]
        simp only [List.getElem_drop, List.getElem_map, List.getElem_range, List.length_append,
          List.length_take, List.length_map, List.length_range, length_encode,
          Nat.min_eq_left (show a ≤ n by omega)]
        rw [iteF (by omega)]; congr 1; omega

theorem memSimOn_ofView {R : Type} [MemOps R] (inv : R → Prop) (size : R → Nat)
    (byte : R → Nat → BitVec 8)
    (hload : ∀ r, inv r → ∀ a k, MemOps.load r a k =
      if a + k ≤ size r then some (loadBytes (byte r) a k) else none)
    (hstore : ∀ r, inv r → ∀ a k v, a + k ≤ size r → ∃ r', MemOps.store r a k v = some r' ∧
      inv r' ∧ size r' = size r ∧
      ∀ i, i < size r → byte r' i = if a ≤ i ∧ i < a + k then encByte v (i - a) else byte r i)
    (hnone : ∀ r, inv r → ∀ a k v, ¬ a + k ≤ size r → MemOps.store r a k v = none) :
    MemSimOn inv (fun r => ListMem.ofView (size r) (byte r)) where
  load r hr a k := by
    rw [hload r hr]
    simp only [MemOps.load, ListMem.ofView, List.length_map, List.length_range]
    split
    · rw [pack_take_drop _ (byte r) (by simp) a k (by simpa)]
    · rfl
  store r hr a k v := by
    by_cases h : a + k ≤ size r
    · obtain ⟨r', h1, _, h3, h4⟩ := hstore r hr a k v h
      rw [h1]
      simp only [MemOps.store, ListMem.ofView, List.length_map, List.length_range, h,
        ↓reduceIte, Option.map_some, h3, splice_eq _ _ _ _ _ h, Option.some.injEq,
        ListMem.mk.injEq]
      apply List.map_congr_left
      intro i hi
      rw [h4 i (by simpa using hi)]
    · rw [hnone r hr a k v h]
      simp [MemOps.store, ListMem.ofView, h]
  store_inv r hr a k v r' hs := by
    by_cases h : a + k ≤ size r
    · obtain ⟨r'', h1, h2, _⟩ := hstore r hr a k v h
      rw [h1] at hs; cases hs; exact h2
    · rw [hnone r hr a k v h] at hs; cases hs

/-! ## Overlays -/

theorem logGet_append (l₁ l₂ : List (Nat × BitVec 8)) (i : Nat) :
    logGet (l₁ ++ l₂) i = (logGet l₁ i).or (logGet l₂ i) := by
  induction l₁ with
  | nil => simp [logGet]
  | cons e l ih => rcases e with ⟨j, b⟩; simp only [List.cons_append, logGet]; split <;> simp [ih]

theorem logGet_writesOf : ∀ (a k v i : Nat),
    logGet (writesOf a k v) i = if a ≤ i ∧ i < a + k then some (encByte v (i - a)) else none
  | a, 0, v, i => by simp [writesOf, logGet]
  | a, k + 1, v, i => by
    simp only [writesOf, logGet, logGet_writesOf (a + 1) k (v / 256) i]
    by_cases h : a = i
    · subst h; simp [encByte]
    · rw [iteF h]
      by_cases h2 : a + 1 ≤ i ∧ i < a + 1 + k
      · rw [iteT h2, iteT (by omega)]
        obtain ⟨j, rfl⟩ : ∃ j, i = a + 1 + j := ⟨i - (a + 1), by omega⟩
        simp only [encByte, Nat.div_div_eq_div_mul, show a + 1 + j - a = j + 1 by omega,
          Nat.pow_succ, Nat.mul_comm, show a + 1 + j - (a + 1) = j by omega]
      · rw [iteF h2, iteF (by omega)]

theorem memSimOn_overlay : MemSimOn (fun _ : Overlay => True) Overlay.toList := by
  apply memSimOn_ofView (fun _ => True) (fun o => o.base.size) Overlay.byte
  · intro r _ a k; rfl
  · intro r _ a k v h
    refine ⟨⟨r.base, writesOf a k v ++ r.log⟩, by simp [MemOps.store, h], trivial, rfl, ?_⟩
    intro i _
    simp only [Overlay.byte, logGet_append, logGet_writesOf]
    by_cases hi : a ≤ i ∧ i < a + k
    · rw [iteT hi, iteT hi]; rfl
    · rw [iteF hi, iteF hi]; rfl
  · intro r _ a k v h; simp [MemOps.store, h]

/-! ## Packed pages -/

theorem encByte_pack : ∀ (L : List (BitVec 8)) (x : Nat) (h : x < L.length),
    encByte (ListMem.pack L) x = L[x]
  | [], _, h => by simp at h
  | c :: L, 0, _ => by
    apply BitVec.eq_of_toNat_eq
    simp [encByte, ListMem.pack, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.isLt]
  | c :: L, x + 1, h => by
    rw [List.getElem_cons_succ, ← encByte_pack L x (by simpa using h)]
    simp only [encByte, ListMem.pack, Nat.pow_succ, Nat.mul_comm (256 ^ x) 256,
      ← Nat.div_div_eq_div_mul]
    congr 2
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt c.isLt, Nat.zero_add]

theorem encode_eq_map (P b : Nat) : ListMem.encode P b = (List.range P).map (encByte b) := by
  apply List.ext_getElem
  · simp [length_encode]
  · intro i h1 h2; rw [getElem_encode]; simp

theorem read_eq_loadBytes (b s : Nat) :
    ∀ (o k : Nat), NatMem.read ⟨b, s⟩ o k = loadBytes (encByte b) o k
  | _, 0 => by simp [NatMem.read, loadBytes, Nat.mod_one]
  | o, k + 1 => by
    rw [loadBytes, ← read_eq_loadBytes b s (o + 1) k]
    simp only [NatMem.read, encByte, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      two_pow_eight_mul]
    rw [show 256 ^ (k + 1) = 256 * 256 ^ k by rw [Nat.pow_succ, Nat.mul_comm], Nat.mod_mul,
      Nat.div_div_eq_div_mul, show 256 ^ o * 256 = 256 ^ (o + 1) by rw [Nat.pow_succ]]

theorem pageWrite_eq (b P o k v : Nat) (hb : b < 256 ^ P) (h : o + k ≤ P) :
    pageWrite b o k v = ListMem.pack
      ((ListMem.encode P b).take o ++ ListMem.encode k v ++ (ListMem.encode P b).drop (o + k)) := by
  have hl : (ListMem.encode P b).length = P := length_encode P b
  have hw := write_toNatMem (ListMem.encode P b) o k v (by omega)
  have hp : ListMem.pack (ListMem.encode P b) = b := by
    rw [pack_encode, Nat.mod_eq_of_lt hb]
  have := congrArg NatMem.bits hw
  simp only [ListMem.toNatMem, hp] at this
  exact this

theorem pageWrite_lt (b P o k v : Nat) (hb : b < 256 ^ P) (h : o + k ≤ P) :
    pageWrite b o k v < 256 ^ P := by
  rw [pageWrite_eq b P o k v hb h]
  have := pack_lt ((ListMem.encode P b).take o ++ ListMem.encode k v ++
    (ListMem.encode P b).drop (o + k))
  simp only [List.length_append, List.length_take, List.length_drop, length_encode] at this
  rwa [show min o P + k + (P - (o + k)) = P by omega] at this

theorem encByte_pageWrite (b P o k v x : Nat) (hb : b < 256 ^ P) (h : o + k ≤ P) (hx : x < P) :
    encByte (pageWrite b o k v) x =
      if o ≤ x ∧ x < o + k then encByte v (x - o) else encByte b x := by
  rw [pageWrite_eq b P o k v hb h, encode_eq_map P b, splice_eq P _ o k v h, encByte_pack _ _
    (by simpa using hx)]
  simp

/-! ## Page trees -/

theorem PTree.wf_zeros (P : Nat) : ∀ d, (PTree.zeros d).Wf P d
  | 0 => by simp [PTree.zeros, PTree.Wf]; exact Nat.pos_of_ne_zero (by simp)
  | d + 1 => ⟨PTree.wf_zeros P d, PTree.wf_zeros P d⟩

theorem PTree.get_lt {P : Nat} : ∀ {d : Nat} {t : PTree} (_ : t.Wf P d) (i : Nat),
    t.get d i < 256 ^ P
  | 0, .leaf _, h, _ => h
  | d + 1, .node _ _, h, i => by
    simp only [PTree.get]; split
    · exact PTree.get_lt h.1 _
    · exact PTree.get_lt h.2 _
  | 0, .node _ _, h, _ => h.elim
  | _ + 1, .leaf _, h, _ => h.elim

theorem PTree.wf_modify {P : Nat} {g : Nat → Nat} (hg : ∀ b, b < 256 ^ P → g b < 256 ^ P) :
    ∀ {d : Nat} {t : PTree} (_ : t.Wf P d) (i : Nat), (t.modify d i g).Wf P d
  | 0, .leaf b, h, _ => hg b h
  | d + 1, .node _ _, h, i => by
    simp only [PTree.modify]; split
    · exact ⟨PTree.wf_modify hg h.1 _, h.2⟩
    · exact ⟨h.1, PTree.wf_modify hg h.2 _⟩
  | 0, .node _ _, h, _ => h.elim
  | _ + 1, .leaf _, h, _ => h.elim

theorem PTree.get_modify {P : Nat} {g : Nat → Nat} :
    ∀ {d : Nat} {t : PTree} (_ : t.Wf P d) (i j : Nat), i < 2 ^ d → j < 2 ^ d →
      (t.modify d i g).get d j = if j = i then g (t.get d i) else t.get d j
  | 0, .leaf b, _, i, j, hi, hj => by
    simp at hi hj; subst hi; subst hj; simp [PTree.modify, PTree.get]
  | d + 1, .node l r, h, i, j, hi, hj => by
    simp only [PTree.modify]
    by_cases hi' : i < 2 ^ d <;> by_cases hj' : j < 2 ^ d <;>
      simp only [hi', hj', ↓reduceIte, PTree.get]
    · exact PTree.get_modify h.1 i j hi' hj'
    · rw [iteF (by omega)]
    · rw [iteF (by omega)]
    · rw [PTree.get_modify h.2 (i - 2 ^ d) (j - 2 ^ d) (by rw [Nat.pow_succ] at hi; omega)
        (by rw [Nat.pow_succ] at hj; omega)]
      by_cases e : j = i
      · subst e; simp
      · rw [iteF (by omega), iteF e]
  | 0, .node _ _, h, _, _, _, _ => h.elim
  | _ + 1, .leaf _, h, _, _, _, _ => h.elim

theorem PTree.get_modify_id {g : Nat → Nat} (hg : ∀ b, g b = b) :
    ∀ (d : Nat) (t : PTree) (i j : Nat), (t.modify d i g).get d j = t.get d j
  | 0, .leaf b, _, _ => by simp [PTree.modify, PTree.get, hg]
  | d + 1, .node l r, i, j => by
    simp only [PTree.modify]; split <;> simp only [PTree.get] <;> split <;>
      simp [PTree.get_modify_id hg]
  | 0, .node _ _, _, _ => rfl
  | _ + 1, .leaf _, _, _ => rfl

theorem pageWrite_zero (b o v : Nat) : pageWrite b o 0 v = b := by
  simp [pageWrite, NatMem.write, NatMem.read, Nat.mod_one]

/-! ## Page memories -/

theorem divmod_add {P a j : Nat} (hP : 0 < P) (h : a % P + j < P) :
    (a + j) / P = a / P ∧ (a + j) % P = a % P + j := by
  have e : a + j = (a % P + j) + P * (a / P) := by have := Nat.mod_add_div a P; omega
  rw [e, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt h, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt h]
  simp

theorem pageSize_pos (m : PageMem) : 0 < m.pageSize := Nat.pow_pos (by decide)

theorem div_lt_depth (m : PageMem) {x : Nat} (hx : x < m.size) :
    x / m.pageSize < 2 ^ m.depth :=
  (Nat.div_lt_iff_lt_mul (pageSize_pos m)).2 hx

/-- A page memory with page `a / pageSize` rewritten by `pageWrite`. -/
def modifyAt (m : PageMem) (a k v : Nat) : PageMem :=
  { m with tree := m.tree.modify m.depth (a / m.pageSize) (fun b => pageWrite b (a % m.pageSize) k v) }

/-- The fast-path store: one page rewritten. -/
theorem byte_modifyAt (m : PageMem) (hm : m.Wf) (a k v : Nat) (ha : a + k ≤ m.size)
    (hk : a % m.pageSize + k ≤ m.pageSize) (x : Nat) (hx : x < m.size) :
    (modifyAt m a k v).byte x = if a ≤ x ∧ x < a + k then encByte v (x - a) else m.byte x := by
  have hP := pageSize_pos m
  have hxq := div_lt_depth m hx
  by_cases hk0 : k = 0
  · subst hk0
    rw [iteF (by omega)]
    simp only [modifyAt, PageMem.byte, PageMem.page]
    rw [PTree.get_modify_id (fun b => pageWrite_zero b _ v)]
    rfl
  have haq := div_lt_depth m (show a < m.size by omega)
  simp only [modifyAt, PageMem.byte, PageMem.page, PageMem.pageSize] at *
  rw [PTree.get_modify hm _ _ haq hxq]
  have hxa := Nat.mod_add_div x (2 ^ m.pbits)
  have haa := Nat.mod_add_div a (2 ^ m.pbits)
  have hxm := Nat.mod_lt x hP
  by_cases e : x / 2 ^ m.pbits = a / 2 ^ m.pbits
  · rw [iteT e, encByte_pageWrite _ _ _ _ _ _ (PTree.get_lt hm _) hk hxm]
    rw [e] at hxa
    by_cases c : a ≤ x ∧ x < a + k
    · rw [iteT c, iteT (by omega)]; congr 1; omega
    · rw [iteF c, iteF (by omega), e]
  · rw [iteF e, iteF]
    intro ⟨c1, c2⟩
    apply e
    have := (divmod_add (a := a) (j := x - a) hP (by omega)).1
    rwa [show a + (x - a) = x by omega] at this

theorem wf_modifyAt (m : PageMem) (hm : m.Wf) (a k v : Nat)
    (hk : a % m.pageSize + k ≤ m.pageSize) : (modifyAt m a k v).Wf :=
  PTree.wf_modify (fun b hb => pageWrite_lt b _ _ k v hb hk) hm _

theorem setBytes_spec : ∀ (k : Nat) (m : PageMem) (a v : Nat), m.Wf → a + k ≤ m.size →
    (m.setBytes a v k).Wf ∧ (m.setBytes a v k).size = m.size ∧
      ∀ x, x < m.size → (m.setBytes a v k).byte x =
        if a ≤ x ∧ x < a + k then encByte v (x - a) else m.byte x
  | 0, m, a, v, hm, _ => ⟨hm, rfl, fun x _ => by
      simp only [PageMem.setBytes]; rw [iteF (by omega)]⟩
  | k + 1, m, a, v, hm, ha => by
    have h1 : a % m.pageSize + 1 ≤ m.pageSize := Nat.mod_lt _ (pageSize_pos m)
    have hw := wf_modifyAt m hm a 1 v h1
    obtain ⟨w, s, b⟩ := setBytes_spec k (modifyAt m a 1 v) (a + 1) (v / 256) hw
      (by simp only [modifyAt, PageMem.size, PageMem.pageSize] at *; omega)
    refine ⟨w, s, fun x hx => ?_⟩
    simp only [PageMem.setBytes]
    change (PageMem.setBytes (modifyAt m a 1 v) (a + 1) (v / 256) k).byte x = _
    rw [b x hx, byte_modifyAt m hm a 1 v (by omega) h1 x hx]
    by_cases c : a + 1 ≤ x ∧ x < a + 1 + k
    · rw [iteT c, iteT (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, x = a + 1 + j := ⟨x - (a + 1), by omega⟩
      simp only [encByte, Nat.div_div_eq_div_mul, show a + 1 + j - a = j + 1 by omega,
        Nat.pow_succ, Nat.mul_comm, show a + 1 + j - (a + 1) = j by omega]
    · rw [iteF c]
      by_cases d : x = a
      · subst d; rw [iteT (by omega), iteT (by omega)]
      · rw [iteF (by omega), iteF (by omega)]

theorem memSimOn_pageMem : MemSimOn PageMem.Wf PageMem.toList := by
  apply memSimOn_ofView PageMem.Wf PageMem.size PageMem.byte
  · intro m _ a k
    simp only [MemOps.load]
    split
    · split
      · rename_i h1 h2
        congr 1
        rw [read_eq_loadBytes]
        apply loadBytes_congr
        intro j hj
        have := divmod_add (a := a) (j := j) (pageSize_pos m) (by omega)
        simp only [PageMem.byte, PageMem.page, this.1, this.2]
      · rfl
    · rfl
  · intro m hm a k v h
    simp only [MemOps.store, h, ↓reduceIte]
    split
    · rename_i hk
      exact ⟨modifyAt m a k v, rfl, wf_modifyAt m hm a k v hk, rfl,
        byte_modifyAt m hm a k v h hk⟩
    · exact ⟨_, rfl, setBytes_spec k m a v hm h⟩
  · intro m _ a k v h; simp [MemOps.store, h]

theorem wf_zeros (pbits depth : Nat) : (PageMem.zeros pbits depth).Wf :=
  PTree.wf_zeros _ _

theorem PTree.get_zeros : ∀ (d i : Nat), (PTree.zeros d).get d i = 0
  | 0, _ => rfl
  | d + 1, i => by simp only [PTree.zeros, PTree.get]; split <;> exact PTree.get_zeros d _

theorem ofView_zero (n : Nat) (f : Nat → BitVec 8) (hf : ∀ i, f i = 0) :
    ListMem.ofView n f = ⟨List.replicate n 0⟩ := by
  simp only [ListMem.ofView, ListMem.mk.injEq]
  apply List.ext_getElem <;> simp [hf]

theorem overlay_zeros_toList (n : Nat) :
    (Overlay.ofBase (NatMem.zeros n)).toList = ⟨List.replicate n 0⟩ :=
  ofView_zero _ _ fun i => by simp [Overlay.byte, Overlay.ofBase, logGet, NatMem.zeros, NatMem.read]

theorem pageMem_zeros_toList (pbits depth : Nat) :
    (PageMem.zeros pbits depth).toList = ⟨List.replicate (2 ^ depth * 2 ^ pbits) 0⟩ :=
  ofView_zero _ _ fun i => by
    simp [PageMem.byte, PageMem.page, PageMem.zeros, PTree.get_zeros, encByte]

end Silmaril.Proofs.Wasm.KernelEval