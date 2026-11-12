module

public import Silmaril.Wasm.KernelEval.Defs

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: proofs

Statements in `Silmaril.Wasm.KernelEval.Thms`.
-/

namespace Silmaril.Proofs.Wasm.KernelEval

open Silmaril.Wasm.KernelEval

variable {M : Type} [MemOps M]

theorem runRec_eq_run (n : Nat) (c : Config M) : runRec n c = run n c := by
  rw [runRec_eq_run_csimp]

theorem run_add (a b : Nat) (c : Config M) :
    run (a + b) c = (run a c).andThen (run b) := by
  induction a generalizing c with
  | zero => simp [run, Result.andThen]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp only [run]
    split
    · exact ih _
    · rename_i r _ _; cases r <;> simp_all [Result.andThen]

/-! ## Memory simulations lift to runs -/

section Sim

variable {N : Type} [MemOps N] {g : M → N}

omit [MemOps M] [MemOps N] in
theorem branch_mapMem (c : Config M) (l : Nat) :
    branch (c.mapMem g) l = (branch c l).mapMem g := by
  simp only [branch, Config.mapMem]
  split <;> simp_all [Result.mapMem, Config.mapMem]
theorem step_mapMem (h : MemSim g) (c : Config M) :
    step (c.mapMem g) = (step c).mapMem g := by
  rcases c with ⟨code, stk, labels, locals, mem⟩
  cases code with
  | nil => cases labels <;> rfl
  | cons i rest =>
    cases i <;> (rcases stk with _ | ⟨v, _ | ⟨w, _ | ⟨u, stk⟩⟩⟩) <;>
      simp only [step, Config.mapMem, h.load, h.store] <;> (try rfl) <;>
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

theorem run_mapMem (h : MemSim g) (n : Nat) (c : Config M) :
    run n (c.mapMem g) = (run n c).mapMem g := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [run, step_mapMem h]
    cases step c <;> simp [Result.mapMem, ih]

end Sim

/-! ## The packed memory simulates the list memory -/

theorem pack_append (xs ys : List (BitVec 8)) :
    ListMem.pack (xs ++ ys) = ListMem.pack xs + 256 ^ xs.length * ListMem.pack ys := by
  induction xs with
  | nil => simp [ListMem.pack]
  | cons x xs ih => simp only [List.cons_append, ListMem.pack, ih, List.length_cons,
      Nat.pow_succ, Nat.mul_add, Nat.add_assoc]; congr 2; rw [Nat.mul_comm (256 ^ _) 256,
      Nat.mul_assoc]

theorem pack_lt (l : List (BitVec 8)) : ListMem.pack l < 256 ^ l.length := by
  induction l with
  | nil => simp [ListMem.pack]
  | cons b l ih =>
    simp only [ListMem.pack, List.length_cons, Nat.pow_succ]
    have := b.isLt
    have : ListMem.pack l + 1 ≤ 256 ^ l.length := ih
    have : 256 * (ListMem.pack l + 1) ≤ 256 * 256 ^ l.length := Nat.mul_le_mul_left _ this
    simp only [Nat.mul_add] at this
    have h2 : (2 : Nat) ^ 8 = 256 := rfl
    rw [h2] at *; rw [Nat.mul_comm (256 ^ _)]; omega

theorem length_encode (k v : Nat) : (ListMem.encode k v).length = k := by
  induction k generalizing v <;> simp_all [ListMem.encode]

theorem pack_encode (k v : Nat) : ListMem.pack (ListMem.encode k v) = v % 256 ^ k := by
  induction k generalizing v with
  | zero => simp [ListMem.encode, ListMem.pack, Nat.mod_one]
  | succ k ih =>
    have h8 : (2 : Nat) ^ 8 = 256 := rfl
    rw [ListMem.encode, ListMem.pack, ih, BitVec.toNat_ofNat, h8, Nat.pow_succ,
      Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]

theorem two_pow_eight_mul (a : Nat) : 2 ^ (8 * a) = 256 ^ a := by
  rw [Nat.pow_mul]

theorem pack_split (l : List (BitVec 8)) (a : Nat) (h : a ≤ l.length) :
    ListMem.pack l = ListMem.pack (l.take a) + 256 ^ a * ListMem.pack (l.drop a) := by
  conv => lhs; rw [← List.take_append_drop a l]
  rw [pack_append, List.length_take, Nat.min_eq_left h]

theorem read_toNatMem (l : List (BitVec 8)) (a k : Nat) (h : a + k ≤ l.length) :
    (ListMem.toNatMem ⟨l⟩).read a k = ListMem.pack ((l.drop a).take k) := by
  simp only [NatMem.read, ListMem.toNatMem, Nat.shiftRight_eq_div_pow, two_pow_eight_mul]
  rw [pack_split l a (by omega)]
  have hP := pack_lt (l.take a)
  rw [List.length_take, Nat.min_eq_left (by omega)] at hP
  rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hP,
    Nat.zero_add]
  have hd : k ≤ (l.drop a).length := by simp; omega
  rw [pack_split (l.drop a) k hd]
  have hW := pack_lt ((l.drop a).take k)
  rw [List.length_take, Nat.min_eq_left hd] at hW
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hW]

theorem write_toNatMem (l : List (BitVec 8)) (a k v : Nat) (h : a + k ≤ l.length) :
    (ListMem.toNatMem ⟨l⟩).write a k v =
      ListMem.toNatMem ⟨l.take a ++ ListMem.encode k v ++ l.drop (a + k)⟩ := by
  have hr := read_toNatMem l a k h
  simp only [NatMem.write, hr]
  simp only [ListMem.toNatMem, NatMem.mk.injEq]
  constructor
  · rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, two_pow_eight_mul, two_pow_eight_mul,
      pack_split l a (by omega), pack_split (l.drop a) k (by simp; omega), List.drop_drop]
    simp only [pack_append, pack_encode, List.length_append, length_encode, List.length_take,
      Nat.min_eq_left (show a ≤ l.length by omega), Nat.pow_add]
    rw [Nat.mul_comm _ (256 ^ a), Nat.mul_comm _ (256 ^ a), Nat.mul_add (256 ^ a),
      Nat.mul_assoc (256 ^ a)]
    generalize 256 ^ a * ListMem.pack (List.take k (List.drop a l)) = X
    omega
  · simp [length_encode]; omega

theorem memSim_toNatMem : MemSim ListMem.toNatMem where
  load m a k := by
    rcases m with ⟨l⟩
    by_cases h : a + k ≤ l.length
    · simp [MemOps.load, h, ← read_toNatMem l a k h, ListMem.toNatMem]
    · simp [MemOps.load, h, ListMem.toNatMem]
  store m a k v := by
    rcases m with ⟨l⟩
    by_cases h : a + k ≤ l.length
    · have hs : (ListMem.toNatMem ⟨l⟩).size = l.length := rfl
      simp only [MemOps.store, hs, h, ↓reduceIte, Option.map_some, write_toNatMem l a k v h]
    · simp [MemOps.store, h, ListMem.toNatMem]

theorem pack_replicate_zero (n : Nat) : ListMem.pack (List.replicate n 0) = 0 := by
  induction n <;> simp_all [List.replicate, ListMem.pack]

theorem zeros_eq (n : Nat) : (⟨List.replicate n 0⟩ : ListMem).toNatMem = NatMem.zeros n := by
  simp only [ListMem.toNatMem, NatMem.zeros, List.length_replicate]
  rw [pack_replicate_zero]

/-! ## Checks -/

omit [MemOps M] in
theorem top?_mapMem {N : Type} (g : M → N) (r : Result M) : (r.mapMem g).top? = r.top? := by
  rcases r with _ | ⟨_ | _, _, _⟩ | _ | _ <;> rfl

theorem returns_toNatMem (fuel : Nat) (body : List Instr) (locals : List (BitVec 32))
    (m : ListMem) (v : BitVec 32) :
    returns fuel body locals m.toNatMem v = returns fuel body locals m v := by
  have : Config.init body locals m.toNatMem = (Config.init body locals m).mapMem ListMem.toNatMem :=
    rfl
  simp only [returns, runRec_eq_run, this, run_mapMem memSim_toNatMem, top?_mapMem]

theorem run_of_returns {fuel : Nat} {body : List Instr} {locals : List (BitVec 32)} {m : M}
    {v : BitVec 32} (h : returns fuel body locals m v = true) :
    ∃ s ls m', run fuel (Config.init body locals m) = .done (v :: s) ls m' := by
  simp only [returns, runRec_eq_run] at h
  generalize run fuel (Config.init body locals m) = r at h
  rcases r with _ | ⟨_ | ⟨w, s⟩, ls, m'⟩ | _ | _ <;> simp_all [Result.top?]

end Silmaril.Proofs.Wasm.KernelEval
