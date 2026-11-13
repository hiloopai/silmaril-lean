module

public import Silmaril.Wasm.Logic.Sep.Memory.Defs
public import Silmaril.Wasm.Logic.Hoare.Memory.Thms
public import Silmaril.Wasm.Logic.Memory.Thms

@[expose] public section
namespace Silmaril.Wasm.Logic.Sep
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome store_eq storeLE getElem?_store)
open Silmaril.Wasm.Logic.Hoare (HWP)
variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem bytes_self {m p k : Nat} {bs : List UInt8} {b : UInt8}
    (hk : bs[k]? = some b) : Heap.bytes m p bs (.byte m (p + k)) = some (.byte b) := by
  simp [Heap.bytes, hk]

theorem cellOf_byte {s : Store H} {m i : Nat} {b : UInt8}
    (h : cellOf s (.byte m i) = some (.byte b)) :
    ∃ mi, s.mems[m]? = some mi ∧ mi.bytes.data.toList[i]? = some b := by
  have he (B : ByteArray) (j : Nat) : B[j]? = B.data.toList[j]? := by
    rw [Array.getElem?_toList]; rfl
  rcases hm : s.mems[m]? with _ | mi <;> simp [cellOf, hm, he] at h
  exact ⟨mi, rfl, by simpa only [Array.getElem?_toList] using h⟩

/-- Ownership of four bytes proves existence and bounds in the actual store. -/
theorem bytes_four_bounds {s : Store H} {m p : Nat} {bs : List UInt8}
    (hn : bs.length = 4) (hs : Heap.Sat s (Heap.bytes m p bs)) :
    ∃ mi, s.mems[m]? = some mi ∧ p + 4 ≤ mi.bytes.size := by
  have hk : 3 < bs.length := by omega
  obtain ⟨mi, hm, hb⟩ := cellOf_byte (hs _ _ (bytes_self (List.getElem?_eq_getElem hk)))
  refine ⟨mi, hm, ?_⟩
  have hi := (List.getElem?_eq_some_iff.mp hb).1
  simp only [Array.length_toList, ByteArray.size_data] at hi
  omega

/-- New and old byte ranges have the same ownership domain. -/
theorem bytes_disj {m p : Nat} {bs cs : List UInt8} {hF : Heap}
    (hn : cs.length = bs.length) (hd : Heap.Disj (Heap.bytes m p bs) hF) :
    Heap.Disj (Heap.bytes m p cs) hF := by
  intro l
  rcases hd l with h | h
  · left
    cases l <;> simp only [Heap.bytes] at h ⊢
    split_ifs with hi
    · simp only [ite_eq_left hi] at h
      simpa [Option.map_eq_none_iff, List.getElem?_eq_none_iff, hn] using h
    · rfl
  · exact .inr h

theorem byteArray_getElem? (B : ByteArray) (i : Nat) : B[i]? = B.data.toList[i]? := by
  rw [Array.getElem?_toList]
  rfl

theorem cellOf_setMem_byte {s : Store H} {m j : Nat} {mi : MemInst} {B : ByteArray}
    (hm : s.mems[m]? = some mi) :
    cellOf (s.setMem m {mi with bytes := B}) (.byte m j) = B.data.toList[j]?.map Cell.byte := by
  have hl := (List.getElem?_eq_some_iff.mp hm).1
  simp [cellOf, Store.setMem, hl, byteArray_getElem?]

/-- Every old frame cell survives, including other bytes of the written memory. -/
theorem sat_store_frame {s : Store H} {m p : Nat} {mi : MemInst} {B : ByteArray}
    {bs : List UInt8} {v : BitVec 32} {hF : Heap}
    (hm : s.mems[m]? = some mi) (hn : bs.length = 4)
    (hs : Memory.store mi.bytes p (count := 4) v = some B)
    (hd : Heap.Disj (Heap.bytes m p bs) hF) (hf : Heap.Sat s hF) :
    Heap.Sat (s.setMem m {mi with bytes := B}) hF := by
  intro l c hc
  have hold := hf l c hc
  cases l with
  | byte m' j =>
    by_cases he : m' = m
    · subst m'
      have hout : ¬ (p ≤ j ∧ j < p + 4) := by
        intro hin
        have hk : j - p < bs.length := by omega
        rcases hd (.byte m j) with hb | hb
        · simp [Heap.bytes, hin.1, List.getElem?_eq_getElem hk] at hb
        · rw [hb] at hc; contradiction
      rw [cellOf_setMem_byte hm, getElem?_store hs, ite_eq_right hout]
      simpa [cellOf, hm, byteArray_getElem?] using hold
    · simpa [cellOf, Store.setMem, List.getElem?_set_ne (Ne.symm he)] using hold
  | _ => exact hold

/-- The written footprint holds the actual little-endian result. -/
theorem sat_store_bytes {s : Store H} {m p : Nat} {mi : MemInst} {B : ByteArray}
    {v : BitVec 32} (hm : s.mems[m]? = some mi)
    (hs : Memory.store mi.bytes p (count := 4) v = some B) :
    Heap.Sat (s.setMem m {mi with bytes := B})
      (Heap.bytes m p (Memory.encodeLE 4 v.toNat).data.toList) := by
  intro l c hc
  cases l with
  | byte m' j =>
    simp only [Heap.bytes] at hc
    split_ifs at hc with hi
    · obtain ⟨rfl, hp⟩ := hi
      have hk : j - p < (Memory.encodeLE 4 v.toNat).data.toList.length := by
        by_contra h
        simp [List.getElem?_eq_none (by omega : (Memory.encodeLE 4 v.toNat).data.toList.length ≤ j - p)] at hc
      have hk' : j - p < 4 := by simpa using hk
      have hj : p ≤ j ∧ j < p + 4 := ⟨hp, by omega⟩
      rw [cellOf_setMem_byte hm, getElem?_store hs, ite_eq_left hj]
      exact hc
  | _ => simp [Heap.bytes] at hc

/-- Full-width i32 store, with actual memory-index resolution and effective offset. -/
theorem STriple.i32Store {a : AddrType} {i : BitVec a.intType.width} {v : BitVec 32}
    {x : MemIdx} {arg : MemArg} {m : Nat} {bs : List UInt8} (hn : bs.length = 4) :
    STriple P host
      (fun f h => f.module.mems[x.toNat]? = some m ∧
        bytesPts m (effAddr i.toNat arg) bs h)
      (vals [.num ⟨.int a.intType, i⟩, .num ⟨.int .i32, v⟩] ++
        [.plain (.intStore .i32 none x arg)])
      (fun _ o h => o = .normal [] ∧
        bytesPts m (effAddr i.toNat arg) (Memory.encodeLE 4 v.toNat).data.toList h) := by
  rintro s f _ hF hd hsat ⟨hx, rfl⟩
  have hp : Heap.Sat s (Heap.bytes m (effAddr i.toNat arg) bs) := Heap.Sat.left hsat
  obtain ⟨mi, hm, hb⟩ := bytes_four_bounds hn hp
  have hmem : s.mem? f x = some (m, mi) := by simp [Store.mem?, hx, hm]
  have hs : Memory.store mi.bytes (effAddr i.toNat arg) (count := 4) v =
      some (storeLE mi.bytes (effAddr i.toNat arg) 4 v.toNat) := store_eq (n := 4) v hb
  have hp' : ∃ vs args c₀,
      [.num ⟨.int a.intType, i⟩, .num ⟨.int .i32, v⟩] = vs ++ args ∧
        SingleThreaded.Det.Head P s f args (.plain (.intStore .i32 none x arg)) c₀ :=
    ⟨[], _, _, rfl, .memory (.storeIntVal hmem (by simpa [IntType.width] using hs))⟩
  change HWP P host s f
    (vals [.num ⟨.int a.intType, i⟩, .num ⟨.int .i32, v⟩] ++
      .plain (.intStore .i32 none x arg) :: []) _
  refine HWP.head ⟨rfl, by simp, rfl⟩ hp' ?_
  intro us args c₀ hW hh
  obtain ⟨a', i', v', m', mi', rfl, hm', hr⟩ := Silmaril.Wasm.Logic.Hoare.head_intStore hh
  obtain ⟨rfl, hv₁, hv₂⟩ := Silmaril.Wasm.Logic.Hoare.split_two (us := []) hW
  obtain ⟨rfl, hi⟩ := Silmaril.Wasm.Logic.Hoare.addr_arg_inj hv₁
  obtain rfl := eq_of_heq hi
  obtain rfl : v' = v := Silmaril.Wasm.Logic.Hoare.numVal_int_inj (Val.num.inj hv₂)
  have hmm : (m', mi') = (m, mi) := by rw [hmem] at hm'; exact (Option.some.inj hm').symm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmm
  rcases hr with ⟨hlt, -⟩ | ⟨B, hs', rfl⟩
  · simp only [IntType.width, effAddr] at hlt hb
    omega
  · show HWP P host (s.setMem m' {mi' with bytes := B}) f (vals []) _
    have hs'' : Memory.store mi'.bytes (effAddr i'.toNat arg) (count := 4) v' = some B := by
      have hv : v'.setWidth 32 = v' := BitVec.setWidth_eq v'
      change Memory.store mi'.bytes (effAddr i'.toNat arg) (count := 4) (v'.setWidth 32) = some B at hs'
      rw [hv] at hs'
      exact hs'
    have hnew : Heap.Sat (s.setMem m' {mi' with bytes := B})
        (Heap.bytes m' (effAddr i'.toNat arg) (Memory.encodeLE 4 v'.toNat).data.toList) :=
      sat_store_bytes hm hs''
    have hframe : Heap.Sat (s.setMem m' {mi' with bytes := B}) hF :=
      sat_store_frame hm hn hs'' hd (Heap.Sat.right hd hsat)
    have hdis : Heap.Disj
        (Heap.bytes m' (effAddr i'.toNat arg) (Memory.encodeLE 4 v'.toNat).data.toList) hF :=
      bytes_disj (cs := (Memory.encodeLE 4 v'.toNat).data.toList) (by simpa using hn.symm) hd
    apply HWP.of_vals
    refine ⟨_, hdis, ?_, rfl, rfl⟩
    intro l c hc
    rcases Heap.union_some hc with hc | ⟨_, hc⟩
    · exact hnew l c hc
    · exact hframe l c hc

end Silmaril.Wasm.Logic.Sep
