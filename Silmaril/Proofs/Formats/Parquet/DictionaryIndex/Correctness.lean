module

public import Silmaril.Formats.Parquet.DictionaryIndex.Defs
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Hybrid.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.DictionaryIndex

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.DictionaryIndex

private theorem mapError_ok_iff {ε δ α : Type} {action : Except ε α} {f : ε → δ} {value : α} :
    action.mapError f = .ok value ↔ action = .ok value := by
  cases action <;> simp [Except.mapError]

private theorem bind_ok_iff {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} :
    (action >>= next) = .ok output ↔
      ∃ input, action = .ok input ∧ next input = .ok output := by
  cases action <;> simp [Bind.bind, Except.bind]

public theorem readIndices_ok_iff {limits : Hybrid.Limits} {expected : Nat} {source : Bytes}
    {indices : List Nat} :
    readIndices limits expected source = .ok indices ↔
      source.length ≤ limits.bytes ∧
      ∃ width : UInt8, ∃ runs : List UInt8,
        source.toList = width :: runs ∧ width.toNat ≤ 32 ∧
        expected < Hybrid.runLimit ∧ expected ≤ limits.values ∧
        Hybrid.Wire width.toNat expected runs indices := by
  constructor
  · intro h
    unfold readIndices at h
    split at h
    · contradiction
    · rename_i limit
      cases bytes : source.toList with
      | nil => rw [bytes] at h; contradiction
      | cons width runs =>
        rw [bytes] at h
        obtain ⟨widthBound, countBound, countLimit, _, wire⟩ :=
          Hybrid.decode_ok_iff.mp (mapError_ok_iff.mp h)
        exact ⟨by omega, width, runs, rfl, widthBound, countBound, countLimit,
          by simpa only [Bytes.toList_ofList] using wire⟩
  · rintro ⟨limit, width, runs, bytes, widthBound, countBound, countLimit, wire⟩
    have tailLimit : (Bytes.ofList runs).length ≤ limits.bytes := by
      have extent := congrArg List.length bytes
      simp only [Bytes.length_toList, List.length_cons] at extent
      simp only [Bytes.length_ofList]
      omega
    rw [readIndices, ite_eq_right (Nat.not_lt_of_ge limit), bytes]
    exact mapError_ok_iff.mpr (Hybrid.decode_ok_iff.mpr
      ⟨widthBound, countBound, countLimit, tailLimit, by simpa only [Bytes.toList_ofList] using wire⟩)

public theorem select_ok_iff {α : Type} {dictionary : Array α} {indices : List Nat}
    {values : List α} :
    select dictionary indices = .ok values ↔
      indices.map (fun index => dictionary[index]?) = values.map some := by
  induction indices generalizing values with
  | nil => cases values <;> simp [select, Pure.pure, Except.pure]
  | cons index indices ih =>
    rw [select, List.mapM_cons, bind_ok_iff]
    constructor
    · rintro ⟨value, hit, tail⟩
      obtain ⟨rest, read, same⟩ := bind_ok_iff.mp tail
      change Except.ok (value :: rest) = .ok values at same
      cases same
      have entry : dictionary[index]? = some value := by
        cases find : dictionary[index]? with
        | none => simp [find] at hit
        | some entry => simpa [find] using hit
      simp [entry, ih.mp read]
    · intro mapped
      cases values with
      | nil => simp at mapped
      | cons value rest =>
        obtain ⟨entry, tail⟩ := List.cons.inj mapped
        exact ⟨value, by simp [entry], bind_ok_iff.mpr ⟨rest, ih.mpr tail, rfl⟩⟩

public theorem select_indices_lt {α : Type} {dictionary : Array α} {indices : List Nat}
    {values : List α} (selected : select dictionary indices = .ok values)
    {index : Nat} (member : index ∈ indices) : index < dictionary.size := by
  by_contra bound
  have absent : dictionary[index]? = none := getElem?_neg dictionary index bound
  have missed : dictionary[index]? ∈ indices.map (fun i => dictionary[i]?) :=
    List.mem_map_of_mem member
  rw [select_ok_iff.mp selected, absent] at missed
  simp at missed

public theorem decode_ok_iff {α : Type} {dictionary : Array α} {params : ScalarPage.Parameters}
    {pageLimits : ScalarPage.Limits} {indexLimits : Hybrid.Limits} {source : Bytes}
    {output : List (Option α)} :
    decode dictionary params pageLimits indexLimits source = .ok output ↔
      (params.encoding = 8 ∨ params.encoding = 2) ∧
      ∃ page indices,
        ScalarPage.prepareFor params.encoding params pageLimits source = .ok page ∧
        readIndices indexLimits (page.mask.count true) page.scalars = .ok indices ∧
        output.map Option.isSome = page.mask ∧
        indices.map (fun index => dictionary[index]?) = (output.filterMap id).map some := by
  unfold decode
  split
  · rename_i encoding
    constructor
    · intro h
      obtain ⟨page, prepared, h⟩ := bind_ok_iff.mp h
      obtain ⟨indices, read, h⟩ := bind_ok_iff.mp h
      obtain ⟨values, selected, h⟩ := bind_ok_iff.mp h
      obtain ⟨shape, order⟩ := FlatPage.reconstruct_ok_iff.mp (mapError_ok_iff.mp h)
      exact ⟨encoding, page, indices, mapError_ok_iff.mp prepared, read, shape,
        order ▸ select_ok_iff.mp selected⟩
    · rintro ⟨_, page, indices, prepared, read, shape, selection⟩
      refine bind_ok_iff.mpr ⟨page, mapError_ok_iff.mpr prepared, ?_⟩
      refine bind_ok_iff.mpr ⟨indices, read, ?_⟩
      refine bind_ok_iff.mpr ⟨output.filterMap id, select_ok_iff.mpr selection, ?_⟩
      exact mapError_ok_iff.mpr (FlatPage.reconstruct_ok_iff.mpr ⟨shape, rfl⟩)
  · rename_i encoding
    constructor
    · intro h
      contradiction
    · exact fun h => (encoding h.1).elim

public theorem decode_counts {α : Type} {dictionary : Array α} {params : ScalarPage.Parameters}
    {pageLimits : ScalarPage.Limits} {indexLimits : Hybrid.Limits} {source : Bytes}
    {output : List (Option α)} (h : decode dictionary params pageLimits indexLimits source = .ok output) :
    output.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (output.filterMap id).length = params.numValues - nulls := by
  obtain ⟨_, page, _, prepared, _, shape, _⟩ := decode_ok_iff.mp h
  obtain ⟨length, counts⟩ := ScalarPage.preparedFor_counts prepared
  refine ⟨?_, ?_⟩
  · have slots := congrArg List.length shape
    rwa [List.length_map, length] at slots
  · have reconstruct := FlatPage.reconstruct_ok_iff.mpr ⟨shape, rfl⟩
    have present := (FlatPage.reconstruct_exists_iff page.mask (output.filterMap id)).mp
      ⟨output, reconstruct⟩
    cases version : params.version with
    | v1 => trivial
    | v2 =>
      rw [version] at counts
      exact present.symm.trans counts

public theorem readValues_wire {α : Type} {limits : Hybrid.Limits} {dictionary : Array α}
    {count : Nat} {source : Bytes} {values : List α}
    (accepted : readValues limits dictionary count source = .ok values) :
    ValuesWire limits dictionary count source values := by
  unfold readValues at accepted
  cases read : readIndices limits count source with
  | error cause => simp [read, Bind.bind, Except.bind] at accepted
  | ok indices =>
    have selected : select dictionary indices = .ok values := by
      simpa [read, Bind.bind, Except.bind] using accepted
    obtain ⟨cap, width, runs, exact, widthCap, runCap, countCap, hybrid⟩ := readIndices_ok_iff.mp read
    exact ⟨width, runs, indices, exact, widthCap, cap, countCap, runCap, hybrid,
      fun _ member => select_indices_lt selected member, select_ok_iff.mp selected⟩

end Silmaril.Proofs.Formats.Parquet.DictionaryIndex
