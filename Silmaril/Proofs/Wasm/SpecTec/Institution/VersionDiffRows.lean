module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionCountRows
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffCounts
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffCounts30
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffWasm10Fixed_000
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffWasm10Fixed_033
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffWasm10Fixed_066
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffWasm10Fixed_099
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain10_000
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain10_033
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain10_066
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain10_099
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain20_000
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain20_032
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain20_064
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain20_096
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain20_128
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain20_160
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain20_192
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain20_224
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_000
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_020
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_040
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_060
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_080
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_100
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_120
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_140
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_160
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_180
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_200
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_220
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_240
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_260
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_280
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_300
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_320
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_340
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_360
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_380
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_400
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_420
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_440
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_460
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_480
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_500
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_520
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMain30_540
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMetaILa
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffMetaILb

/-!
# The remaining `theory-diff` rows, assembled

The chunk checks (`check_*`) cover every rule of the earlier script; with the rule totals they
give, for each row, the exact dropped set (`dropped_*`) and the retained count (`retained_*`),
the numbers `spectec-gen theory-diff` reports. No script is evaluated here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Versions

open Silmaril.Wasm.SpecTec.Scripts

/-! ## wasm-1.0 original → fixed -/

theorem all_wasm10_fixed :
    (ruleList Wasm10.envOriginal).all (keepsExcept Wasm10.envFixed keysWasm10Fixed) = true :=
  all_of_all_drop_zero <| all_drop_of_chunk check_wasm10Fixed_0 <|
    all_drop_of_chunk check_wasm10Fixed_33 <| all_drop_of_chunk check_wasm10Fixed_66 <|
    all_drop_of_chunk check_wasm10Fixed_99 <| all_drop_of_length_le ruleList_wasm10_length.le

/-- **The one rule the wasm-1.0 errata drop**: the dropped set is a single rule, of
`Module_ok`. -/
theorem dropped_wasm10_fixed_singleton :
    ∃ φ, dropped Wasm10.envOriginal Wasm10.envFixed = {φ} ∧ φ.key = ("Module_ok", "") :=
  dropped_eq_singleton all_wasm10_fixed droppedKeys_wasm10_fixed

theorem retained_wasm10_fixed : retainedCount Wasm10.envOriginal Wasm10.envFixed = 131 := by
  rw [retainedCount_eq_of_all all_wasm10_fixed, keptCount_eq, droppedKeys_wasm10_fixed,
    ruleList_wasm10_length]
  rfl

/-! ## meta-IL original → fixed -/

theorem all_metaIL :
    (ruleList Meta.envO).all (keepsExcept Meta.envF keysMetaFixed) = true :=
  all_of_all_drop_zero <| all_drop_of_chunk check_metaIL_0 <| all_drop_of_chunk check_metaIL_117 <|
    all_drop_of_length_le ruleList_metaIL_length.le

/-- **The rules erratum M1 drops**: exactly the four `Step_exp` rules of `keysMetaFixed`. -/
theorem dropped_metaIL :
    dropped Meta.envO Meta.envF = {φ | φ ∈ theoryOf Meta.envO ∧ φ.key ∈ keysMetaFixed} :=
  dropped_eq_of_all all_metaIL

theorem retained_metaIL : retainedCount Meta.envO Meta.envF = 229 := by
  rw [retainedCount_eq_of_all all_metaIL, keptCount_eq, droppedKeys_metaIL,
    ruleList_metaIL_length]
  rfl

/-! ## wasm-1.0 pinned → main -/

theorem all_wasm10_main :
    (ruleList Wasm10.envOriginal).all
      (keepsExcept Versions.Main.Wasm10.env keysWasm10Main) = true :=
  all_of_all_drop_zero <| all_drop_of_chunk check_main10_0 <| all_drop_of_chunk check_main10_33 <|
    all_drop_of_chunk check_main10_66 <| all_drop_of_chunk check_main10_99 <|
    all_drop_of_length_le ruleList_wasm10_length.le

/-- **wasm-1.0 pinned → main drops** the rules of `Module_ok` and `Export_ok`. -/
theorem dropped_wasm10_main :
    dropped Wasm10.envOriginal Versions.Main.Wasm10.env =
      {φ | φ ∈ theoryOf Wasm10.envOriginal ∧ φ.key ∈ keysWasm10Main} :=
  dropped_eq_of_all all_wasm10_main

/-! ## wasm-2.0 pinned → main -/

theorem all_wasm20_main :
    (ruleList Wasm20.envOriginal).all
      (keepsExcept Versions.Main.Wasm20.env keysWasm20Main) = true :=
  all_of_all_drop_zero <| all_drop_of_chunk check_main20_0 <| all_drop_of_chunk check_main20_32 <|
    all_drop_of_chunk check_main20_64 <| all_drop_of_chunk check_main20_96 <|
    all_drop_of_chunk check_main20_128 <| all_drop_of_chunk check_main20_160 <|
    all_drop_of_chunk check_main20_192 <| all_drop_of_chunk check_main20_224 <|
    all_drop_of_length_le ruleList_wasm20_length.le

/-- **wasm-2.0 pinned → main drops** the rules of `Module_ok` and `Export_ok`. -/
theorem dropped_wasm20_main :
    dropped Wasm20.envOriginal Versions.Main.Wasm20.env =
      {φ | φ ∈ theoryOf Wasm20.envOriginal ∧ φ.key ∈ keysWasm20Main} :=
  dropped_eq_of_all all_wasm20_main

theorem retained_wasm20_main : retainedCount Wasm20.envOriginal Versions.Main.Wasm20.env = 257 := by
  rw [retainedCount_eq_of_all all_wasm20_main, keptCount_eq, droppedKeys_wasm20_main,
    ruleList_wasm20_length]
  rfl

/-! ## wasm-3.0 pinned → main -/

theorem all_wasm30_main :
    (ruleList Wasm30.envOriginal).all
      (keepsExcept Versions.Main.Wasm30.env keysWasm30Main) = true :=
  all_of_all_drop_zero <| all_drop_of_chunk check_main30_0 <| all_drop_of_chunk check_main30_20 <|
    all_drop_of_chunk check_main30_40 <| all_drop_of_chunk check_main30_60 <|
    all_drop_of_chunk check_main30_80 <| all_drop_of_chunk check_main30_100 <|
    all_drop_of_chunk check_main30_120 <| all_drop_of_chunk check_main30_140 <|
    all_drop_of_chunk check_main30_160 <| all_drop_of_chunk check_main30_180 <|
    all_drop_of_chunk check_main30_200 <| all_drop_of_chunk check_main30_220 <|
    all_drop_of_chunk check_main30_240 <| all_drop_of_chunk check_main30_260 <|
    all_drop_of_chunk check_main30_280 <| all_drop_of_chunk check_main30_300 <|
    all_drop_of_chunk check_main30_320 <| all_drop_of_chunk check_main30_340 <|
    all_drop_of_chunk check_main30_360 <| all_drop_of_chunk check_main30_380 <|
    all_drop_of_chunk check_main30_400 <| all_drop_of_chunk check_main30_420 <|
    all_drop_of_chunk check_main30_440 <| all_drop_of_chunk check_main30_460 <|
    all_drop_of_chunk check_main30_480 <| all_drop_of_chunk check_main30_500 <|
    all_drop_of_chunk check_main30_520 <| all_drop_of_chunk check_main30_540 <|
    all_drop_of_length_le ruleList_wasm30_length.le

/-- **wasm-3.0 pinned → main drops** exactly the 23 rules of `keysWasm30Main`. -/
theorem dropped_wasm30_main :
    dropped Wasm30.envOriginal Versions.Main.Wasm30.env =
      {φ | φ ∈ theoryOf Wasm30.envOriginal ∧ φ.key ∈ keysWasm30Main} :=
  dropped_eq_of_all all_wasm30_main

theorem retained_wasm30_main : retainedCount Wasm30.envOriginal Versions.Main.Wasm30.env = 543 := by
  rw [retainedCount_eq_of_all all_wasm30_main, keptCount_eq, droppedKeys_wasm30_main,
    ruleList_wasm30_length]
  rfl

end Silmaril.Wasm.SpecTec.Institution.Versions
