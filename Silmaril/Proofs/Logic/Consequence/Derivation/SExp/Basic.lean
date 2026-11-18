module

public import Silmaril.Logic.Consequence.Derivation.SExp.Defs
public import Silmaril.Logic.Concrete.Codec.Thms
public import Silmaril.Logic.Concrete.SExp.Thms

/-!
# Proofs for the derivation S-expression formats: the readers invert the encoders
-/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Derivation.SExp

open Silmaril.Consequence Silmaril.Consequence.ProofSExp
open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Concrete (SExpCodec)
open Silmaril.Logic.Concrete.SExp (num num? num?_num)

universe u

variable {J : Type u} (cj : SExpCodec J)

mutual

theorem readTree_encode : ∀ t : ProofTree SE J, readTree cj (encodeTree cj t) = some t
  | .assume j => by simp [encodeTree, readTree, SExpCodec.decode_encode]
  | .infer r c ts => by
    simp [encodeTree, readTree, SExpCodec.decode_encode, readTrees_encode ts]

theorem readTrees_encode : ∀ ts : List (ProofTree SE J), readTrees cj (encodeTrees cj ts) = some ts
  | [] => by simp [encodeTrees, readTrees]
  | t :: ts => by simp [encodeTrees, readTrees, readTree_encode t, readTrees_encode ts]

end

theorem readNums_map : ∀ ixs : List ℕ, readNums (ixs.map num) = some ixs
  | [] => rfl
  | i :: ixs => by simp [readNums, num?_num, readNums_map ixs]

theorem readLine_encode (l : Line SE J) : readLine cj (encodeLine cj l) = some l := by
  cases l <;> simp [encodeLine, readLine, SExpCodec.decode_encode, readNums_map]

theorem readLineList_map : ∀ ls : List (Line SE J),
    readLineList cj (ls.map (encodeLine cj)) = some ls
  | [] => rfl
  | l :: ls => by simp [readLineList, readLine_encode, readLineList_map ls]

theorem readLines_encode (ls : List (Line SE J)) :
    readLines cj (encodeLines cj ls) = some ls := by
  simp [encodeLines, readLines, readLineList_map]

end Silmaril.Proofs.Logic.Consequence.Derivation.SExp
