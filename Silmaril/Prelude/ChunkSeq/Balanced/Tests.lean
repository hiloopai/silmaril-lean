module

import Silmaril.Prelude.ChunkSeq.Balanced.Thms

namespace Silmaril.ChunkSeq.Balanced.Tests

def left : Seq .left Nat := Seq.ofList .left [0, 1, 2, 3, 4, 5, 6]
def right : Seq .right Nat := Seq.ofList .right [0, 1, 2, 3, 4, 5, 6]

example : left.val.size = 7 := by decide +kernel
example : (left.insert 7).get? 7 = some 7 := by decide +kernel
example : (left.insert 7).get? 0 = some 0 := by decide +kernel
example : (right.insert 9).get? 0 = some 9 := by decide +kernel
example : (right.insert 9).get? 7 = some 6 := by decide +kernel
example : (right.insert 9).get? 8 = none := by decide +kernel

def leftChunks : Chunked .left 2 Nat := Chunked.ofList .left 2 [0, 1, 2, 3, 4, 5, 6, 7]
def rightChunks : Chunked .right 2 Nat := Chunked.ofList .right 2 [0, 1, 2, 3, 4, 5, 6, 7]

example : leftChunks.val.tail = #[6, 7] := by decide +kernel
example : rightChunks.val.tail = #[1, 0] := by decide +kernel
example : (leftChunks.insert 8).val.tail.isEmpty = true := by decide +kernel
example : (leftChunks.insert 8).get? 5 = some 5 := by decide +kernel
example : (leftChunks.insert 8).get? 9 = none := by decide +kernel
example : (rightChunks.insert 9).get? 0 = some 9 := by decide +kernel
example : (rightChunks.insert 9).get? 1 = some 0 := by decide +kernel
example : (rightChunks.insert 9).get? 8 = some 7 := by decide +kernel
example : (rightChunks.insert 9).size = 9 := by decide +kernel

example : (Chunked.ofList .left 0 [1, 2, 3]).get? 1 = some 2 := by decide +kernel
example : (Chunked.ofList .right 0 ([] : List Nat)).get? 0 = none := by decide +kernel

end Silmaril.ChunkSeq.Balanced.Tests
