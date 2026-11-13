#!/usr/bin/env bash
# Write the benchmark file for N bytes to stdout.
N=$1; NATIVE=${2:-}
C=$((N / 2 + 1003))       # an unaligned cut for ropes
cat <<EOT
import Bench
open Silmaril Silmaril.KBytes
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
#data D $N 1
#data E $N 1
#dataOneLeaf W D
#reads D 100 1
#reads D 100 1 flat
#reads W 100 1
#reads D 1000 8
#reads D 100 4096
#krfl D E
#kcheck "beq D E (structural)" (KBytes.beq D E)
#kcheck "sameBytes 65536 D E" (KBytes.sameBytes 65536 D E)
#kcheck "sameBytes 4096 D E" (KBytes.sameBytes 4096 D E)
#kcheck "sameBytes 65536 rope D" (KBytes.sameBytes 65536 (D.slice 0 $C ++ D.slice $C ($N - $C)) D)
#kcheck "beq (canon 4096 rope) D" (KBytes.beq (KBytes.canon 4096 (D.slice 0 $C ++ D.slice $C ($N - $C))) D)
#kcheck "read whole value D = whole value E" (Nat.beq (D.read 0 $N) (E.read 0 $N))
#kcheck "zeros: read in one 16 MiB zero leaf" (Nat.beq ((KBytes.leaf 16777216 0).read 9999999 8) 0)
EOT
if [ -n "$NATIVE" ]; then cat <<EOT
#data DC $N 1 computable
#ncheck "sameBytes 65536 rope D" (KBytes.sameBytes 65536 (DC.slice 0 $C ++ DC.slice $C ($N - $C)) DC)
#ncheck "eqByteArray D D.toByteArray" (KBytes.eqByteArray DC DC.toByteArray)
EOT
fi
