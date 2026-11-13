# Print the WAT of the core-module template FILE with filler functions inserted before its
# last line: NF_ functions, each a chain of `local.get 0 i32.const K i32.add` steps (about
# 6 bytes of code per step), STEPS steps per function. Called by corpus.sh.
#   awk -v nfun=N -v steps=S -v step='…' -f gen-filler.awk xf.wat.in
{ lines[NR] = $0 }
END {
  for (i = 1; i < NR; i++) { l = lines[i]; gsub(/@STEP@/, step, l); print l }
  last = lines[NR]
  sub(/\)$/, "", last)
  print last
  for (f = 0; f < nfun; f++) {
    printf "  (func $filler%d (param i32) (result i32)\n", f
    for (s = 0; s < steps; s++) printf "    local.get 0 i32.const %d i32.add local.set 0\n", (f * 7919 + s * 104729) % 1000000
    print "    local.get 0)"
  }
  print ")"
}
