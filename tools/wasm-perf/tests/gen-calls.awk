# Print the WAT of a core module of NFUN functions, each a chain of NCALLS calls to
# pseudo-random functions of the module (a linear congruential generator on small numbers,
# exact in every awk, so the output is fixed): the shape of compiled programs with many
# functions and calls, where a validator that looks functions up in a list is quadratic.
# Called by bench.sh.
#   awk -v nfun=N -v ncalls=K -f gen-calls.awk
BEGIN {
  seed = 12345
  print "(module"
  for (f = 0; f < nfun; f++) {
    printf "  (func $f%d (param i32) (result i32)", f
    for (c = 0; c < ncalls; c++) {
      seed = (seed * 75 + 74) % 65537
      printf " local.get 0 call $f%d drop", seed % nfun
    }
    print " local.get 0)"
  }
  print ")"
}
