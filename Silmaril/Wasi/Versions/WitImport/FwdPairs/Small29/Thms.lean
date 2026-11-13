module

public import Silmaril.Wasi.Versions.WitImport.Fwd.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables29.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables29.Defs

@[expose] public section

/-!
# Forwarding pairs, computed once: cli, clocks, rand (0.2.9)

Each `fwdPairs P Q` of `Silmaril.Wasi.Versions.WitImport.Fwd.Thms` is stated here as a literal
list, checked by the kernel (`decide +kernel`), and `FwdOk` is checked on that literal. The
pairs are split over several modules so each stays under the module time budget; `Fwd.Thms`
assembles `fwdOk_all` and the name lists from these equations by rewriting. The literals were
printed by evaluating `fwdPairs` (not trusted: the kernel checks each equation).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- Forwarding pairs, 0.3.2 `rand` over 0.2.9. -/
theorem fwdPairs_rand3_29 : fwdPairs rand29P rand3P =
    [(⟨"wasi:random/insecure@0.3.2", "get-insecure-random-bytes"⟩,
       ⟨"wasi:random/insecure", "get-insecure-random-bytes"⟩),
      (⟨"wasi:random/insecure@0.3.2", "get-insecure-random-u64"⟩,
       ⟨"wasi:random/insecure", "get-insecure-random-u64"⟩),
      (⟨"wasi:random/random@0.3.2", "get-random-bytes"⟩,
       ⟨"wasi:random/random", "get-random-bytes"⟩),
      (⟨"wasi:random/random@0.3.2", "get-random-u64"⟩,
       ⟨"wasi:random/random", "get-random-u64"⟩)] := by
  decide +kernel

/-- The pairs of 0.3.2 `rand` over 0.2.9 are forwardable. -/
theorem fwdOk_rand3_29 : FwdOk rand29P rand3P (fwdPairs rand29P rand3P) = true := by
  rw [fwdPairs_rand3_29]
  decide +kernel

/-- Forwarding pairs, 0.2.9 `rand` over 0.3.2. -/
theorem fwdPairs_rand29 : fwdPairs rand3P rand29P =
    [(⟨"wasi:random/insecure", "get-insecure-random-bytes"⟩,
       ⟨"wasi:random/insecure@0.3.2", "get-insecure-random-bytes"⟩),
      (⟨"wasi:random/insecure", "get-insecure-random-u64"⟩,
       ⟨"wasi:random/insecure@0.3.2", "get-insecure-random-u64"⟩),
      (⟨"wasi:random/random", "get-random-bytes"⟩,
       ⟨"wasi:random/random@0.3.2", "get-random-bytes"⟩),
      (⟨"wasi:random/random", "get-random-u64"⟩,
       ⟨"wasi:random/random@0.3.2", "get-random-u64"⟩)] := by
  decide +kernel

/-- The pairs of 0.2.9 `rand` over 0.3.2 are forwardable. -/
theorem fwdOk_rand29 : FwdOk rand3P rand29P (fwdPairs rand3P rand29P) = true := by
  rw [fwdPairs_rand29]
  decide +kernel

/-- Forwarding pairs, 0.3.2 `clocks` over 0.2.9. -/
theorem fwdPairs_clocks3_29 : fwdPairs clocks29P clocks3P =
    [] := by
  decide +kernel

/-- The pairs of 0.3.2 `clocks` over 0.2.9 are forwardable. -/
theorem fwdOk_clocks3_29 : FwdOk clocks29P clocks3P (fwdPairs clocks29P clocks3P) = true := by
  rw [fwdPairs_clocks3_29]
  decide +kernel

/-- Forwarding pairs, 0.2.9 `clocks` over 0.3.2. -/
theorem fwdPairs_clocks29 : fwdPairs clocks3P clocks29P =
    [] := by
  decide +kernel

/-- The pairs of 0.2.9 `clocks` over 0.3.2 are forwardable. -/
theorem fwdOk_clocks29 : FwdOk clocks3P clocks29P (fwdPairs clocks3P clocks29P) = true := by
  rw [fwdPairs_clocks29]
  decide +kernel

/-- Forwarding pairs, 0.3.2 `cli` over 0.2.9. -/
theorem fwdPairs_cli3_29 : fwdPairs cli29P cli3P =
    [(⟨"wasi:cli/environment@0.3.2", "get-environment"⟩,
       ⟨"wasi:cli/environment", "get-environment"⟩),
      (⟨"wasi:cli/environment@0.3.2", "get-arguments"⟩,
       ⟨"wasi:cli/environment", "get-arguments"⟩),
      (⟨"wasi:cli/exit@0.3.2", "exit"⟩,
       ⟨"wasi:cli/exit", "exit"⟩),
      (⟨"wasi:cli/terminal-stdin@0.3.2", "get-terminal-stdin"⟩,
       ⟨"wasi:cli/terminal-stdin", "get-terminal-stdin"⟩),
      (⟨"wasi:cli/terminal-stdout@0.3.2", "get-terminal-stdout"⟩,
       ⟨"wasi:cli/terminal-stdout", "get-terminal-stdout"⟩),
      (⟨"wasi:cli/terminal-stderr@0.3.2", "get-terminal-stderr"⟩,
       ⟨"wasi:cli/terminal-stderr", "get-terminal-stderr"⟩)] := by
  decide +kernel

/-- The pairs of 0.3.2 `cli` over 0.2.9 are forwardable. -/
theorem fwdOk_cli3_29 : FwdOk cli29P cli3P (fwdPairs cli29P cli3P) = true := by
  rw [fwdPairs_cli3_29]
  decide +kernel

/-- Forwarding pairs, 0.2.9 `cli` over 0.3.2. -/
theorem fwdPairs_cli29 : fwdPairs cli3P cli29P =
    [(⟨"wasi:cli/environment", "get-environment"⟩,
       ⟨"wasi:cli/environment@0.3.2", "get-environment"⟩),
      (⟨"wasi:cli/environment", "get-arguments"⟩,
       ⟨"wasi:cli/environment@0.3.2", "get-arguments"⟩),
      (⟨"wasi:cli/exit", "exit"⟩,
       ⟨"wasi:cli/exit@0.3.2", "exit"⟩),
      (⟨"wasi:cli/terminal-stdin", "get-terminal-stdin"⟩,
       ⟨"wasi:cli/terminal-stdin@0.3.2", "get-terminal-stdin"⟩),
      (⟨"wasi:cli/terminal-stdout", "get-terminal-stdout"⟩,
       ⟨"wasi:cli/terminal-stdout@0.3.2", "get-terminal-stdout"⟩),
      (⟨"wasi:cli/terminal-stderr", "get-terminal-stderr"⟩,
       ⟨"wasi:cli/terminal-stderr@0.3.2", "get-terminal-stderr"⟩)] := by
  decide +kernel

/-- The pairs of 0.2.9 `cli` over 0.3.2 are forwardable. -/
theorem fwdOk_cli29 : FwdOk cli3P cli29P (fwdPairs cli3P cli29P) = true := by
  rw [fwdPairs_cli29]
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
