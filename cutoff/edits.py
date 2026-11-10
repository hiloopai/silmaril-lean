"""Apply one named edit to the base module for the Lake cutoff experiment."""

import sys
from pathlib import Path

BASE = Path("Silmaril/X86/Machine.lean")

FETCH_PROOF_HEAD = (
    "        Insn.decode bytes = some (instr, length) := by\n"
    "  constructor\n"
    "  · intro h\n"
    "    unfold fetch at h\n"
)
FETCH_PROOF_TAIL = "    simp only [Memory.readWith_permitted fetched, ite_true]\n"
PRIVATE_PROOF = (
    "private theorem length_completion (w : List Byte) : 4 ≤ (completion w).length := by\n"
    "  unfold completion\n"
)
STATEMENT = (
    "    Memory.WritesOnly m.memory next.memory (m.core.read .rsp - 8#64).toNat 8 := by\n"
    "  unfold step at h\n"
)


def insert_before_constructor(lines: str) -> tuple[str, str]:
    return FETCH_PROOF_HEAD, FETCH_PROOF_HEAD.replace("  constructor\n", lines + "  constructor\n", 1)


EDITS: dict[str, tuple[str, str] | str] = {
    # Proof-only edits to the public theorem `fetch_eq_decoded_iff` (17 downstream files use it).
    "proof_skip": (FETCH_PROOF_HEAD, FETCH_PROOF_HEAD.replace("  constructor\n", "  constructor; skip\n", 1)),
    "proof_simp": (FETCH_PROOF_TAIL, "    simp [Memory.readWith_permitted fetched]\n"),
    "proof_have": insert_before_constructor("  have _h : (1 : Nat) + 1 = 2 := rfl\n  clear _h\n"),
    "proof_match": insert_before_constructor(
        "  have _h : ∀ n : Nat, n = n := fun n => match n with | 0 => rfl | _ + 1 => rfl\n  clear _h\n"
    ),
    "proof_kernel": insert_before_constructor("  have _h : (2 : Nat) ≤ 5 := by decide +kernel\n  clear _h\n"),
    # Controls.
    "comment_eof": "APPEND",
    "comment_top": ("namespace Silmaril.X86\n", "namespace Silmaril.X86\n-- cutoff test\n"),
    "private_proof": (PRIVATE_PROOF, PRIVATE_PROOF + "  have _h : (1 : Nat) + 1 = 2 := rfl\n  clear _h\n"),
    "statement": (
        STATEMENT,
        STATEMENT.replace(".toNat 8 := by\n", ".toNat 8 ∧ True := by\n  refine ⟨?_, trivial⟩\n", 1),
    ),
}


def main() -> None:
    name = sys.argv[1]
    text = BASE.read_text()
    edit = EDITS[name]
    if edit == "APPEND":
        new = text + "\n-- cutoff test\n"
    else:
        old, repl = edit
        if text.count(old) != 1:
            raise SystemExit(f"{name}: anchor found {text.count(old)} times")
        new = text.replace(old, repl, 1)
    BASE.write_text(new)


if __name__ == "__main__":
    main()
