"""Count import kinds in module headers under the given roots."""

import json
import re
import sys
from pathlib import Path

IMP = re.compile(r"^(public\s+)?(meta\s+)?import\s+(all\s+)?\S+")


def main() -> None:
    counts = {"public": 0, "private": 0, "files": 0}
    for root in sys.argv[1:]:
        p = Path(root)
        for f in [p] if p.is_file() else p.rglob("*.lean"):
            counts["files"] += 1
            for line in f.read_text(errors="replace").splitlines():
                m = IMP.match(line.split("--")[0].strip())
                if m:
                    counts["public" if m.group(1) else "private"] += 1
    print(json.dumps(counts))


if __name__ == "__main__":
    main()
