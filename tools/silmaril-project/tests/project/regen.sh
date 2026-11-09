#!/usr/bin/env bash
# Regenerate the `sil project` goldens: `SIL_BLESS=1 cargo test --test project` rewrites each
# case's check.txt and project.sql from its hand-written dump.json. Review with `git diff`.
set -euo pipefail
cd "$(dirname "$0")/../.."
SIL_BLESS=1 cargo test --test project
