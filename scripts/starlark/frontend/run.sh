#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."
script_dir="$PWD/scripts/starlark/frontend"
revision=4f4267fb140d1e8b91c9bce55cee2f809e8840dd
oracle=$(mktemp -d)
trap 'rm -rf "$oracle"' EXIT

lake build --wfail +Silmaril.Languages.Starlark.Frontend.Checks \
  +Silmaril.Languages.Starlark.Frontend.Module.Checks \
  +Silmaril.Languages.Starlark.Frontend.Module.Loader.Checks \
  +Silmaril.Languages.Starlark.Frontend.Module.Loader.KeywordOnlyChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.SpreadChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.ComputedCallChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.ReturnCallChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.AssignmentCallChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.CallStatementChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.LogicalCallChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.ConditionalCallChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.BranchCallChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.ListDisplayChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.TupleDisplayChecks
lake env lean -DautoImplicit=false -DwarningAsError=true --run "$script_dir/Fixtures.lean" \
  "$oracle/fixtures.json"

git -C "$oracle" init -q
git -C "$oracle" fetch -q --depth 1 https://github.com/google/starlark-go.git "$revision"
git -C "$oracle" checkout -q --detach "$revision"
cd "$oracle"
go run "$script_dir/check.go" "$script_dir/spreads.go" < fixtures.json
