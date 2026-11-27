"""Compare native IPC with checked, independently cut mixed Parquet chunks."""

import argparse
from hashlib import sha256
from importlib.metadata import version
import os
from pathlib import Path
from runpy import run_path
import subprocess

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PINS = {
    "int-first-late.arrows": "db955b187bc476f89de7e7e2437b00998314e5f15bbcc175c347476aa28573bf",
    "int-first-missing-eos.arrows": "b81c930893ea3e0ab17d7eb4109798d224fdcfcba6806bff615badaf9d6aef20",
    "byte-first-late.arrows": "43474b3f82887bc710780b19ebc812a846bffd914d2ce63ce9884e5d160dac82",
    "byte-first-missing-eos.arrows": "416de1e3d96f9766e9a5a08eefc3e57c1360d6c4f6ee4bd5ce5110171f7c0ffc",
    "int-first.arrows": "42a7fa50ceaa9eb5e182e890526e692e9e0b593765ce1e8ed7a1310f55ee319d",
    "int-first-returned.arrows": "a7e62c738ff42381adb47cad66c8ceacbab42e65e7a97ed0a0f74f842de666fd",
    "int-first.parquet": "e10ab4c45c6b52fd92a081ade11b8ac57a92e75595dad1951031de8b658947ae",
    "int-first-schema-only.arrows": "4400e52954d8008f3247cb7951585031e3195b5dfd8f2450a2fd7514d45c404d",
    "int-first-schema-only-returned.arrows": "0ee19e6a081b5d12f3dc4f3d3870490970429474ad7cd8a15867712e32abee52",
    "int-first-schema-only.parquet": "cdabbe1e4059ca18470f3cb93fbdb2677e825487f8483959599fe66309f4f14f",
    "int-first-empty-batch.arrows": "b9ab5e12d2843af68ebad38c998c589d5b4aa0d39ce8fb9b426830e1dbee895f",
    "int-first-empty-batch-returned.arrows": "88e0ef09c9889b7fc3cc299e4ba54c1075352fe67e243ec544db38d124156a36",
    "int-first-empty-batch.parquet": "ac9ae510f6183e0a1ab6b55e75898ab571fa12dba6e8a7c76181edbf7f0c0b2a",
    "byte-first.arrows": "9f8231a22bd96776d039535bc88c893891187385b22431e451dbd6f11f3d1547",
    "byte-first-returned.arrows": "e892e61c23c412b7d4a23ba101366cc7c4d1a44d85999243ef7ed099d66fb1cf",
    "byte-first.parquet": "b998b61d5013aed6305e4073b879866a48a749566aa872b660ed344950cb7d56",
    "byte-first-schema-only.arrows": "d22f36303f59890a0dd6c9f9f0babec63ca5af901ca8a741bf9c7828f3c26ce1",
    "byte-first-schema-only-returned.arrows": "6a22847c0ae4c3b276211714a07432542e5883e178bad659cf06a1bb3b8dca6e",
    "byte-first-schema-only.parquet": "8a0761b8af71d280104c562f1602cd4d4d6d5376655a5c278792fbb0b1d55e75",
    "byte-first-empty-batch.arrows": "4792119299cf49b9a46b0825d1e748a9fe2d46c367f9529af98073c7661dfcba",
    "byte-first-empty-batch-returned.arrows": "069a1fd35e0a088d5b3e52b7581aa598f00a82f1be1990d946a4c850be645c0a",
    "byte-first-empty-batch.parquet": "8c7634231695195f845d1b8193b192f52af42a80207eda428394ceb26b89b2b7",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert version("thrift") == "0.25.0"
    stream = run_path(str(ROOT / "scripts/arrow-mixed-named-oracle/check.py"))["stream"]
    schema_only = run_path(str(ROOT / "scripts/arrow-mixed-parquet-schema-only-oracle/check.py"))
    messages = run_path(str(ROOT / "scripts/arrow-mixed-parquet-roundtrip-oracle/check.py"))["messages"]
    thrift = run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
    parquet = run_path(str(ROOT / "scripts/parquet-mixed-v1-writer-oracle/check.py"))
    reference = run_path(str(ROOT / "scripts/parquet-mixed-v1-multipage-oracle/check.py"))["GROUPS"]
    cases = []
    rejected = []
    for name, order, first_cuts in (
        ("int-first", (1, 6), [[2, 3], [1, 1, 3]]),
        ("byte-first", (6, 1), [[1, 4], [2, 1, 2]]),
    ):
        columns = [pa.field("count", pa.int32()), pa.field("opaque", pa.binary_view())]
        groups = reference
        cuts = [first_cuts, [[0], [0]], [[3], [1, 2]]]
        if order == (6, 1):
            columns = columns[::-1]
            groups = [group[::-1] for group in groups]
            cuts = [group[::-1] for group in cuts]
        schema = pa.schema(columns)
        wire = stream(schema, groups)
        (out / f"{name}.arrows").write_bytes(wire)
        for suffix, drop in (("late", 9), ("missing-eos", 8)):
            fixture = out / f"{name}-{suffix}.arrows"
            fixture.write_bytes(wire[:-drop])
            rejected.append(fixture)
        (out / f"{name}-schema-only.arrows").write_bytes(stream(schema, []))
        (out / f"{name}-empty-batch.arrows").write_bytes(stream(schema, [[[], []]]))
        cases.extend([
            (name, schema, order, [5, 0, 3], cuts),
            (name + "-schema-only", schema, order, [], []),
            (name + "-empty-batch", schema, order, [0], [[[0], [0]]]),
        ])

    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Convert.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    fixtures = rejected
    for name, schema, order, counts, cuts in cases:
        source = out / f"{name}.arrows"
        output = out / f"{name}-returned.arrows"
        file = out / f"{name}.parquet"
        groups = schema_only["check_ipc"](source, schema, counts, messages)
        assert schema_only["check_ipc"](output, schema, counts, messages) == groups
        fields = [(field.name, field.nullable) for field in schema]
        parquet["check_wire_groups"](thrift, file.read_bytes(), fields, groups, order, cuts)
        parquet["check_arrow_groups"](file.read_bytes(), fields, groups, order)
        fixtures.extend((source, output, file))
    assert {path.name for path in fixtures} == PINS.keys()
    for path in fixtures:
        digest = sha256(path.read_bytes()).hexdigest()
        print(f"{digest}  {path.name}")
        assert digest == PINS[path.name], f"{path.name}: fixture hash changed"
    print("PyArrow and Thrift checked every page, group, field order and IPC EOS in six native round trips.")


if __name__ == "__main__":
    main()
