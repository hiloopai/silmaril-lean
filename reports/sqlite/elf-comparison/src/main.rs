mod analysis;
mod compare;
mod dwarf;
mod elf;

use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::error::Error;
use std::path::Path;
use std::{fmt::Write, fs};

type Result<T> = std::result::Result<T, Box<dyn Error>>;

const BUILDS: [&str; 8] = [
    "gcc-O0", "gcc-O1", "gcc-O2", "gcc-O3", "clang-O0", "clang-O1", "clang-O2", "clang-O3",
];

fn hex(bytes: &[u8]) -> String {
    let mut text = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(text, "{byte:02x}").expect("writing into String cannot fail");
    }
    text
}

fn hex_hash(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

#[derive(Serialize)]
struct Measurements<'a> {
    schema_version: u32,
    builds: BTreeMap<&'a str, compare::Summary<'a>>,
    comparisons: Vec<compare::Comparison<'a>>,
}

fn read_build<'a>(work: &Path, id: &'a str) -> Result<compare::Build<'a>> {
    let unstripped = fs::read(work.join(id).join("libsqlite3.so"))?;
    let stripped = fs::read(work.join(id).join("stripped.so"))?;
    let relocations = fs::read(work.join(id).join("relocs.so"))?;
    let full = elf::load(&unstripped)?;
    let relocs = elf::load(&relocations)?;
    let stripped = elf::load(&stripped)?;
    let pair =
        elf::stripped_pair(&full, &stripped, &relocs).map_err(|e| format!("strip check: {e}"))?;
    let inline = dwarf::inline_hints(&full).map_err(|e| format!("DWARF: {e}"))?;
    Ok(compare::Build::new(
        id,
        elf::Image::new(&relocs).map_err(|e| format!("ELF inventory: {e}"))?,
        inline,
        pair,
    ))
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args_os().collect();
    let [_, work] = args.as_slice() else {
        return Err("usage: sqlite-elf-comparison WORK".into());
    };
    let work = Path::new(work);
    let mut builds = Vec::new();
    for id in BUILDS {
        let build = read_build(work, id).map_err(|error| format!("{id}: {error}"))?;
        builds.push(build);
    }
    let comparisons = builds
        .iter()
        .enumerate()
        .flat_map(|(i, a)| builds[i + 1..].iter().map(move |b| compare::compare(a, b)))
        .collect();
    let measurements = Measurements {
        schema_version: 1,
        builds: builds.iter().map(|b| (b.id, b.summary())).collect(),
        comparisons,
    };
    serde_json::to_writer_pretty(std::io::stdout().lock(), &measurements)?;
    println!();
    Ok(())
}
