use crate::{hex, hex_hash, Result};
use iced_x86::{Decoder, DecoderOptions, FlowControl};
use object::read::elf::Sym;
use object::{
    elf, Architecture, BinaryFormat, Object, ObjectKind, ObjectSection, ObjectSegment,
    ObjectSymbol, RelocationFlags, RelocationTarget, SectionFlags, SegmentFlags, SymbolFlags,
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

pub type Elf<'a> = object::File<'a>;

#[derive(Clone, Default, Serialize)]
pub struct Inventory {
    pub defined_function_records: usize,
    pub zero_size_records: usize,
    pub unusable_records: usize,
    pub overlapping_spans: usize,
    pub usable_spans: usize,
    pub alias_spans: usize,
    pub clone_spans: usize,
    pub split_or_outline_spans: usize,
}

pub struct Span<'a> {
    pub address: u64,
    pub bytes: &'a [u8],
    pub names: BTreeSet<String>,
}

impl Span<'_> {
    pub fn end(&self) -> u64 {
        self.address + self.bytes.len() as u64
    }
}

pub fn clone_base(name: &str) -> Option<&str> {
    [".isra.", ".constprop.", ".part.", ".cold", ".llvm."]
        .iter()
        .filter_map(|pattern| name.split_once(pattern).map(|(base, _)| base))
        .min_by_key(|base| base.len())
}

pub fn outline_name(name: &str) -> bool {
    name.starts_with("OUTLINED_FUNCTION_") || name.contains(".cold") || name.contains(".part.")
}

fn symbol_type<'a>(symbol: &impl ObjectSymbol<'a>) -> u8 {
    match symbol.flags() {
        SymbolFlags::Elf { st_info, .. } => st_info & 0xf,
        _ => unreachable!("validated ELF"),
    }
}

fn executable<'a>(section: &impl ObjectSection<'a>) -> bool {
    matches!(section.flags(), SectionFlags::Elf { sh_flags } if sh_flags & (elf::SHF_EXECINSTR as u64) != 0)
}

pub fn load(bytes: &[u8]) -> Result<Elf<'_>> {
    let file = object::File::parse(bytes)?;
    if file.format() != BinaryFormat::Elf
        || file.architecture() != Architecture::X86_64
        || file.kind() != ObjectKind::Dynamic
        || !file.is_little_endian()
        || !file.is_64()
    {
        return Err("expected x86-64 little-endian ELF64 shared object".into());
    }
    Ok(file)
}

fn spans<'a>(file: &Elf<'a>) -> Result<(Inventory, Vec<Span<'a>>)> {
    let mut inv = Inventory::default();
    let mut ranges = BTreeMap::<_, Span<'_>>::new();
    for sym in file.symbols() {
        if symbol_type(&sym) != elf::STT_FUNC || sym.is_undefined() {
            continue;
        }
        inv.defined_function_records += 1;
        if sym.size() == 0 {
            inv.zero_size_records += 1;
            continue;
        }
        let extent = sym
            .section_index()
            .and_then(|index| file.section_by_index(index).ok())
            .filter(executable)
            .and_then(|section| section.data_range(sym.address(), sym.size()).ok().flatten());
        let (Ok(name), Some(bytes)) = (sym.name(), extent) else {
            inv.unusable_records += 1;
            continue;
        };
        if name.is_empty() {
            inv.unusable_records += 1;
            continue;
        }
        ranges
            .entry((sym.address(), sym.size()))
            .or_insert_with(|| Span {
                address: sym.address(),
                bytes,
                names: BTreeSet::new(),
            })
            .names
            .insert(name.into());
    }
    if inv.defined_function_records == 0 {
        return Err("missing defined STT_FUNC records in .symtab".into());
    }
    let ranges: Vec<_> = ranges.into_values().collect();
    let mut prior_end = 0;
    let mut usable = Vec::new();
    for (index, span) in ranges.iter().enumerate() {
        let overlaps_left = prior_end > span.address;
        prior_end = prior_end.max(span.end());
        let overlaps_right = ranges
            .get(index + 1)
            .is_some_and(|next| next.address < span.end());
        if overlaps_left || overlaps_right {
            inv.overlapping_spans += 1;
            continue;
        }
        inv.usable_spans += 1;
        inv.alias_spans += usize::from(span.names.len() > 1);
        inv.clone_spans += usize::from(span.names.iter().any(|name| clone_base(name).is_some()));
        inv.split_or_outline_spans += usize::from(span.names.iter().any(|name| outline_name(name)));
        usable.push(Span {
            address: span.address,
            bytes: span.bytes,
            names: span.names.clone(),
        });
    }
    Ok((inv, usable))
}

// Names of PLT and GOT references are dynamic symbol names, with version names
// supplied by the ELF version tables. Use numeric versions only to index those tables.
pub fn dynamic_name(file: &Elf<'_>, index: object::SymbolIndex) -> Result<String> {
    if let object::File::Elf64(elf_file) = file {
        let symbols = elf_file.elf_dynamic_symbol_table();
        let sym = symbols.symbol(index)?;
        let name = sym.name(elf_file.endian(), symbols.strings())?;
        let name = std::str::from_utf8(name)?;
        if let Some(versions) = elf_file
            .elf_section_table()
            .versions(elf_file.endian(), elf_file.data())?
        {
            let version = versions.version_index(elf_file.endian(), index);
            if let Some(version) = versions.version(version)? {
                return Ok(format!("{name}@{}", std::str::from_utf8(version.name())?));
            }
        }
        return Ok(name.into());
    }
    Err("expected ELF64".into())
}

pub struct Reloc {
    pub kind: u32,
}

pub struct Image<'a> {
    pub inventory: Inventory,
    pub spans: Vec<Span<'a>>,
    pub exports: BTreeSet<String>,
    pub functions: BTreeMap<u64, String>,
    pub plt: BTreeMap<u64, String>,
    pub got: BTreeMap<u64, String>,
    pub objects: BTreeMap<u64, (u64, String)>,
    pub read_only: Vec<(u64, &'a [u8])>,
    pub relocations: BTreeMap<u64, Vec<Reloc>>,
}

impl<'a> Image<'a> {
    pub fn new(file: &Elf<'a>) -> Result<Self> {
        let (inventory, spans) = spans(file)?;
        let mut name_counts = BTreeMap::new();
        for span in &spans {
            for name in &span.names {
                *name_counts.entry(name.as_str()).or_insert(0) += 1;
            }
        }
        let functions = spans
            .iter()
            .filter_map(|span| {
                let unique: Vec<_> = span
                    .names
                    .iter()
                    .filter(|name| name_counts[name.as_str()] == 1)
                    .map(String::as_str)
                    .collect();
                (!unique.is_empty())
                    .then(|| (span.address, format!("function:{}", unique.join("|"))))
            })
            .collect();
        let exports = exports(file)?;
        let mut got = BTreeMap::new();
        for (address, reloc) in file.dynamic_relocations().into_iter().flatten() {
            if matches!(
                reloc.flags(),
                RelocationFlags::Elf {
                    r_type: elf::R_X86_64_JUMP_SLOT | elf::R_X86_64_GLOB_DAT
                }
            ) {
                if let RelocationTarget::Symbol(index) = reloc.target() {
                    got.insert(address, dynamic_name(file, index)?);
                }
            }
        }

        let mut plt = BTreeMap::new();
        let mut read_only = Vec::new();
        let mut relocations = BTreeMap::<_, Vec<_>>::new();
        for section in file.sections() {
            let name = section.name()?;
            if matches!(name, ".plt" | ".plt.got" | ".plt.sec") {
                // A plain stub begins with a RIP-relative jump through a GOT slot.
                // An IBT stub can begin with endbr64 immediately before the jump.
                let bytes = section.data()?;
                let decoder = Decoder::with_ip(64, bytes, section.address(), DecoderOptions::NONE);
                let mut endbr = None;
                for instr in decoder {
                    if instr.flow_control() == FlowControl::IndirectBranch
                        && instr.is_ip_rel_memory_operand()
                    {
                        if let Some(name) = got.get(&instr.ip_rel_memory_address()) {
                            let start = endbr
                                .filter(|(_, end)| *end == instr.ip())
                                .map_or(instr.ip(), |(start, _)| start);
                            plt.insert(start, format!("plt:{name}"));
                        }
                    }
                    endbr = (instr.mnemonic() == iced_x86::Mnemonic::Endbr64)
                        .then(|| (instr.ip(), instr.next_ip()));
                }
            }
            if name == ".rodata" {
                read_only.push((section.address(), section.data()?));
            }
            if executable(&section) {
                for (address, relocation) in section.relocations() {
                    // object exposes raw r_offset values. In ET_DYN these are VAs.
                    if !(section.address()..section.address() + section.size()).contains(&address) {
                        return Err(format!("relocation at {address:#x} outside {name}").into());
                    }
                    let RelocationFlags::Elf { r_type } = relocation.flags() else {
                        return Err("expected ELF relocation".into());
                    };
                    relocations
                        .entry(address)
                        .or_default()
                        .push(Reloc { kind: r_type });
                }
            }
        }
        if relocations.is_empty() {
            return Err("missing retained executable-section relocations (--emit-relocs)".into());
        }

        // Only uniquely named, nonoverlapping STT_OBJECT ranges can label a reference.
        let mut data = Vec::new();
        let mut counts = BTreeMap::new();
        for sym in file.symbols() {
            if symbol_type(&sym) == elf::STT_OBJECT && !sym.is_undefined() && sym.size() > 0 {
                let name = sym.name()?;
                if !name.is_empty() && !name.starts_with('.') {
                    *counts.entry(name).or_insert(0) += 1;
                    data.push((sym.address(), sym.address() + sym.size(), name));
                }
            }
        }
        data.sort_unstable();
        let mut previous_end = 0;
        let mut objects = BTreeMap::new();
        for (i, &(start, end, name)) in data.iter().enumerate() {
            if counts[name] == 1
                && start >= previous_end
                && data.get(i + 1).is_none_or(|row| row.0 >= end)
            {
                objects.insert(start, (end, name.into()));
            }
            previous_end = previous_end.max(end);
        }
        Ok(Self {
            inventory,
            spans,
            exports,
            functions,
            plt,
            got,
            objects,
            read_only,
            relocations,
        })
    }

    pub fn named_code(&self, address: u64) -> Option<&str> {
        self.plt
            .get(&address)
            .or_else(|| self.functions.get(&address))
            .map(String::as_str)
    }

    pub fn named_data(&self, address: u64) -> Option<String> {
        if let Some(name) = self.got.get(&address) {
            return Some(format!("got:{name}"));
        }
        let (&start, (end, name)) = self.objects.range(..=address).next_back()?;
        (address < *end).then(|| format!("object:{name}+{}", address - start))
    }

    pub fn table_entry(&self, address: u64) -> Option<i32> {
        for &(base, bytes) in &self.read_only {
            if let Some(offset) = address.checked_sub(base) {
                if let Some(field) = bytes.get(offset as usize..offset as usize + 4) {
                    return Some(i32::from_le_bytes(field.try_into().ok()?));
                }
            }
        }
        None
    }
}

fn exports(file: &Elf<'_>) -> Result<BTreeSet<String>> {
    file.dynamic_symbols()
        .filter(|sym| symbol_type(sym) == elf::STT_FUNC && !sym.is_undefined() && sym.is_global())
        .map(|sym| Ok(sym.name()?.to_owned()))
        .collect()
}

#[derive(Serialize)]
pub struct Pair {
    pub build_id: String,
    pub relocation_link_build_id: String,
    pub executable_segments: Vec<Segment>,
    pub dynamic_symbol_records: usize,
    pub stripped_static_symbol_records: usize,
    pub stripped_debug_info: bool,
}

#[derive(PartialEq, Serialize)]
pub struct Segment {
    address: u64,
    file_size_bytes: usize,
    memory_size_bytes: u64,
    sha256: String,
}

fn executable_segments(file: &Elf<'_>) -> Result<Vec<Segment>> {
    file.segments()
        .filter(
            |seg| matches!(seg.flags(), SegmentFlags::Elf { p_flags } if p_flags & elf::PF_X != 0),
        )
        .map(|seg| {
            let data = seg.data()?;
            Ok(Segment {
                address: seg.address(),
                file_size_bytes: data.len(),
                memory_size_bytes: seg.size(),
                sha256: hex_hash(data),
            })
        })
        .collect()
}

fn dyn_symbols(file: &Elf<'_>) -> Result<Vec<impl PartialEq + std::fmt::Debug>> {
    file.dynamic_symbols()
        .map(|sym| {
            let section = sym
                .section_index()
                .map(|i| {
                    file.section_by_index(i).map_err(|e| {
                        format!("dynamic symbol {}: {i:?}: {e}", sym.name().unwrap_or("?"))
                    })
                })
                .transpose()?;
            Ok((
                sym.name()?.to_owned(),
                sym.address(),
                sym.size(),
                sym.flags(),
                sym.is_undefined(),
                section.map(|s| s.name().map(str::to_owned)).transpose()?,
            ))
        })
        .collect()
}

fn dynamic_sections_match(a: &Elf<'_>, b: &Elf<'_>) -> Result<()> {
    if dyn_symbols(a)? != dyn_symbols(b)? {
        return Err("different dynamic symbol records".into());
    }
    for name in [
        ".dynamic",
        ".dynstr",
        ".gnu.hash",
        ".gnu.version",
        ".gnu.version_r",
        ".gnu.version_d",
        ".rela.dyn",
        ".rela.plt",
    ] {
        let left = a.section_by_name(name).map(|s| s.data()).transpose()?;
        let right = b.section_by_name(name).map(|s| s.data()).transpose()?;
        if left != right {
            return Err(format!("link variants differ in {name}").into());
        }
    }
    Ok(())
}

pub fn stripped_pair(full: &Elf<'_>, stripped: &Elf<'_>, relocs: &Elf<'_>) -> Result<Pair> {
    let build_id = full.build_id()?.ok_or("no build ID")?;
    let relocation_link_build_id = relocs
        .build_id()?
        .ok_or("relocation link has no build ID")?;
    let executable_segments = executable_segments(full)?;
    let stripped_static_symbol_records = stripped.symbols().count();
    let stripped_debug_info = stripped.has_debug_symbols();
    if Some(build_id) != stripped.build_id()?
        || executable_segments.is_empty()
        || executable_segments != self::executable_segments(stripped)?
        || executable_segments != self::executable_segments(relocs)?
        || stripped_static_symbol_records != 0
        || stripped_debug_info
    {
        return Err("link variants differ in executable segments, the strip pair has distinct build IDs, or strip retains symbols/debug info".into());
    }
    dynamic_sections_match(full, stripped)?;
    dynamic_sections_match(full, relocs)?;
    let (_, full_spans) = spans(full)?;
    let (_, reloc_spans) = spans(relocs)?;
    if full_spans
        .iter()
        .map(|s| (s.address, s.bytes, &s.names))
        .ne(reloc_spans.iter().map(|s| (s.address, s.bytes, &s.names)))
    {
        return Err(
            "relocation link differs from ordinary link in usable .symtab function spans".into(),
        );
    }
    Ok(Pair {
        build_id: hex(build_id),
        relocation_link_build_id: hex(relocation_link_build_id),
        executable_segments,
        dynamic_symbol_records: full.dynamic_symbols().count(),
        stripped_static_symbol_records,
        stripped_debug_info,
    })
}
