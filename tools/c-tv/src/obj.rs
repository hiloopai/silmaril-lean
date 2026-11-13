//! The relocatable object a compiler wrote: its `.text`, symbols, relocations and DWARF.
//!
//! DWARF in an `ET_REL` file refers to other sections through relocations (`.rela.debug_*`).
//! Every debug section is copied and its `R_X86_64_32`/`R_X86_64_64` relocations are applied
//! (symbol value + addend; section symbols have value 0) before gimli reads it. Addresses in
//! the line table and the DIEs are then offsets in `.text` (the tool requires one code
//! section). Nothing read here is trusted: the Lean header ties the bytes to the file, and the
//! line table and frame slots only shape the goals (a wrong slot gives an unprovable goal).

use std::collections::HashMap;

use anyhow::{Context, Result, anyhow, bail};
use gimli::{EndianSlice, LittleEndian, RunTimeEndian};
use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget, SectionKind, SymbolKind};

/// A function symbol of `.text`.
#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    pub off: u64,
    pub size: u64,
}

/// One row of the line table (DWARF `.debug_line`), an address in `.text`.
#[derive(Clone, Debug)]
pub struct Row {
    pub addr: u64,
    pub line: u64,
    /// Column and `is_stmt`, kept for the report.
    #[allow(dead_code)]
    pub column: u64,
    #[allow(dead_code)]
    pub is_stmt: bool,
    pub end: bool,
}

/// Where DWARF says a variable lives.
#[derive(Clone, Debug, PartialEq)]
pub enum Location {
    /// `DW_OP_fbreg off` with the frame base `DW_OP_call_frame_cfa`.
    FrameSlot(i64),
    /// Anything else (a register, a location list, an expression the tool does not read).
    Other(String),
}

/// A parameter or local variable of a function (DWARF).
#[derive(Clone, Debug)]
pub struct Var {
    pub name: String,
    pub param: bool,
    #[allow(dead_code)]
    pub decl_line: u64,
    /// Byte size and signedness of the base type, when the type resolves to a base type.
    pub base: Option<(u64, bool)>,
    pub loc: Location,
    /// Declared in a nested lexical block.
    pub nested: bool,
}

/// The DWARF facts about one function.
#[derive(Clone, Debug, Default)]
pub struct FuncInfo {
    pub decl_line: u64,
    pub frame_base_cfa: bool,
    pub vars: Vec<Var>,
    pub return_base: Option<(u64, bool)>,
}

/// The facts the tool reads from the object.
pub struct ObjFile {
    pub text: Vec<u8>,
    #[allow(dead_code)]
    pub text_index: usize,
    pub funcs: Vec<Func>,
    /// Offsets in `.text` of relocations that patch code.
    pub text_relocs: Vec<u64>,
    pub rows: Vec<Row>,
    pub info: HashMap<String, FuncInfo>,
}

pub fn read(bytes: &[u8]) -> Result<ObjFile> {
    let file = object::File::parse(bytes).context("parse the object")?;
    if file.kind() != object::ObjectKind::Relocatable {
        bail!("not a relocatable object (ET_REL)");
    }
    let mut code_sections = file
        .sections()
        .filter(|s| s.kind() == SectionKind::Text && s.size() > 0);
    let text_sec = code_sections
        .next()
        .ok_or_else(|| anyhow!("no code section"))?;
    if let Some(other) = code_sections.next() {
        bail!(
            "more than one code section ({} and {}): compile without -ffunction-sections",
            text_sec.name().unwrap_or("?"),
            other.name().unwrap_or("?")
        );
    }
    if text_sec.name()? != ".text" {
        bail!("the code section is {}, not .text", text_sec.name()?);
    }
    let text = text_sec.data()?.to_vec();
    let text_index = text_sec.index().0;
    let mut funcs: Vec<Func> = file
        .symbols()
        .filter(|s| s.kind() == SymbolKind::Text && s.section_index() == Some(text_sec.index()))
        .filter(|s| s.size() > 0)
        .map(|s| {
            Ok(Func {
                name: s.name()?.to_string(),
                off: s.address(),
                size: s.size(),
            })
        })
        .collect::<Result<_>>()?;
    funcs.sort_by_key(|f| f.off);
    let text_relocs = text_sec.relocations().map(|(off, _)| off).collect();

    // Debug sections, relocated.
    let mut sections: HashMap<String, Vec<u8>> = HashMap::new();
    for sec in file.sections() {
        let name = sec.name()?.to_string();
        if !name.starts_with(".debug_") {
            continue;
        }
        let mut data = sec.uncompressed_data()?.into_owned();
        for (off, rel) in sec.relocations() {
            let value = match rel.target() {
                RelocationTarget::Symbol(i) => file.symbol_by_index(i)?.address() as i64,
                RelocationTarget::Section(_) => 0,
                _ => bail!("{name}: unsupported relocation target"),
            };
            let v = value.wrapping_add(rel.addend());
            let off = off as usize;
            match rel.size() {
                32 => data[off..off + 4].copy_from_slice(&(v as u32).to_le_bytes()),
                64 => data[off..off + 8].copy_from_slice(&(v as u64).to_le_bytes()),
                n => bail!("{name}: {n}-bit relocation at {off:#x}"),
            }
        }
        sections.insert(name, data);
    }
    let empty: Vec<u8> = Vec::new();
    let load = |id: gimli::SectionId| -> Result<EndianSlice<'_, RunTimeEndian>> {
        let data = sections.get(id.name()).unwrap_or(&empty);
        Ok(EndianSlice::new(data.as_slice(), RunTimeEndian::Little))
    };
    let dwarf = gimli::Dwarf::load(load)?;
    let mut rows = Vec::new();
    let mut info = HashMap::new();
    let mut units = dwarf.units();
    while let Some(header) = units.next()? {
        let unit = dwarf.unit(header)?;
        if let Some(program) = unit.line_program.clone() {
            let mut lr = program.rows();
            while let Some((_, row)) = lr.next_row()? {
                rows.push(Row {
                    addr: row.address(),
                    line: row.line().map(|l| l.get()).unwrap_or(0),
                    column: match row.column() {
                        gimli::ColumnType::LeftEdge => 0,
                        gimli::ColumnType::Column(c) => c.get(),
                    },
                    is_stmt: row.is_stmt(),
                    end: row.end_sequence(),
                });
            }
        }
        read_dies(&dwarf, &unit, &mut info)?;
    }
    let _ = LittleEndian;
    Ok(ObjFile {
        text,
        text_index,
        funcs,
        text_relocs,
        rows,
        info,
    })
}

type Slice<'a> = EndianSlice<'a, RunTimeEndian>;

fn attr_string(
    dwarf: &gimli::Dwarf<Slice>,
    unit: &gimli::Unit<Slice>,
    v: gimli::AttributeValue<Slice>,
) -> Result<String> {
    Ok(dwarf.attr_string(unit, v)?.to_string_lossy().into_owned())
}

/// The byte size and signedness of a type DIE, through typedefs and qualifiers.
fn base_of(unit: &gimli::Unit<Slice>, mut off: gimli::UnitOffset) -> Result<Option<(u64, bool)>> {
    for _ in 0..16 {
        let die = unit.entry(off)?;
        match die.tag() {
            gimli::DW_TAG_base_type => {
                let size = die
                    .attr_value(gimli::DW_AT_byte_size)?
                    .and_then(|v| v.udata_value());
                let enc = die.attr_value(gimli::DW_AT_encoding)?;
                let signed = matches!(enc, Some(gimli::AttributeValue::Encoding(e)) if e == gimli::DW_ATE_signed || e == gimli::DW_ATE_signed_char);
                return Ok(size.map(|s| (s, signed)));
            }
            gimli::DW_TAG_typedef | gimli::DW_TAG_const_type | gimli::DW_TAG_volatile_type => {
                match die.attr_value(gimli::DW_AT_type)? {
                    Some(gimli::AttributeValue::UnitRef(o)) => off = o,
                    _ => return Ok(None),
                }
            }
            _ => return Ok(None),
        }
    }
    Ok(None)
}

fn read_dies(
    dwarf: &gimli::Dwarf<Slice>,
    unit: &gimli::Unit<Slice>,
    info: &mut HashMap<String, FuncInfo>,
) -> Result<()> {
    let mut entries = unit.entries();
    // (depth of the subprogram, its name) while inside one; lexical-block depth.
    let mut current: Option<(isize, String)> = None;
    let mut depth: isize = 0;
    let mut block_depths: Vec<isize> = Vec::new();
    while let Some((delta, die)) = entries.next_dfs()? {
        depth += delta;
        if let Some((d, _)) = &current
            && depth <= *d
        {
            current = None;
        }
        block_depths.retain(|b| *b < depth);
        match die.tag() {
            gimli::DW_TAG_subprogram => {
                let Some(name) = die.attr_value(gimli::DW_AT_name)? else {
                    continue;
                };
                let name = attr_string(dwarf, unit, name)?;
                let decl_line = die
                    .attr_value(gimli::DW_AT_decl_line)?
                    .and_then(|v| v.udata_value())
                    .unwrap_or(0);
                let frame_base_cfa = match die.attr_value(gimli::DW_AT_frame_base)? {
                    Some(gimli::AttributeValue::Exprloc(e)) => {
                        e.0.slice() == [gimli::DW_OP_call_frame_cfa.0]
                    }
                    _ => false,
                };
                let return_base = match die.attr_value(gimli::DW_AT_type)? {
                    Some(gimli::AttributeValue::UnitRef(o)) => base_of(unit, o)?,
                    _ => None,
                };
                info.insert(
                    name.clone(),
                    FuncInfo {
                        decl_line,
                        frame_base_cfa,
                        vars: vec![],
                        return_base,
                    },
                );
                current = Some((depth, name));
            }
            gimli::DW_TAG_lexical_block if current.is_some() => block_depths.push(depth),
            gimli::DW_TAG_formal_parameter | gimli::DW_TAG_variable => {
                let Some((_, fname)) = &current else { continue };
                let Some(name) = die.attr_value(gimli::DW_AT_name)? else {
                    continue;
                };
                let name = attr_string(dwarf, unit, name)?;
                let decl_line = die
                    .attr_value(gimli::DW_AT_decl_line)?
                    .and_then(|v| v.udata_value())
                    .unwrap_or(0);
                let base = match die.attr_value(gimli::DW_AT_type)? {
                    Some(gimli::AttributeValue::UnitRef(o)) => base_of(unit, o)?,
                    _ => None,
                };
                let loc = match die.attr_value(gimli::DW_AT_location)? {
                    Some(gimli::AttributeValue::Exprloc(e)) => {
                        let mut ops = e.operations(unit.encoding());
                        match (ops.next()?, ops.next()?) {
                            (Some(gimli::Operation::FrameOffset { offset }), None) => {
                                Location::FrameSlot(offset)
                            }
                            (op, _) => Location::Other(format!("{op:?}")),
                        }
                    }
                    Some(v) => Location::Other(format!("{v:?}")),
                    None => Location::Other("no DW_AT_location".into()),
                };
                let var = Var {
                    name,
                    param: die.tag() == gimli::DW_TAG_formal_parameter,
                    decl_line,
                    base,
                    loc,
                    nested: !block_depths.is_empty(),
                };
                info.get_mut(fname)
                    .expect("current function")
                    .vars
                    .push(var);
            }
            _ => {}
        }
    }
    Ok(())
}
