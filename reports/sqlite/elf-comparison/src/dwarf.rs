use crate::{elf::Elf, Result};
use gimli::{AttributeValue, DebuggingInformationEntry, Dwarf, EndianSlice, LittleEndian, Unit};
use object::{Object, ObjectSection};
use serde::Serialize;
use std::collections::BTreeMap;

#[derive(Default, Serialize)]
pub struct InlineHints {
    pub inline_dies: usize,
    pub unresolved_inline_dies: usize,
    pub sites_by_name: BTreeMap<String, usize>,
}

type Reader<'a> = EndianSlice<'a, LittleEndian>;

#[derive(Default)]
struct Origin {
    name: Option<String>,
    parent: Option<usize>,
}

fn get_origin(
    dwarf: &Dwarf<Reader<'_>>,
    unit: &Unit<Reader<'_>>,
    die: &DebuggingInformationEntry<'_, '_, Reader<'_>>,
) -> Result<Origin> {
    let mut entry = Origin::default();
    for attribute in [gimli::DW_AT_linkage_name, gimli::DW_AT_name] {
        if let Some(value) = die.attr_value(attribute)? {
            entry.name = Some(dwarf.attr_string(unit, value)?.to_string_lossy().into());
            break;
        }
    }
    for attribute in [gimli::DW_AT_abstract_origin, gimli::DW_AT_specification] {
        entry.parent = match die.attr_value(attribute)? {
            Some(AttributeValue::UnitRef(offset)) => {
                offset.to_debug_info_offset(&unit.header).map(|o| o.0)
            }
            Some(AttributeValue::DebugInfoRef(offset)) => Some(offset.0),
            _ => None,
        };
        if entry.parent.is_some() {
            break;
        }
    }
    Ok(entry)
}

pub fn inline_hints(file: &Elf<'_>) -> Result<InlineHints> {
    let dwarf = Dwarf::load(|id| {
        let bytes = file
            .section_by_name(id.name())
            .map(|s| s.data())
            .transpose()?;
        Ok::<_, object::Error>(EndianSlice::new(bytes.unwrap_or_default(), LittleEndian))
    })?;
    let mut entries = BTreeMap::new();
    let mut inline_offsets = Vec::new();
    let mut units = dwarf.units();
    while let Some(header) = units.next()? {
        let unit = dwarf.unit(header)?;
        let mut cursor = unit.entries();
        while let Some((_, die)) = cursor.next_dfs()? {
            if matches!(
                die.tag(),
                gimli::DW_TAG_inlined_subroutine | gimli::DW_TAG_subprogram
            ) {
                let index = die
                    .offset()
                    .to_debug_info_offset(&unit.header)
                    .ok_or("missing .debug_info offset")?
                    .0;
                entries.insert(index, get_origin(&dwarf, &unit, die)?);
                if die.tag() == gimli::DW_TAG_inlined_subroutine {
                    inline_offsets.push(index);
                }
            }
        }
    }
    if entries.is_empty() {
        return Err("no DWARF subprogram DIEs".into());
    }
    let mut hints = InlineHints {
        inline_dies: inline_offsets.len(),
        ..Default::default()
    };
    for mut index in inline_offsets {
        let mut name = None;
        // Bound traversal of malformed or cyclic DIE references.
        for _ in 0..32 {
            let Some(entry) = entries.get(&index) else {
                break;
            };
            if let Some(value) = entry.name.as_ref() {
                name = Some(value);
                break;
            }
            let Some(origin) = entry.parent else { break };
            index = origin;
        }
        if let Some(name) = name {
            *hints.sites_by_name.entry(name.clone()).or_default() += 1;
        } else {
            hints.unresolved_inline_dies += 1;
        }
    }
    Ok(hints)
}
