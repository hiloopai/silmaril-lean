use crate::elf::{Image, Span};
use crate::hex_hash;
use iced_x86::{
    ConstantOffsets, Decoder, DecoderOptions, FlowControl, Instruction, InstructionInfoFactory,
    Mnemonic, OpAccess, OpKind, Register,
};
use object::elf;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

pub const SAMPLES: &[&str] = &[
    "sqlite3_libversion_number",
    "sqlite3_str_length",
    "sqlite3_threadsafe",
    "sqlite3_step",
    "sqlite3_mutex_enter",
    "sqlite3VdbeExec",
    "pthreadMutexEnter",
    "unixShmBarrier",
];

#[derive(Clone, Default, Serialize)]
pub struct Counts {
    pub instructions: usize,
    pub analyzed_spans: usize,
    pub invalid_decode_spans: usize,
    pub cfg_spans: usize,
    pub blocks: usize,
    pub cfg_edges: usize,
    pub direct_branch_sites: usize,
    pub invalid_local_targets: usize,
    pub direct_call_sites: usize,
    pub unknown_direct_call_sites: usize,
    pub named_direct_exit_jump_sites: usize,
    pub unknown_direct_exit_jump_sites: usize,
    pub indirect_call_sites: usize,
    pub got_named_indirect_call_sites: usize,
    pub indirect_jump_sites: usize,
    pub got_named_indirect_jump_sites: usize,
    pub switch_table_candidates: usize,
    pub lock_prefix_sites: usize,
    pub mfence_sites: usize,
    pub memory_xchg_sites: usize,
    pub mutex_transfer_sites: usize,
    pub compiler_helper_transfer_sites: usize,
    pub executable_relocations_in_decoded_spans: usize,
    pub unsupported_relocations: usize,
    pub normalized_fields: usize,
    pub unresolved_address_fields: usize,
    pub normalized_spans: usize,
}

impl Counts {
    pub fn add(&mut self, rhs: &Self) {
        // Destructuring makes newly added counters require an aggregation decision.
        let Self {
            instructions,
            analyzed_spans,
            invalid_decode_spans,
            cfg_spans,
            blocks,
            cfg_edges,
            direct_branch_sites,
            invalid_local_targets,
            direct_call_sites,
            unknown_direct_call_sites,
            named_direct_exit_jump_sites,
            unknown_direct_exit_jump_sites,
            indirect_call_sites,
            got_named_indirect_call_sites,
            indirect_jump_sites,
            got_named_indirect_jump_sites,
            switch_table_candidates,
            lock_prefix_sites,
            mfence_sites,
            memory_xchg_sites,
            mutex_transfer_sites,
            compiler_helper_transfer_sites,
            executable_relocations_in_decoded_spans,
            unsupported_relocations,
            normalized_fields,
            unresolved_address_fields,
            normalized_spans,
        } = *rhs;
        self.instructions += instructions;
        self.analyzed_spans += analyzed_spans;
        self.invalid_decode_spans += invalid_decode_spans;
        self.cfg_spans += cfg_spans;
        self.blocks += blocks;
        self.cfg_edges += cfg_edges;
        self.direct_branch_sites += direct_branch_sites;
        self.invalid_local_targets += invalid_local_targets;
        self.direct_call_sites += direct_call_sites;
        self.unknown_direct_call_sites += unknown_direct_call_sites;
        self.named_direct_exit_jump_sites += named_direct_exit_jump_sites;
        self.unknown_direct_exit_jump_sites += unknown_direct_exit_jump_sites;
        self.indirect_call_sites += indirect_call_sites;
        self.got_named_indirect_call_sites += got_named_indirect_call_sites;
        self.indirect_jump_sites += indirect_jump_sites;
        self.got_named_indirect_jump_sites += got_named_indirect_jump_sites;
        self.switch_table_candidates += switch_table_candidates;
        self.lock_prefix_sites += lock_prefix_sites;
        self.mfence_sites += mfence_sites;
        self.memory_xchg_sites += memory_xchg_sites;
        self.mutex_transfer_sites += mutex_transfer_sites;
        self.compiler_helper_transfer_sites += compiler_helper_transfer_sites;
        self.executable_relocations_in_decoded_spans += executable_relocations_in_decoded_spans;
        self.unsupported_relocations += unsupported_relocations;
        self.normalized_fields += normalized_fields;
        self.unresolved_address_fields += unresolved_address_fields;
        self.normalized_spans += normalized_spans;
    }
}

#[derive(Ord, PartialOrd, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum EdgeKind {
    Fallthrough,
    Branch,
    DirectExit,
    IndirectExit,
    Return,
    Stop,
}

pub type Edge = (usize, EdgeKind, Option<usize>);

#[derive(Default, PartialEq)]
pub struct Cfg {
    pub blocks: usize,
    pub edges: BTreeSet<Edge>,
}

#[derive(Serialize)]
pub struct Table {
    pub jump_address: u64,
    pub table_address: u64,
    pub first_two_destinations: [u64; 2],
}

#[derive(Serialize)]
pub struct Transfer {
    pub address: u64,
    pub kind: &'static str,
    pub destination: Option<String>,
}

pub struct Function {
    pub counts: Counts,
    pub exact: String,
    pub normalized: Option<String>,
    pub cfg: Option<Cfg>,
    pub direct_callees: BTreeSet<String>,
    pub special_targets: BTreeMap<String, usize>,
    pub transfer_examples: Vec<Transfer>,
    pub table_examples: Vec<Table>,
}

fn near_target(instr: &Instruction) -> Option<u64> {
    matches!(
        instr.op0_kind(),
        OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
    )
    .then(|| instr.near_branch_target())
}

fn ends_block(flow: FlowControl) -> bool {
    !matches!(
        flow,
        FlowControl::Next | FlowControl::Call | FlowControl::IndirectCall
    )
}

fn local_target(span: &Span<'_>, address: u64) -> bool {
    (span.address..span.end()).contains(&address)
}

fn add_cfg_edge(
    cfg: &mut Cfg,
    block: usize,
    kind: EdgeKind,
    target: Option<u64>,
    by_address: &BTreeMap<u64, usize>,
) {
    cfg.edges.insert((
        block,
        kind,
        target.and_then(|address| by_address.get(&address).copied()),
    ));
}

fn build_cfg(instrs: &[(Instruction, ConstantOffsets)], starts: &BTreeSet<u64>) -> Cfg {
    let by_address: BTreeMap<_, _> = starts
        .iter()
        .copied()
        .enumerate()
        .map(|(i, addr)| (addr, i))
        .collect();
    let mut cfg = Cfg {
        blocks: starts.len(),
        ..Default::default()
    };
    let mut block = 0;
    for (index, (instr, _)) in instrs.iter().enumerate() {
        if let Some(&i) = by_address.get(&instr.ip()) {
            block = i;
        }
        let next = instrs.get(index + 1).map(|(next, _)| next.ip());
        if next.is_some_and(|address| !by_address.contains_key(&address)) {
            continue;
        }
        let flow = instr.flow_control();
        if matches!(
            flow,
            FlowControl::ConditionalBranch | FlowControl::UnconditionalBranch
        ) {
            let target = near_target(instr);
            let kind = if target.is_some_and(|addr| by_address.contains_key(&addr)) {
                EdgeKind::Branch
            } else {
                EdgeKind::DirectExit
            };
            add_cfg_edge(&mut cfg, block, kind, target, &by_address);
        }
        let kind = match flow {
            FlowControl::Next
            | FlowControl::Call
            | FlowControl::IndirectCall
            | FlowControl::ConditionalBranch => EdgeKind::Fallthrough,
            FlowControl::UnconditionalBranch => continue,
            FlowControl::IndirectBranch => EdgeKind::IndirectExit,
            FlowControl::Return => EdgeKind::Return,
            _ => EdgeKind::Stop,
        };
        let target = if kind == EdgeKind::Fallthrough {
            next
        } else {
            None
        };
        add_cfg_edge(&mut cfg, block, kind, target, &by_address);
    }
    cfg
}

fn relocation_field_supported(kind: u32, width: usize, rip: bool) -> bool {
    match kind {
        elf::R_X86_64_PC8 => width == 1,
        elf::R_X86_64_PC16 => width == 2,
        elf::R_X86_64_PC32 | elf::R_X86_64_PLT32 => width == 4,
        elf::R_X86_64_GOTPCREL | elf::R_X86_64_GOTPCRELX | elf::R_X86_64_REX_GOTPCRELX => {
            rip && width == 4
        }
        _ => false,
    }
}

fn normalization(
    image: &Image<'_>,
    span: &Span<'_>,
    instrs: &[(Instruction, ConstantOffsets)],
    ordinals: &BTreeMap<u64, usize>,
    counts: &mut Counts,
) -> Option<String> {
    let mut hash = Sha256::new();
    hash.update(b"sqlite-elf-norm-v1\0");
    for (instr, offsets) in instrs {
        let rip = instr.is_ip_rel_memory_operand();
        let branch = near_target(instr);
        let field = if rip {
            let address = instr.ip_rel_memory_address();
            let label = image
                .named_code(address)
                .map(str::to_owned)
                .or_else(|| image.named_data(address));
            Some((
                offsets.displacement_offset(),
                offsets.displacement_size(),
                label,
            ))
        } else {
            branch.map(|address| {
                let label = if local_target(span, address) {
                    ordinals.get(&address).map(|index| format!("local:{index}"))
                } else {
                    image.named_code(address).map(str::to_owned)
                };
                (offsets.immediate_offset(), offsets.immediate_size(), label)
            })
        };
        for (&address, relocations) in image.relocations.range(instr.ip()..instr.next_ip()) {
            counts.executable_relocations_in_decoded_spans += relocations.len();
            for relocation in relocations {
                if !field.as_ref().is_some_and(|(offset, width, _)| {
                    address == instr.ip() + *offset as u64
                        && relocation_field_supported(relocation.kind, *width, rip)
                }) {
                    counts.unsupported_relocations += 1;
                }
            }
        }
        let begin = (instr.ip() - span.address) as usize;
        let bytes = &span.bytes[begin..begin + instr.len()];
        let mut record = [0u8; 15];
        record[..bytes.len()].copy_from_slice(bytes);
        let mut label = String::new();
        if let Some((offset, width, token)) = field {
            if let (Some(token), Some(field)) =
                (token, record[..bytes.len()].get_mut(offset..offset + width))
            {
                if width != 0 {
                    field.fill(0);
                    label = token;
                    counts.normalized_fields += 1;
                }
            }
            counts.unresolved_address_fields += usize::from(label.is_empty());
        }
        hash.update([bytes.len() as u8]);
        hash.update(&record[..bytes.len()]);
        hash.update((label.len() as u32).to_le_bytes());
        hash.update(label.as_bytes());
    }
    if counts.unresolved_address_fields == 0 && counts.unsupported_relocations == 0 {
        counts.normalized_spans = 1;
        Some(format!("{:x}", hash.finalize()))
    } else {
        None
    }
}

fn table_candidate(
    image: &Image<'_>,
    instrs: &[(Instruction, ConstantOffsets)],
    index: usize,
    ordinals: &BTreeMap<u64, usize>,
    starts: &BTreeSet<u64>,
    info: &mut InstructionInfoFactory,
) -> Option<Table> {
    let jump = &instrs[index].0;
    let reg = jump.op0_register();
    let add = &instrs.get(index.checked_sub(1)?)?.0;
    let load = &instrs.get(index.checked_sub(2)?)?.0;
    let base = add.op1_register();
    if reg == Register::None
        || base == Register::None
        || reg == base
        || add.mnemonic() != Mnemonic::Add
        || add.op0_register() != reg
        || load.mnemonic() != Mnemonic::Movsxd
        || load.op0_register() != reg
        || load.op1_kind() != OpKind::Memory
        || load.memory_base() != base
        || load.memory_index() == Register::None
        || load.memory_index_scale() != 4
        || load.memory_displacement64() != 0
        || starts.contains(&jump.ip())
        || starts.contains(&add.ip())
    {
        return None;
    }
    let mut window = instrs[index.saturating_sub(8)..index - 2].iter().rev();
    let mut nearest = load;
    let lea = window.find_map(|(i, _)| {
        if starts.contains(&nearest.ip()) || i.flow_control() != FlowControl::Next {
            return Some(None);
        }
        nearest = i;
        if i.mnemonic() == Mnemonic::Lea && i.op0_register() == base && i.is_ip_rel_memory_operand()
        {
            return Some(Some(i));
        }
        info.info(i)
            .used_registers()
            .iter()
            .any(|used| {
                used.register().full_register() == base
                    && matches!(
                        used.access(),
                        OpAccess::Write
                            | OpAccess::CondWrite
                            | OpAccess::ReadWrite
                            | OpAccess::ReadCondWrite
                    )
            })
            .then_some(None)
    })??;
    let table = lea.ip_rel_memory_address();
    let first =
        |offset| Some(table.wrapping_add_signed(i64::from(image.table_entry(table + offset)?)));
    let destinations = [first(0)?, first(4)?];
    destinations
        .iter()
        .all(|target| ordinals.contains_key(target))
        .then_some(Table {
            jump_address: jump.ip(),
            table_address: table,
            first_two_destinations: destinations,
        })
}

fn target_name(target: &str) -> &str {
    target
        .split_once(':')
        .map_or(target, |(_, name)| name)
        .split('@')
        .next()
        .unwrap_or(target)
}

fn helper(name: &str) -> bool {
    [
        "__stack_chk_",
        "__atomic_",
        "__sync_",
        "__asan_",
        "__ubsan_",
        "__tsan_",
        "__divti3",
        "__udivti3",
        "__modti3",
        "__umodti3",
        "__muloti4",
        "__tls_get_addr",
        "__x86.get_pc_thunk",
        "__x86_indirect_thunk",
    ]
    .iter()
    .any(|prefix| name.starts_with(prefix))
}

pub fn analyze(image: &Image<'_>, span: &Span<'_>) -> Function {
    let sample = span
        .names
        .iter()
        .any(|name| SAMPLES.contains(&name.as_str()));
    let mut result = Function {
        counts: Counts::default(),
        cfg: None,
        normalized: None,
        exact: hex_hash(span.bytes),
        direct_callees: BTreeSet::new(),
        special_targets: BTreeMap::new(),
        transfer_examples: Vec::new(),
        table_examples: Vec::new(),
    };
    let mut decoder = Decoder::with_ip(64, span.bytes, span.address, DecoderOptions::NONE);
    let mut instrs = Vec::new();
    let mut ordinals = BTreeMap::new();
    while decoder.can_decode() {
        let instr = decoder.decode();
        if instr.is_invalid() {
            result.counts.invalid_decode_spans = 1;
            return result;
        }
        ordinals.insert(instr.ip(), instrs.len());
        instrs.push((instr, decoder.get_constant_offsets(&instr)));
    }

    let counts = &mut result.counts;
    counts.analyzed_spans = 1;
    counts.instructions = instrs.len();
    result.normalized = normalization(image, span, &instrs, &ordinals, counts);
    let mut starts = BTreeSet::from([span.address]);
    for (instr, _) in &instrs {
        let flow = instr.flow_control();
        if ends_block(flow) && ordinals.contains_key(&instr.next_ip()) {
            starts.insert(instr.next_ip());
        }
        if matches!(
            flow,
            FlowControl::ConditionalBranch | FlowControl::UnconditionalBranch
        ) {
            counts.direct_branch_sites += 1;
            if let Some(target) = near_target(instr).filter(|&addr| local_target(span, addr)) {
                if ordinals.contains_key(&target) {
                    starts.insert(target);
                } else {
                    counts.invalid_local_targets += 1;
                }
            }
        }
    }
    if counts.invalid_local_targets == 0 {
        let cfg = build_cfg(&instrs, &starts);
        counts.cfg_spans = 1;
        counts.blocks = cfg.blocks;
        counts.cfg_edges = cfg.edges.len();
        result.cfg = Some(cfg);
    }

    let mut info = InstructionInfoFactory::new();
    for (index, (instr, _)) in instrs.iter().enumerate() {
        counts.lock_prefix_sites += usize::from(instr.has_lock_prefix());
        counts.mfence_sites += usize::from(instr.mnemonic() == Mnemonic::Mfence);
        if instr.mnemonic() == Mnemonic::Xchg
            && (0..instr.op_count()).any(|i| instr.op_kind(i) == OpKind::Memory)
        {
            counts.memory_xchg_sites += 1;
        }
        let got = instr
            .is_ip_rel_memory_operand()
            .then(|| image.got.get(&instr.ip_rel_memory_address()))
            .flatten();
        let destination = near_target(instr).and_then(|address| {
            if address != span.address && local_target(span, address) {
                ordinals.get(&address).map(|index| format!("local:{index}"))
            } else {
                image.named_code(address).map(str::to_owned)
            }
        });
        let (kind, target) = match instr.flow_control() {
            FlowControl::Call => {
                counts.direct_call_sites += 1;
                if let Some(ref target) = destination {
                    result.direct_callees.insert(target.clone());
                } else {
                    counts.unknown_direct_call_sites += 1;
                }
                ("direct_call", destination)
            }
            FlowControl::IndirectCall => {
                counts.indirect_call_sites += 1;
                counts.got_named_indirect_call_sites += usize::from(got.is_some());
                ("indirect_call", got.map(|name| format!("got:{name}")))
            }
            FlowControl::IndirectBranch => {
                counts.indirect_jump_sites += 1;
                counts.got_named_indirect_jump_sites += usize::from(got.is_some());
                if let Some(table) =
                    table_candidate(image, &instrs, index, &ordinals, &starts, &mut info)
                {
                    counts.switch_table_candidates += 1;
                    if sample && result.table_examples.len() < 3 {
                        result.table_examples.push(table);
                    }
                }
                ("indirect_jump", got.map(|name| format!("got:{name}")))
            }
            FlowControl::UnconditionalBranch
                if near_target(instr).is_none_or(|addr| !local_target(span, addr)) =>
            {
                if destination.is_some() {
                    counts.named_direct_exit_jump_sites += 1;
                } else {
                    counts.unknown_direct_exit_jump_sites += 1;
                }
                ("direct_exit_jump", destination)
            }
            _ => continue,
        };
        let mut special = false;
        if let Some(ref name) = target {
            let name = target_name(name);
            if name.starts_with("pthread_mutex_")
                || name.starts_with("sqlite3_mutex_")
                || name.starts_with("pthreadMutex")
            {
                counts.mutex_transfer_sites += 1;
                special = true;
            }
            if helper(name) {
                counts.compiler_helper_transfer_sites += 1;
                special = true;
            }
            if special {
                *result.special_targets.entry(name.to_owned()).or_default() += 1;
            }
        }
        if sample
            && (result.transfer_examples.len() < 4 || special)
            && result.transfer_examples.len() < 10
        {
            result.transfer_examples.push(Transfer {
                address: instr.ip(),
                kind,
                destination: target,
            });
        }
    }
    result
}
