extern crate core;

use std::{
    collections::{hash_map::Entry, HashMap},
    error::Error,
    fs,
    fs::File,
    io::BufWriter,
    mem::{discriminant, take},
    path::PathBuf,
    process,
};

use ariadne::{Color, Label, Report, ReportKind, Source};
use compact_str::CompactString;
use object::{
    elf::{
        R_PPC_ADDR16_HA, R_PPC_ADDR16_HI, R_PPC_ADDR16_LO, R_PPC_ADDR32, R_PPC_EMB_SDA21,
        R_PPC_REL14, R_PPC_REL24,
    },
    write::{SectionId, SymbolId},
    Architecture, BinaryFormat, Endianness, RelocationFlags,
};
use parser::Parser;
use powerpc_asm::{Argument, Arguments};

use crate::{
    errors::{ParseError, ParseErrorDiagnostic, SourceInfo},
    parser::{
        Arg, ArgWithSource, BinaryOpKind, Expression, Operand, RelocationKind, Statement,
        StatementArgs, Symbol, UnaryOpKind,
    },
};

mod errors;
mod parser;

#[derive(Debug, Eq, PartialEq)]
enum Visibility {
    Local,
    Global,
    Weak,
    Hidden,
}

#[derive(Debug, Eq, PartialEq)]
enum SymbolKind {
    Function,
    Object,
    Common,
}

#[derive(Debug, PartialEq)]
struct DefSym {
    name: CompactString,
    section: Option<CompactString>,
    address: Option<u32>,
    size: Option<u32>,
    kind: Option<SymbolKind>,
    visibility: Visibility,
    source: SourceInfo,
}

#[derive(Debug, Eq, PartialEq)]
struct Relocation {
    sym: CompactString,
    addend: i32,
    kind: RelocationKind,
    section: CompactString,
    offset: u32,
}

#[derive(Debug)]
struct BranchFixup {
    section: CompactString,
    offset: u32,
    target_sym: CompactString,
    addend: i32,
}

struct SectionInfo {
    kind: object::SectionKind,
    align: u64,
}

struct Analyzer {
    current_section: Option<CompactString>,
    section_offset: u32,
    replacements: HashMap<CompactString, Operand>,
    symbols: HashMap<CompactString, DefSym>,
    section_data: HashMap<CompactString, Vec<u8>>,
    section_info: HashMap<CompactString, SectionInfo>,
    section_order: Vec<CompactString>,
    relocations: Vec<Relocation>,
    branch_fixups: Vec<BranchFixup>,
    file_name: Option<CompactString>,
}

type AnalyzerResult<T> = Result<T, ParseError>;

enum ExpressionResult {
    Number(i64),
    Float(f32),
    Double(f64),
    Relocation(CompactString, i32),
}

impl Analyzer {
    fn new() -> Self {
        let mut replacements = HashMap::<CompactString, Operand>::new();
        // General-purpose and floating-point registers
        for i in 0..=31 {
            replacements.insert(format!("r{}", i).into(), Operand::Number(i, SourceInfo::new(0)));
            replacements.insert(format!("f{}", i).into(), Operand::Number(i, SourceInfo::new(0)));
        }
        // Paired-singles quantization registers
        for i in 0..=7 {
            replacements.insert(format!("qr{}", i).into(), Operand::Number(i, SourceInfo::new(0)));
        }
        // CR fields
        for i in 0..=7 {
            replacements.insert(format!("cr{}", i).into(), Operand::Number(i, SourceInfo::new(0)));
        }
        // CR bits: cr0lt=0, cr0gt=1, cr0eq=2, cr0un=3, ..., cr7un=31
        let cr_bit_names = ["lt", "gt", "eq", "un", "so"];
        for cr in 0..=7 {
            for (bit, name) in cr_bit_names.iter().enumerate() {
                let bit_num = cr * 4 + bit as i64;
                // "so" is an alias for "un" (bit 3)
                let bit_num = if *name == "so" { cr * 4 + 3 } else { bit_num };
                replacements.insert(
                    format!("cr{}{}", cr, name).into(),
                    Operand::Number(bit_num, SourceInfo::new(0)),
                );
            }
        }
        // Bare CR bit names (aliases for cr0 bits)
        replacements.insert("lt".into(), Operand::Number(0, SourceInfo::new(0)));
        replacements.insert("gt".into(), Operand::Number(1, SourceInfo::new(0)));
        replacements.insert("eq".into(), Operand::Number(2, SourceInfo::new(0)));
        replacements.insert("so".into(), Operand::Number(3, SourceInfo::new(0)));
        replacements.insert("un".into(), Operand::Number(3, SourceInfo::new(0)));
        // SPRs
        let sprs: &[(&str, i64)] = &[
            ("XER", 1),
            ("LR", 8),
            ("CTR", 9),
            ("DSISR", 18),
            ("DAR", 19),
            ("DEC", 22),
            ("SDR1", 25),
            ("SRR0", 26),
            ("SRR1", 27),
            ("SPRG0", 272),
            ("SPRG1", 273),
            ("SPRG2", 274),
            ("SPRG3", 275),
            ("EAR", 282),
            ("TBL", 284),
            ("TBU", 285),
            ("PVR", 287),
            ("IBAT0U", 528),
            ("IBAT0L", 529),
            ("IBAT1U", 530),
            ("IBAT1L", 531),
            ("IBAT2U", 532),
            ("IBAT2L", 533),
            ("IBAT3U", 534),
            ("IBAT3L", 535),
            ("DBAT0U", 536),
            ("DBAT0L", 537),
            ("DBAT1U", 538),
            ("DBAT1L", 539),
            ("DBAT2U", 540),
            ("DBAT2L", 541),
            ("DBAT3U", 542),
            ("DBAT3L", 543),
            ("GQR0", 912),
            ("GQR1", 913),
            ("GQR2", 914),
            ("GQR3", 915),
            ("GQR4", 916),
            ("GQR5", 917),
            ("GQR6", 918),
            ("GQR7", 919),
            ("HID0", 1008),
            ("HID1", 1009),
            ("HID2", 920),
            ("WPAR", 921),
            ("DMA_U", 922),
            ("DMA_L", 923),
            ("UMMCR0", 936),
            ("UPMC1", 937),
            ("UPMC2", 938),
            ("USIA", 939),
            ("UMMCR1", 940),
            ("UPMC3", 941),
            ("UPMC4", 942),
            ("USDA", 943),
            ("MMCR0", 952),
            ("PMC1", 953),
            ("PMC2", 954),
            ("SIA", 955),
            ("MMCR1", 956),
            ("PMC3", 957),
            ("PMC4", 958),
            ("SDA", 959),
            ("IABR", 1010),
            ("DABR", 1013),
            ("L2CR", 1017),
            ("ICTC", 1019),
            ("THRM1", 1020),
            ("THRM2", 1021),
            ("THRM3", 1022),
        ];
        for &(name, value) in sprs {
            replacements.insert(name.into(), Operand::Number(value, SourceInfo::new(0)));
        }
        Self {
            current_section: None,
            section_offset: 0,
            replacements,
            symbols: Default::default(),
            section_data: Default::default(),
            section_info: Default::default(),
            section_order: Vec::new(),
            relocations: Default::default(),
            branch_fixups: Default::default(),
            file_name: None,
        }
    }

    fn process(&mut self, stmt: Statement) -> AnalyzerResult<()> {
        match stmt {
            Statement::Label(sym, source) => self.label(sym, source),
            Statement::Instruction(sym, source, args) => {
                if sym.starts_with('.') {
                    match sym.as_str() {
                        ".include" => {
                            // Silently ignore (built-in replacements cover macros.inc)
                            Ok(())
                        }
                        ".section" => self.section(args, source),
                        ".text" => self.switch_section_named(".text"),
                        ".data" => self.switch_section_named(".data"),
                        ".rodata" => self.switch_section_named(".rodata"),
                        ".bss" => self.switch_section_named(".bss"),
                        ".sbss" => self.switch_section_named(".sbss"),
                        ".sdata" => self.switch_section_named(".sdata"),
                        ".sdata2" => self.switch_section_named(".sdata2"),
                        ".4byte" => self.byte4(args, source),
                        ".2byte" => self.byte2(args, source),
                        ".byte" => self.byte(args, source),
                        ".balign" => self.balign(args, source),
                        ".global" | ".globl" => self.global(args, source),
                        ".local" => self.local(args, source),
                        ".weak" => self.weak(args, source),
                        ".float" => self.float(args, source),
                        ".double" => self.double(args, source),
                        ".lcomm" => self.lcomm(args, source),
                        ".comm" => self.comm(args, source),
                        ".skip" | ".space" => self.space(args, source),
                        ".asciz" | ".string" => self.asciz(args, source),
                        ".ascii" => self.ascii(args, source),
                        ".hidden" => self.hidden(args, source),
                        ".fn" => self.dir_fn(args, source),
                        ".endfn" => self.dir_endfn(args, source),
                        ".obj" => self.dir_obj(args, source),
                        ".endobj" => self.dir_endobj(args, source),
                        ".sym" => self.dir_sym(args, source),
                        ".endsym" => self.dir_endsym(args, source),
                        ".set" => self.dir_set(args, source),
                        ".type" => self.dir_type(args, source),
                        ".size" => self.dir_size(args, source),
                        ".file" => self.dir_file(args, source),
                        ".rel" => self.dir_rel(args, source),
                        _ => Err(ParseError {
                            message: format!("unknown directive '{}'", sym),
                            diagnostics: vec![ParseErrorDiagnostic {
                                source,
                                message: format!("unknown directive"),
                                color: Color::Red,
                            }],
                            note: None,
                        }),
                    }
                } else {
                    self.assemble_instruction(&sym, args, source)
                }
            }
        }
    }

    fn assemble_instruction(
        &mut self,
        mnemonic: &str,
        args: StatementArgs,
        source: SourceInfo,
    ) -> AnalyzerResult<()> {
        let instruction_offset = self.section_offset;
        let mut asm_args: Arguments = [Argument::None; 5];
        let mut arg_idx = 0;
        let mut pending_branch_reloc: Option<(CompactString, i32)> = None;

        for arg in args {
            match arg.arg {
                Arg::Expression(expr) => {
                    let result = self.evaluate(expr)?;
                    match result {
                        ExpressionResult::Number(n) => {
                            if n < 0 {
                                asm_args[arg_idx] = Argument::Signed(n as i32);
                            } else {
                                asm_args[arg_idx] = Argument::Unsigned(n as u32);
                            }
                            arg_idx += 1;
                        }
                        ExpressionResult::Relocation(sym, addend) => {
                            let is_local_label = sym.starts_with(".L");
                            if is_local_label {
                                // Local label: try to resolve inline
                                if let Some(offset) =
                                    self.resolve_same_section(&sym, addend, instruction_offset)
                                {
                                    asm_args[arg_idx] = Argument::Signed(offset);
                                    arg_idx += 1;
                                } else {
                                    // Forward ref to local label: fixup later
                                    asm_args[arg_idx] = Argument::Signed(0);
                                    arg_idx += 1;
                                    pending_branch_reloc = Some((sym, addend));
                                }
                            } else {
                                // Named symbol: always emit relocation
                                asm_args[arg_idx] = Argument::Signed(0);
                                arg_idx += 1;
                                pending_branch_reloc = Some((sym, addend));
                            }
                        }
                        ExpressionResult::Float(_) | ExpressionResult::Double(_) => {
                            return Err(ParseError {
                                message: format!("float not valid in instruction argument"),
                                diagnostics: vec![],
                                note: None,
                            });
                        }
                    }
                }
                Arg::Offset(disp, reg) => {
                    let disp_result = self.evaluate(disp)?;
                    let reg_result = self.evaluate(reg)?;
                    match disp_result {
                        ExpressionResult::Number(n) => {
                            if n < 0 {
                                asm_args[arg_idx] = Argument::Signed(n as i32);
                            } else {
                                asm_args[arg_idx] = Argument::Unsigned(n as u32);
                            }
                        }
                        _ => {
                            return Err(ParseError {
                                message: format!("expected numeric displacement"),
                                diagnostics: vec![],
                                note: None,
                            });
                        }
                    }
                    arg_idx += 1;
                    match reg_result {
                        ExpressionResult::Number(n) => {
                            asm_args[arg_idx] = Argument::Unsigned(n as u32);
                        }
                        _ => {
                            return Err(ParseError {
                                message: format!("expected register"),
                                diagnostics: vec![],
                                note: None,
                            });
                        }
                    }
                    arg_idx += 1;
                }
                Arg::Relocation(expr, kind) => {
                    let (sym, addend) = self.evaluate_reloc(expr)?;
                    match kind {
                        RelocationKind::Sda21 => {
                            // Bare @sda21 without register: only add the immediate
                            // value (0). The linker patches both the register field
                            // and offset via R_PPC_EMB_SDA21.
                            asm_args[arg_idx] = Argument::Signed(0);
                            arg_idx += 1;
                            self.relocations.push(Relocation {
                                sym,
                                addend,
                                kind,
                                section: self.current_section.clone().unwrap(),
                                offset: instruction_offset,
                            });
                        }
                        RelocationKind::Ha | RelocationKind::H | RelocationKind::L => {
                            asm_args[arg_idx] = Argument::Signed(0);
                            arg_idx += 1;
                            self.relocations.push(Relocation {
                                sym,
                                addend,
                                kind,
                                section: self.current_section.clone().unwrap(),
                                offset: instruction_offset + 2,
                            });
                        }
                        _ => {
                            return Err(ParseError {
                                message: format!("unexpected relocation kind in instruction"),
                                diagnostics: vec![],
                                note: None,
                            });
                        }
                    }
                }
                Arg::RelocationWithOffset(expr, kind, offs_expr) => {
                    let (sym, addend) = self.evaluate_reloc(expr)?;
                    let offs_result = self.evaluate(offs_expr)?;
                    let reg = match offs_result {
                        ExpressionResult::Number(n) => n as u32,
                        _ => {
                            return Err(ParseError {
                                message: format!("expected register"),
                                diagnostics: vec![],
                                note: None,
                            });
                        }
                    };
                    match kind {
                        RelocationKind::Sda21 => {
                            asm_args[arg_idx] = Argument::Signed(0);
                            arg_idx += 1;
                            asm_args[arg_idx] = Argument::Unsigned(reg);
                            arg_idx += 1;
                            self.relocations.push(Relocation {
                                sym,
                                addend,
                                kind,
                                section: self.current_section.clone().unwrap(),
                                offset: instruction_offset,
                            });
                        }
                        RelocationKind::Ha | RelocationKind::H | RelocationKind::L => {
                            asm_args[arg_idx] = Argument::Signed(0);
                            arg_idx += 1;
                            asm_args[arg_idx] = Argument::Unsigned(reg);
                            arg_idx += 1;
                            self.relocations.push(Relocation {
                                sym,
                                addend,
                                kind,
                                section: self.current_section.clone().unwrap(),
                                offset: instruction_offset + 2,
                            });
                        }
                        _ => {
                            return Err(ParseError {
                                message: format!("unexpected relocation kind"),
                                diagnostics: vec![],
                                note: None,
                            });
                        }
                    }
                }
            }
        }

        // Assemble the instruction
        let encoded = powerpc_asm::assemble(mnemonic, &asm_args).map_err(|e| ParseError {
            message: format!("assembly error for '{}': {:?}", mnemonic, e),
            diagnostics: vec![ParseErrorDiagnostic {
                source,
                message: format!("failed to assemble"),
                color: Color::Red,
            }],
            note: None,
        })?;

        self.write_data(&encoded.to_be_bytes())?;

        // Handle unresolved branch relocations
        if let Some((sym, addend)) = pending_branch_reloc {
            let opcode = (encoded >> 26) & 0x3F;
            let _reloc_kind = match opcode {
                18 => RelocationKind::Rel24,
                16 => RelocationKind::Rel14,
                _ => RelocationKind::Absolute,
            };
            self.branch_fixups.push(BranchFixup {
                section: self.current_section.clone().unwrap(),
                offset: instruction_offset,
                target_sym: sym,
                addend,
            });
        }

        Ok(())
    }

    /// Try to resolve a symbol reference to a same-section relative offset.
    /// Returns Some(offset) if the symbol is defined in the same section.
    fn resolve_same_section(
        &self,
        sym: &CompactString,
        addend: i32,
        instruction_offset: u32,
    ) -> Option<i32> {
        let defsym = self.symbols.get(sym)?;
        let sym_section = defsym.section.as_ref()?;
        let cur_section = self.current_section.as_ref()?;
        if sym_section != cur_section {
            return None;
        }
        let addr = defsym.address?;
        Some((addr as i64 - instruction_offset as i64 + addend as i64) as i32)
    }

    /// Resolve branch fixups after all statements have been processed.
    fn resolve_branch_fixups(&mut self) -> AnalyzerResult<()> {
        let fixups = take(&mut self.branch_fixups);
        for fixup in fixups {
            let is_local_label = fixup.target_sym.starts_with(".L");

            // Determine the relocation kind from the encoded instruction
            let data = match self.section_data.get(&fixup.section) {
                Some(d) => d,
                None => continue,
            };
            let off = fixup.offset as usize;
            let insn = u32::from_be_bytes([data[off], data[off + 1], data[off + 2], data[off + 3]]);
            let opcode = (insn >> 26) & 0x3F;
            let reloc_kind = match opcode {
                18 => RelocationKind::Rel24,
                16 => RelocationKind::Rel14,
                _ => RelocationKind::Absolute,
            };

            // For local labels in the same section: patch inline, no relocation
            if is_local_label {
                if let Some(defsym) = self.symbols.get(&fixup.target_sym) {
                    if let (Some(sym_section), Some(addr)) = (&defsym.section, defsym.address) {
                        if *sym_section == fixup.section {
                            let offset =
                                (addr as i64 - fixup.offset as i64 + fixup.addend as i64) as i32;
                            let data = self.section_data.get_mut(&fixup.section).unwrap();
                            let patched = match opcode {
                                18 => (insn & !0x03FFFFFC) | ((offset as u32) & 0x03FFFFFC),
                                16 => (insn & !0x0000FFFC) | ((offset as u32) & 0x0000FFFC),
                                _ => insn,
                            };
                            let bytes = patched.to_be_bytes();
                            data[off] = bytes[0];
                            data[off + 1] = bytes[1];
                            data[off + 2] = bytes[2];
                            data[off + 3] = bytes[3];
                            continue;
                        }
                    }
                }
            }

            // Named symbols or unresolved: emit relocation
            self.relocations.push(Relocation {
                sym: fixup.target_sym,
                addend: fixup.addend,
                kind: reloc_kind,
                section: fixup.section,
                offset: fixup.offset,
            });
        }
        Ok(())
    }

    fn label(&mut self, sym: CompactString, source: SourceInfo) -> AnalyzerResult<()> {
        if let Some(defsym) = self.symbols.get_mut(&sym) {
            if defsym.address.is_some() {
                return Err(errors::symbol_redefinition(defsym, source));
            }
            defsym.section = self.current_section.clone();
            defsym.address = Some(self.section_offset);
        } else {
            self.symbols.insert(sym.clone(), DefSym {
                name: sym,
                section: self.current_section.clone(),
                address: Some(self.section_offset),
                size: None,
                kind: None,
                visibility: Visibility::Local,
                source,
            });
        }
        Ok(())
    }

    fn section(&mut self, args: StatementArgs, _source: SourceInfo) -> AnalyzerResult<()> {
        let mut name = CompactString::default();
        let mut flags = CompactString::default();
        let mut sec_type = CompactString::default();
        let mut unique_id: Option<i64> = None;
        let mut saw_unique = false;
        for (idx, arg) in args.into_iter().enumerate() {
            if saw_unique {
                if let Ok(n) = self.expect_absolute(arg) {
                    unique_id = Some(n);
                }
                saw_unique = false;
                continue;
            }
            match idx {
                0 => name = self.expect_symbol(arg)?,
                1 => {
                    if let Ok(s) = self.expect_string(arg) {
                        flags = s;
                    }
                }
                _ => {
                    match arg.arg {
                        Arg::Expression(Expression::Operand(Operand::Symbol(
                            Symbol::Regular(ref sym),
                            _,
                        ))) => {
                            if sym.as_str() == "unique" {
                                saw_unique = true;
                            } else {
                                // @nobits, @progbits, etc.
                                sec_type = sym.clone();
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        // For unique sections, use an internal key that distinguishes instances
        let internal_name = if let Some(id) = unique_id {
            CompactString::from(format!("{}\0{}", name, id))
        } else {
            name.clone()
        };
        // Determine section info from flags/type, falling back to name
        let info = if !flags.is_empty() {
            section_info_from_flags(&flags, &sec_type)
        } else {
            section_info_from_name(&name)
        };
        self.section_info.insert(internal_name.clone(), info);
        self.switch_section(internal_name)?;
        Ok(())
    }

    fn byte4(&mut self, args: StatementArgs, _source: SourceInfo) -> AnalyzerResult<()> {
        if args.is_empty() {
            return self.write_data(&[0u8; 4]);
        }
        for value in args {
            match value.arg {
                Arg::Expression(expr) => {
                    let result = self.evaluate(expr)?;
                    match result {
                        ExpressionResult::Number(n) => {
                            self.write_data(&(n as u32).to_be_bytes())?;
                        }
                        ExpressionResult::Float(_) | ExpressionResult::Double(_) => {
                            return Err(ParseError {
                                message: format!("float value not permitted for .4byte"),
                                diagnostics: vec![],
                                note: None,
                            });
                        }
                        ExpressionResult::Relocation(sym, addend) => {
                            self.relocations.push(Relocation {
                                sym,
                                addend,
                                kind: RelocationKind::Absolute,
                                section: self.current_section.clone().unwrap(),
                                offset: self.section_offset,
                            });
                            self.write_data(&[0u8; 4])?;
                        }
                    }
                }
                _ => {
                    return Err(ParseError {
                        message: format!("unexpected argument type for .4byte"),
                        diagnostics: vec![],
                        note: None,
                    });
                }
            }
        }
        Ok(())
    }

    fn byte2(&mut self, args: StatementArgs, _source: SourceInfo) -> AnalyzerResult<()> {
        for value in args {
            match value.arg {
                Arg::Expression(expr) => {
                    let result = self.evaluate(expr)?;
                    match result {
                        ExpressionResult::Number(n) => {
                            self.write_data(&(n as u16).to_be_bytes())?;
                        }
                        ExpressionResult::Float(_) | ExpressionResult::Double(_) => {
                            return Err(ParseError {
                                message: format!("float value not permitted for .2byte"),
                                diagnostics: vec![],
                                note: None,
                            });
                        }
                        ExpressionResult::Relocation(sym, addend) => {
                            self.relocations.push(Relocation {
                                sym,
                                addend,
                                kind: RelocationKind::Absolute,
                                section: self.current_section.clone().unwrap(),
                                offset: self.section_offset,
                            });
                            self.write_data(&[0u8; 2])?;
                        }
                    }
                }
                _ => {
                    return Err(ParseError {
                        message: format!("unexpected argument type for .2byte"),
                        diagnostics: vec![],
                        note: None,
                    });
                }
            }
        }
        Ok(())
    }

    fn byte(&mut self, args: StatementArgs, _source: SourceInfo) -> AnalyzerResult<()> {
        for value in args {
            match value.arg {
                Arg::Expression(expr) => {
                    let result = self.evaluate(expr)?;
                    match result {
                        ExpressionResult::Number(n) => {
                            self.write_data(&[n as u8])?;
                        }
                        ExpressionResult::Float(_) | ExpressionResult::Double(_) => {
                            return Err(ParseError {
                                message: format!("float value not permitted for .byte"),
                                diagnostics: vec![],
                                note: None,
                            });
                        }
                        ExpressionResult::Relocation(sym, addend) => {
                            self.relocations.push(Relocation {
                                sym,
                                addend,
                                kind: RelocationKind::Absolute,
                                section: self.current_section.clone().unwrap(),
                                offset: self.section_offset,
                            });
                            self.write_data(&[0u8; 1])?;
                        }
                    }
                }
                _ => {
                    return Err(ParseError {
                        message: format!("unexpected argument type for .byte"),
                        diagnostics: vec![],
                        note: None,
                    });
                }
            }
        }
        Ok(())
    }

    fn float(&mut self, args: StatementArgs, _source: SourceInfo) -> AnalyzerResult<()> {
        for value in args {
            match value.arg {
                Arg::Expression(expr) => {
                    let f = self.evaluate_as_f64(expr)?;
                    self.write_data(&(f as f32).to_be_bytes())?;
                }
                _ => {
                    return Err(ParseError {
                        message: format!("expected float value"),
                        diagnostics: vec![],
                        note: None,
                    });
                }
            }
        }
        Ok(())
    }

    fn double(&mut self, args: StatementArgs, _source: SourceInfo) -> AnalyzerResult<()> {
        for value in args {
            match value.arg {
                Arg::Expression(expr) => {
                    let f = self.evaluate_as_f64(expr)?;
                    self.write_data(&f.to_be_bytes())?;
                }
                _ => {
                    return Err(ParseError {
                        message: format!("expected double value"),
                        diagnostics: vec![],
                        note: None,
                    });
                }
            }
        }
        Ok(())
    }

    fn asciz(&mut self, args: StatementArgs, _source: SourceInfo) -> AnalyzerResult<()> {
        for value in args {
            let str = self.expect_string(value)?;
            // Convert chars to raw bytes: each char U+0000-U+00FF maps to a single byte.
            // This is necessary because octal/hex escapes like \203 produce U+0083 in the
            // Rust string, but we need the raw byte 0x83 in the output.
            let bytes: Vec<u8> = str.chars().map(|c| c as u8).collect();
            self.write_data(&bytes)?;
            self.fill_data(1, 0)?;
        }
        Ok(())
    }

    fn ascii(&mut self, args: StatementArgs, _source: SourceInfo) -> AnalyzerResult<()> {
        for value in args {
            let str = self.expect_string(value)?;
            let bytes: Vec<u8> = str.chars().map(|c| c as u8).collect();
            self.write_data(&bytes)?;
            // No null terminator (unlike .asciz/.string)
        }
        Ok(())
    }

    fn hidden(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        for arg in args {
            let sym = self.expect_symbol(arg)?;
            match self.symbols.entry(sym.clone()) {
                Entry::Occupied(mut entry) => {
                    entry.get_mut().visibility = Visibility::Hidden;
                }
                Entry::Vacant(entry) => {
                    entry.insert(DefSym {
                        name: sym,
                        section: None,
                        address: None,
                        size: None,
                        kind: None,
                        visibility: Visibility::Hidden,
                        source,
                    });
                }
            }
        }
        Ok(())
    }

    fn balign(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        const USAGE: &str = "usage: .balign [align[, fill]]";
        let add_usage = |mut e: ParseError| {
            e.diagnostics.push(ParseErrorDiagnostic {
                source,
                message: USAGE.into(),
                color: Color::Green,
            });
            e
        };

        let mut align = 0u32;
        let mut fill = 0u8;
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => align = self.expect_absolute(arg).map_err(add_usage)? as u32,
                1 => fill = self.expect_absolute(arg).map_err(add_usage)? as u8,
                _ => return Err(errors::extra_arg(".balign", &arg)),
            }
        }
        if align > 0 {
            let count = ((self.section_offset + align - 1) & !(align - 1)) - self.section_offset;
            if count > 0 {
                self.fill_data(count, fill)?;
            }
        }
        Ok(())
    }

    fn global(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        if args.is_empty() {
            return Err(errors::missing_arg(".global", 1, &args, source));
        }
        for arg in args {
            let sym = self.expect_symbol(arg)?;
            match self.symbols.entry(sym.clone()) {
                Entry::Occupied(mut entry) => {
                    entry.get_mut().visibility = Visibility::Global;
                }
                Entry::Vacant(entry) => {
                    entry.insert(DefSym {
                        name: sym,
                        section: None,
                        address: None,
                        size: None,
                        kind: None,
                        visibility: Visibility::Global,
                        source,
                    });
                }
            }
        }
        Ok(())
    }

    fn local(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        for arg in args {
            let sym = self.expect_symbol(arg)?;
            match self.symbols.entry(sym.clone()) {
                Entry::Occupied(mut entry) => {
                    entry.get_mut().visibility = Visibility::Local;
                }
                Entry::Vacant(entry) => {
                    entry.insert(DefSym {
                        name: sym,
                        section: None,
                        address: None,
                        size: None,
                        kind: None,
                        visibility: Visibility::Local,
                        source,
                    });
                }
            }
        }
        Ok(())
    }

    fn weak(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        for arg in args {
            let sym = self.expect_symbol(arg)?;
            match self.symbols.entry(sym.clone()) {
                Entry::Occupied(mut entry) => {
                    entry.get_mut().visibility = Visibility::Weak;
                }
                Entry::Vacant(entry) => {
                    entry.insert(DefSym {
                        name: sym,
                        section: None,
                        address: None,
                        size: None,
                        kind: None,
                        visibility: Visibility::Weak,
                        source,
                    });
                }
            }
        }
        Ok(())
    }

    fn lcomm(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        let mut sym = CompactString::default();
        let mut size = 0u32;
        let mut align = 4u32;
        if args.len() < 2 {
            return Err(errors::missing_arg(".lcomm", 2, &args, source));
        }
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => sym = self.expect_symbol(arg)?,
                1 => size = self.expect_absolute(arg)? as u32,
                2 => align = self.expect_absolute(arg)? as u32,
                _ => return Err(errors::extra_arg(".lcomm", &arg)),
            }
        }
        let prev_section = self.current_section.clone();
        self.switch_section_named(".bss")?;
        // Align the current offset before placing the symbol
        if align > 1 {
            let padding = ((self.section_offset + align - 1) & !(align - 1)) - self.section_offset;
            if padding > 0 {
                self.fill_data(padding, 0)?;
            }
        }
        match self.symbols.entry(sym.clone()) {
            Entry::Occupied(mut entry) => {
                let defsym = entry.get_mut();
                if defsym.address.is_some() {
                    return Err(errors::symbol_redefinition(defsym, source));
                }
                defsym.address = Some(self.section_offset);
                defsym.section = self.current_section.clone();
                defsym.size = Some(size);
                defsym.kind = Some(SymbolKind::Common);
            }
            Entry::Vacant(entry) => {
                entry.insert(DefSym {
                    name: sym,
                    section: self.current_section.clone(),
                    address: Some(self.section_offset),
                    size: Some(size),
                    kind: Some(SymbolKind::Common),
                    visibility: Visibility::Local,
                    source,
                });
            }
        }
        self.fill_data(size, 0)?;
        if let Some(section) = prev_section {
            self.switch_section(section)?;
        }
        Ok(())
    }

    fn comm(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        let mut sym = CompactString::default();
        let mut size = 0u32;
        let mut align = 4u32;
        if args.len() < 2 {
            return Err(errors::missing_arg(".comm", 2, &args, source));
        }
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => sym = self.expect_symbol(arg)?,
                1 => size = self.expect_absolute(arg)? as u32,
                2 => align = self.expect_absolute(arg)? as u32,
                _ => return Err(errors::extra_arg(".comm", &arg)),
            }
        }
        // Common symbols don't live in a section; the linker allocates space.
        // st_value = alignment, st_size = size, st_shndx = SHN_COMMON
        match self.symbols.entry(sym.clone()) {
            Entry::Occupied(mut entry) => {
                let defsym = entry.get_mut();
                if defsym.address.is_some() {
                    return Err(errors::symbol_redefinition(defsym, source));
                }
                defsym.address = Some(align);
                defsym.size = Some(size);
                defsym.kind = Some(SymbolKind::Common);
            }
            Entry::Vacant(entry) => {
                entry.insert(DefSym {
                    name: sym,
                    section: None,
                    address: Some(align),
                    size: Some(size),
                    kind: Some(SymbolKind::Common),
                    visibility: Visibility::Global,
                    source,
                });
            }
        }
        Ok(())
    }

    fn space(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        let mut size = 0u32;
        let mut fill = 0u8;
        if args.is_empty() {
            return Err(errors::missing_arg(".space", 1, &args, source));
        }
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => size = self.expect_absolute(arg)? as u32,
                1 => fill = self.expect_absolute(arg)? as u8,
                _ => return Err(errors::extra_arg(".space", &arg)),
            }
        }
        self.fill_data(size, fill)?;
        Ok(())
    }

    // .fn name, visibility
    fn dir_fn(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        let mut name = CompactString::default();
        let mut vis = Visibility::Local;
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => name = self.expect_symbol(arg)?,
                1 => {
                    let v = self.expect_symbol(arg)?;
                    vis = parse_visibility(&v);
                }
                _ => return Err(errors::extra_arg(".fn", &arg)),
            }
        }
        self.set_symbol_vis_and_kind(&name, vis, Some(SymbolKind::Function), source)?;
        self.label(name, source)
    }

    fn dir_endfn(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        let mut name = CompactString::default();
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => name = self.expect_symbol(arg)?,
                _ => return Err(errors::extra_arg(".endfn", &arg)),
            }
        }
        self.set_symbol_size(&name, source)
    }

    // .obj name, visibility
    fn dir_obj(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        let mut name = CompactString::default();
        let mut vis = Visibility::Local;
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => name = self.expect_symbol(arg)?,
                1 => {
                    let v = self.expect_symbol(arg)?;
                    vis = parse_visibility(&v);
                }
                _ => return Err(errors::extra_arg(".obj", &arg)),
            }
        }
        self.set_symbol_vis_and_kind(&name, vis, Some(SymbolKind::Object), source)?;
        self.label(name, source)
    }

    fn dir_endobj(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        let mut name = CompactString::default();
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => name = self.expect_symbol(arg)?,
                _ => return Err(errors::extra_arg(".endobj", &arg)),
            }
        }
        self.set_symbol_size(&name, source)
    }

    // .sym name, visibility
    fn dir_sym(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        let mut name = CompactString::default();
        let mut vis = Visibility::Local;
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => name = self.expect_symbol(arg)?,
                1 => {
                    let v = self.expect_symbol(arg)?;
                    vis = parse_visibility(&v);
                }
                _ => return Err(errors::extra_arg(".sym", &arg)),
            }
        }
        self.set_symbol_vis_and_kind(&name, vis, None, source)?;
        self.label(name, source)
    }

    fn dir_endsym(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        let mut name = CompactString::default();
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => name = self.expect_symbol(arg)?,
                _ => return Err(errors::extra_arg(".endsym", &arg)),
            }
        }
        self.set_symbol_size(&name, source)
    }

    // .set name, value
    fn dir_set(&mut self, args: StatementArgs, _source: SourceInfo) -> AnalyzerResult<()> {
        let mut name = CompactString::default();
        let mut value = 0i64;
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => name = self.expect_symbol(arg)?,
                1 => value = self.expect_absolute(arg)?,
                _ => return Err(errors::extra_arg(".set", &arg)),
            }
        }
        self.replacements.insert(name, Operand::Number(value, SourceInfo::new(0)));
        Ok(())
    }

    // .type name, @function/@object
    fn dir_type(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        let mut name = CompactString::default();
        let mut type_str = CompactString::default();
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => name = self.expect_symbol(arg)?,
                1 => type_str = self.expect_constant(arg)?,
                _ => return Err(errors::extra_arg(".type", &arg)),
            }
        }
        let kind = match type_str.as_str() {
            "@function" => Some(SymbolKind::Function),
            "@object" => Some(SymbolKind::Object),
            _ => None,
        };
        if let Some(defsym) = self.symbols.get_mut(&name) {
            defsym.kind = kind;
        } else {
            self.symbols.insert(name.clone(), DefSym {
                name,
                section: None,
                address: None,
                size: None,
                kind,
                visibility: Visibility::Local,
                source,
            });
        }
        Ok(())
    }

    // .size name, expr
    fn dir_size(&mut self, args: StatementArgs, _source: SourceInfo) -> AnalyzerResult<()> {
        let mut name = CompactString::default();
        let mut size_val = 0u32;
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => name = self.expect_symbol(arg)?,
                1 => size_val = self.expect_absolute(arg)? as u32,
                _ => return Err(errors::extra_arg(".size", &arg)),
            }
        }
        if let Some(defsym) = self.symbols.get_mut(&name) {
            defsym.size = Some(size_val);
        }
        Ok(())
    }

    // .file "name"
    fn dir_file(&mut self, args: StatementArgs, _source: SourceInfo) -> AnalyzerResult<()> {
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => {
                    let name = self.expect_string(arg)?;
                    self.file_name = Some(name);
                }
                _ => {} // ignore extra args
            }
        }
        Ok(())
    }

    // .rel sym1, sym2 - emit a 4-byte relocation targeting sym1 with
    // addend = sym2_addr - sym1_addr (decomp-toolkit convention)
    fn dir_rel(&mut self, args: StatementArgs, _source: SourceInfo) -> AnalyzerResult<()> {
        let mut sym1 = CompactString::default();
        let mut sym2 = CompactString::default();
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => sym1 = self.expect_symbol(arg)?,
                1 => sym2 = self.expect_symbol(arg)?,
                _ => return Err(errors::extra_arg(".rel", &arg)),
            }
        }
        let addend = match (self.symbols.get(&sym1), self.symbols.get(&sym2)) {
            (Some(def1), Some(def2)) => match (def1.address, def2.address) {
                (Some(a1), Some(a2)) => (a2 as i32) - (a1 as i32),
                _ => 0,
            },
            _ => 0,
        };
        self.relocations.push(Relocation {
            sym: sym1,
            addend,
            kind: RelocationKind::Absolute,
            section: self.current_section.clone().unwrap(),
            offset: self.section_offset,
        });
        self.write_data(&[0u8; 4])?;
        Ok(())
    }

    fn set_symbol_vis_and_kind(
        &mut self,
        name: &CompactString,
        vis: Visibility,
        kind: Option<SymbolKind>,
        source: SourceInfo,
    ) -> AnalyzerResult<()> {
        match self.symbols.entry(name.clone()) {
            Entry::Occupied(mut entry) => {
                let defsym = entry.get_mut();
                defsym.visibility = vis;
                if kind.is_some() {
                    defsym.kind = kind;
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(DefSym {
                    name: name.clone(),
                    section: None,
                    address: None,
                    size: None,
                    kind,
                    visibility: vis,
                    source,
                });
            }
        }
        Ok(())
    }

    fn set_symbol_size(&mut self, name: &CompactString, _source: SourceInfo) -> AnalyzerResult<()> {
        if let Some(defsym) = self.symbols.get_mut(name) {
            if let Some(addr) = defsym.address {
                defsym.size = Some(self.section_offset - addr);
            }
        }
        Ok(())
    }

    fn write_data(&mut self, bytes: &[u8]) -> AnalyzerResult<()> {
        let curr_section = self.current_section.clone().ok_or(ParseError {
            message: "[internal] write_data called without a section".into(),
            diagnostics: vec![],
            note: None,
        })?;
        self.section_data.entry(curr_section).or_default().extend_from_slice(bytes);
        self.section_offset += bytes.len() as u32;
        Ok(())
    }

    fn fill_data(&mut self, count: u32, value: u8) -> AnalyzerResult<()> {
        let curr_section = self.current_section.clone().ok_or(ParseError {
            message: "[internal] fill_data called without a section".into(),
            diagnostics: vec![],
            note: None,
        })?;
        let data = self.section_data.entry(curr_section).or_default();
        data.resize(data.len() + count as usize, value);
        self.section_offset += count;
        Ok(())
    }

    fn evaluate(&mut self, expr: Expression) -> AnalyzerResult<ExpressionResult> {
        match expr {
            Expression::BinaryOp(lhs, kind, rhs) => {
                let left = self.evaluate(*lhs)?;
                let right = self.evaluate(*rhs)?;
                match (left, right) {
                    (ExpressionResult::Number(l), ExpressionResult::Number(r)) => match kind {
                        BinaryOpKind::Mul => Ok(ExpressionResult::Number(l * r)),
                        BinaryOpKind::Div => Ok(ExpressionResult::Number(l / r)),
                        BinaryOpKind::Rem => Ok(ExpressionResult::Number(l % r)),
                        BinaryOpKind::Shl => Ok(ExpressionResult::Number(l << r)),
                        BinaryOpKind::Shr => Ok(ExpressionResult::Number(l >> r)),
                        BinaryOpKind::Or => Ok(ExpressionResult::Number(l | r)),
                        BinaryOpKind::And => Ok(ExpressionResult::Number(l & r)),
                        BinaryOpKind::Xor => Ok(ExpressionResult::Number(l ^ r)),
                        BinaryOpKind::Nor => Ok(ExpressionResult::Number(!(l | r))),
                        BinaryOpKind::Add => Ok(ExpressionResult::Number(l + r)),
                        BinaryOpKind::Sub => Ok(ExpressionResult::Number(l - r)),
                        BinaryOpKind::Eq => {
                            Ok(ExpressionResult::Number(if l == r { -1 } else { 0 }))
                        }
                        BinaryOpKind::Neq => {
                            Ok(ExpressionResult::Number(if l != r { -1 } else { 0 }))
                        }
                        BinaryOpKind::Lt => {
                            Ok(ExpressionResult::Number(if l < r { -1 } else { 0 }))
                        }
                        BinaryOpKind::Gt => {
                            Ok(ExpressionResult::Number(if l > r { -1 } else { 0 }))
                        }
                        BinaryOpKind::Le => {
                            Ok(ExpressionResult::Number(if l <= r { -1 } else { 0 }))
                        }
                        BinaryOpKind::Ge => {
                            Ok(ExpressionResult::Number(if l >= r { -1 } else { 0 }))
                        }
                        BinaryOpKind::LAnd => {
                            Ok(ExpressionResult::Number(if l != 0 && r != 0 { 1 } else { 0 }))
                        }
                        BinaryOpKind::LOr => {
                            Ok(ExpressionResult::Number(if l != 0 || r != 0 { 1 } else { 0 }))
                        }
                    },
                    (ExpressionResult::Relocation(sym, l), ExpressionResult::Number(r)) => {
                        match kind {
                            BinaryOpKind::Add => {
                                Ok(ExpressionResult::Relocation(sym, (l as i64 + r) as i32))
                            }
                            BinaryOpKind::Sub => {
                                Ok(ExpressionResult::Relocation(sym, (l as i64 - r) as i32))
                            }
                            _ => Err(ParseError {
                                message: format!(
                                    "can't perform {:?} between relocation and number",
                                    kind,
                                ),
                                diagnostics: vec![],
                                note: None,
                            }),
                        }
                    }
                    (ExpressionResult::Number(l), ExpressionResult::Relocation(sym, r)) => {
                        match kind {
                            BinaryOpKind::Add => {
                                Ok(ExpressionResult::Relocation(sym, (l + r as i64) as i32))
                            }
                            _ => Err(ParseError {
                                message: format!(
                                    "can't perform {:?} between number and relocation",
                                    kind,
                                ),
                                diagnostics: vec![],
                                note: None,
                            }),
                        }
                    }
                    (
                        ExpressionResult::Relocation(sym_l, add_l),
                        ExpressionResult::Relocation(sym_r, add_r),
                    ) => {
                        match kind {
                            BinaryOpKind::Sub => {
                                // sym_l - sym_r: if both in same section, resolves to a number
                                if let (Some(def_l), Some(def_r)) =
                                    (self.symbols.get(&sym_l), self.symbols.get(&sym_r))
                                {
                                    if let (Some(sec_l), Some(sec_r), Some(addr_l), Some(addr_r)) = (
                                        &def_l.section,
                                        &def_r.section,
                                        def_l.address,
                                        def_r.address,
                                    ) {
                                        if sec_l == sec_r {
                                            return Ok(ExpressionResult::Number(
                                                addr_l as i64 - addr_r as i64 + add_l as i64
                                                    - add_r as i64,
                                            ));
                                        }
                                    }
                                }
                                Err(ParseError {
                                    message: format!(
                                        "can't subtract relocations from different sections"
                                    ),
                                    diagnostics: vec![],
                                    note: None,
                                })
                            }
                            _ => Err(ParseError {
                                message: format!(
                                    "can't perform {:?} between two relocations",
                                    kind,
                                ),
                                diagnostics: vec![],
                                note: None,
                            }),
                        }
                    }
                    (left, right) => Err(ParseError {
                        message: format!(
                            "can't perform {:?} on types {:?} and {:?}",
                            kind,
                            discriminant(&left),
                            discriminant(&right)
                        ),
                        diagnostics: vec![],
                        note: None,
                    }),
                }
            }
            Expression::UnaryOp(kind, expr) => {
                let result = self.evaluate(*expr)?;
                match result {
                    ExpressionResult::Number(n) => match kind {
                        UnaryOpKind::Pos => Ok(ExpressionResult::Number(n)),
                        UnaryOpKind::Neg => Ok(ExpressionResult::Number(-n)),
                        UnaryOpKind::Comp => Ok(ExpressionResult::Number(!n)),
                    },
                    ExpressionResult::Float(n) => match kind {
                        UnaryOpKind::Pos => Ok(ExpressionResult::Float(n)),
                        UnaryOpKind::Neg => Ok(ExpressionResult::Float(-n)),
                        _ => Err(ParseError {
                            message: format!("can't perform {:?} on float", kind),
                            diagnostics: vec![],
                            note: None,
                        }),
                    },
                    ExpressionResult::Double(n) => match kind {
                        UnaryOpKind::Pos => Ok(ExpressionResult::Double(n)),
                        UnaryOpKind::Neg => Ok(ExpressionResult::Double(-n)),
                        _ => Err(ParseError {
                            message: format!("can't perform {:?} on float", kind),
                            diagnostics: vec![],
                            note: None,
                        }),
                    },
                    ExpressionResult::Relocation(sym, addend) => match kind {
                        // +reloc is a no-op (handles branch hints like beq+ label)
                        UnaryOpKind::Pos => Ok(ExpressionResult::Relocation(sym, addend)),
                        // -reloc makes sense for same-section diffs (handled elsewhere)
                        UnaryOpKind::Neg => Ok(ExpressionResult::Relocation(sym, -addend)),
                        _ => Err(ParseError {
                            message: format!("can't perform {:?} on relocation", kind),
                            diagnostics: vec![],
                            note: None,
                        }),
                    },
                }
            }
            Expression::Operand(operand) => {
                match operand {
                    Operand::Number(n, _source) => Ok(ExpressionResult::Number(n)),
                    Operand::Float(n, _source) => Ok(ExpressionResult::Float(n)),
                    Operand::Double(n, _source) => Ok(ExpressionResult::Double(n)),
                    Operand::Symbol(sym, _source) => {
                        let sym = match sym {
                            Symbol::Regular(sym) => {
                                if sym.as_str() == "." {
                                    return Ok(ExpressionResult::Number(
                                        self.section_offset as i64,
                                    ));
                                }
                                if let Some(replacement) = self.replacements.get(&sym) {
                                    return match replacement {
                                        Operand::Number(n, _) => Ok(ExpressionResult::Number(*n)),
                                        Operand::Float(n, _) => Ok(ExpressionResult::Float(*n)),
                                        Operand::Double(n, _) => Ok(ExpressionResult::Double(*n)),
                                        Operand::Symbol(_, _) => unreachable!(),
                                        Operand::Expression(_) => unreachable!(),
                                    };
                                }
                                sym
                            }
                            Symbol::Quoted(sym) => sym,
                        };
                        // Always return Relocation for symbols that have a section
                        // (labels), so call sites can decide how to handle them.
                        // Symbols without a section and with an address are .set constants.
                        if let Some(defsym) = self.symbols.get(&sym) {
                            if defsym.section.is_some() {
                                return Ok(ExpressionResult::Relocation(sym, 0));
                            }
                            if let Some(addr) = defsym.address {
                                return Ok(ExpressionResult::Number(addr as i64));
                            }
                        }
                        Ok(ExpressionResult::Relocation(sym, 0))
                    }
                    Operand::Expression(_) => unreachable!(),
                }
            }
        }
    }

    /// Evaluate an expression as f64, preserving negative zero.
    /// Used by .float and .double directives.
    fn evaluate_as_f64(&mut self, expr: Expression) -> AnalyzerResult<f64> {
        // Handle unary negation specially to preserve -0.0
        if let Expression::UnaryOp(UnaryOpKind::Neg, inner) = expr {
            let val = self.evaluate_as_f64(*inner)?;
            return Ok(-val);
        }
        let result = self.evaluate(expr)?;
        match result {
            ExpressionResult::Number(n) => Ok(n as f64),
            ExpressionResult::Float(n) => Ok(n as f64),
            ExpressionResult::Double(n) => Ok(n),
            ExpressionResult::Relocation(_, _) => Err(ParseError {
                message: format!("expected numeric value for float/double"),
                diagnostics: vec![],
                note: None,
            }),
        }
    }

    /// Evaluate an expression in a relocation context.
    /// Unlike regular evaluate(), this treats bare symbol names as relocations
    /// even if they match a replacement (register name), since `sym@ha` means
    /// "the symbol named sym", not "register number".
    fn evaluate_reloc(&mut self, expr: Expression) -> AnalyzerResult<(CompactString, i32)> {
        // For simple symbol operands, return the name directly
        match &expr {
            Expression::Operand(Operand::Symbol(Symbol::Regular(sym), _)) => {
                return Ok((sym.clone(), 0));
            }
            Expression::Operand(Operand::Symbol(Symbol::Quoted(sym), _)) => {
                return Ok((sym.clone(), 0));
            }
            _ => {}
        }
        // For complex expressions, evaluate and expect a Relocation result
        let result = self.evaluate(expr)?;
        match result {
            ExpressionResult::Relocation(sym, addend) => Ok((sym, addend)),
            _ => Err(ParseError {
                message: format!("expected symbol for relocation"),
                diagnostics: vec![],
                note: None,
            }),
        }
    }

    /// Expect an absolute value
    fn expect_absolute(&mut self, value: ArgWithSource) -> AnalyzerResult<i64> {
        let result = match value.arg {
            Arg::Expression(expr) => self.evaluate(expr),
            _ => Err(errors::arg_expected("absolute value", &value)),
        }?;
        match result {
            ExpressionResult::Number(n) => Ok(n),
            _ => Err(errors::result_expected("absolute value", &result, value.source)),
        }
    }

    /// Expect a symbol, regular or quoted
    fn expect_symbol(&mut self, value: ArgWithSource) -> AnalyzerResult<CompactString> {
        match value.arg {
            Arg::Expression(Expression::Operand(Operand::Symbol(mut sym, _))) => {
                Ok(sym.take_string())
            }
            _ => Err(errors::arg_expected("symbol", &value)),
        }
    }

    /// Expect a quoted string
    fn expect_string(&mut self, value: ArgWithSource) -> AnalyzerResult<CompactString> {
        match value.arg {
            Arg::Expression(Expression::Operand(Operand::Symbol(Symbol::Quoted(sym), _))) => {
                Ok(sym)
            }
            _ => Err(errors::arg_expected("string", &value)),
        }
    }

    /// Expect a constant symbol (non-quoted)
    fn expect_constant(&mut self, value: ArgWithSource) -> AnalyzerResult<CompactString> {
        match value.arg {
            Arg::Expression(Expression::Operand(Operand::Symbol(Symbol::Regular(sym), _))) => {
                Ok(sym)
            }
            _ => Err(errors::arg_expected("constant", &value)),
        }
    }

    /// Switch to a well-known section by name, registering its info from defaults.
    fn switch_section_named(&mut self, name: &str) -> AnalyzerResult<()> {
        let name: CompactString = name.into();
        if !self.section_info.contains_key(&name) {
            self.section_info.insert(name.clone(), section_info_from_name(&name));
        }
        self.switch_section(name)
    }

    fn switch_section(&mut self, name: CompactString) -> AnalyzerResult<()> {
        self.section_offset =
            self.section_data.get(&name).map(|v| v.len() as u32).unwrap_or_default();
        if !self.section_order.contains(&name) {
            self.section_order.push(name.clone());
        }
        self.current_section = Some(name);
        Ok(())
    }
}

/// Determine section kind and alignment from flags and type.
/// `flags` is the GAS flags string (e.g. "ax", "wa", "a").
/// `sec_type` is the GAS type (e.g. "@nobits", "@progbits", or empty).
fn section_info_from_flags(flags: &str, sec_type: &str) -> SectionInfo {
    let is_nobits = sec_type == "@nobits";
    let has_x = flags.contains('x');
    let has_w = flags.contains('w');

    let kind = if is_nobits {
        object::SectionKind::UninitializedData
    } else if has_x {
        object::SectionKind::Text
    } else if has_w {
        object::SectionKind::Data
    } else {
        object::SectionKind::ReadOnlyData
    };

    let align = if has_x { 4 } else { 8 };
    SectionInfo { kind, align }
}

/// Determine section kind and alignment from a well-known section name.
fn section_info_from_name(name: &str) -> SectionInfo {
    match name {
        ".text" | ".init" => SectionInfo { kind: object::SectionKind::Text, align: 4 },
        ".data" | ".sdata" => SectionInfo { kind: object::SectionKind::Data, align: 8 },
        ".rodata" | ".sdata2" => SectionInfo { kind: object::SectionKind::ReadOnlyData, align: 8 },
        ".bss" | ".sbss" | ".sbss2" => {
            SectionInfo { kind: object::SectionKind::UninitializedData, align: 8 }
        }
        ".ctors" | ".dtors" => SectionInfo { kind: object::SectionKind::Data, align: 4 },
        _ => SectionInfo { kind: object::SectionKind::Data, align: 4 },
    }
}

fn parse_visibility(s: &str) -> Visibility {
    match s {
        "global" => Visibility::Global,
        "weak" => Visibility::Weak,
        _ => Visibility::Local,
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: ppcasm <input.s> [-o output.o]");
        process::exit(1);
    }

    let input_path = PathBuf::from(&args[1]);
    let output_path = if let Some(pos) = args.iter().position(|a| a == "-o") {
        if pos + 1 < args.len() {
            PathBuf::from(&args[pos + 1])
        } else {
            eprintln!("Error: -o requires an argument");
            process::exit(1);
        }
    } else {
        input_path.with_extension("o")
    };

    let filename = input_path
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or("[unknown]".into());
    let result = fs::read_to_string(&input_path)?;
    let mut parser = Parser::new(result.as_str());
    let mut analyzer = Analyzer::new();
    let mut had_error = false;
    while !parser.at_end() {
        let stmt = match parser.statement() {
            Ok(stmt) => stmt,
            Err(e) => {
                print_error(&e, filename.as_str(), result.as_str())?;
                had_error = true;
                break;
            }
        };
        match analyzer.process(stmt) {
            Ok(_) => {}
            Err(e) => {
                print_error(&e, filename.as_str(), result.as_str())?;
                had_error = true;
                break;
            }
        }
    }
    if had_error {
        process::exit(1);
    }

    // Resolve forward branch references
    analyzer.resolve_branch_fixups()?;

    // Build ELF object
    let mut obj =
        object::write::Object::new(BinaryFormat::Elf, Architecture::PowerPc, Endianness::Big);

    // Add file symbol if .file was encountered
    if let Some(ref file_name) = analyzer.file_name {
        obj.add_file_symbol(file_name.as_bytes().to_vec());
    }

    let mut section_map = HashMap::<CompactString, SectionId>::new();
    for section_key in &analyzer.section_order {
        let data = match analyzer.section_data.get(section_key) {
            Some(d) => d,
            None => continue,
        };
        // Extract the original section name (strip unique ID suffix after \0)
        let section_name = match section_key.find('\0') {
            Some(pos) => &section_key[..pos],
            None => section_key.as_str(),
        };
        if section_name == ".comm" {
            continue;
        }
        let info = analyzer
            .section_info
            .get(section_key)
            .unwrap_or(&SectionInfo { kind: object::SectionKind::Data, align: 4 });
        let kind = info.kind;
        let align = info.align;
        let id = obj.add_section(Vec::new(), section_name.as_bytes().to_vec(), kind);
        section_map.insert(section_key.clone(), id);
        let section = obj.section_mut(id);
        match kind {
            object::SectionKind::UninitializedData => {
                section.append_bss(data.len() as u64, align);
            }
            _ => {
                section.set_data(data.clone(), align);
            }
        }
    }

    // Add symbols (skip local labels like .L_xxx)
    let mut symbol_ids = HashMap::<CompactString, SymbolId>::new();
    for (name, defsym) in &analyzer.symbols {
        // Skip local labels - they don't appear in the output symbol table
        if name.starts_with(".L") && defsym.visibility == Visibility::Local {
            continue;
        }
        let sym_id = obj.add_symbol(object::write::Symbol {
            name: defsym.name.as_bytes().to_vec(),
            value: defsym.address.unwrap_or_default() as u64,
            size: defsym.size.unwrap_or_default() as u64,
            kind: match defsym.kind {
                None => object::SymbolKind::Label,
                Some(SymbolKind::Function) => object::SymbolKind::Text,
                Some(SymbolKind::Object) => object::SymbolKind::Data,
                Some(SymbolKind::Common) => object::SymbolKind::Data,
            },
            scope: match defsym.visibility {
                Visibility::Local => object::SymbolScope::Compilation,
                Visibility::Global | Visibility::Weak => object::SymbolScope::Dynamic,
                Visibility::Hidden => object::SymbolScope::Linkage,
            },
            weak: defsym.visibility == Visibility::Weak,
            section: match defsym.kind {
                Some(SymbolKind::Common) => object::write::SymbolSection::Common,
                _ => {
                    match defsym.section.as_ref().and_then(|name| section_map.get(name).cloned()) {
                        None => object::write::SymbolSection::Undefined,
                        Some(id) => object::write::SymbolSection::Section(id),
                    }
                }
            },
            flags: object::SymbolFlags::None,
        });
        symbol_ids.insert(name.clone(), sym_id);
    }

    // Sort relocations by offset for deterministic output
    analyzer.relocations.sort_by_key(|r| r.offset);

    // Add relocations
    for reloc in &analyzer.relocations {
        let section_id = match section_map.get(reloc.section.as_str()).cloned() {
            Some(id) => id,
            None => continue,
        };
        let symbol_id = match symbol_ids.get(&reloc.sym) {
            Some(&id) => id,
            None => {
                // External symbol - add as undefined (and cache it)
                let id = obj.add_symbol(object::write::Symbol {
                    name: reloc.sym.as_bytes().to_vec(),
                    value: 0,
                    size: 0,
                    kind: object::SymbolKind::Unknown,
                    scope: object::SymbolScope::Unknown,
                    weak: false,
                    section: object::write::SymbolSection::Undefined,
                    flags: object::SymbolFlags::None,
                });
                symbol_ids.insert(reloc.sym.clone(), id);
                id
            }
        };
        let r_type = match reloc.kind {
            RelocationKind::Absolute => R_PPC_ADDR32,
            RelocationKind::Sda21 => R_PPC_EMB_SDA21,
            RelocationKind::Ha => R_PPC_ADDR16_HA,
            RelocationKind::H => R_PPC_ADDR16_HI,
            RelocationKind::L => R_PPC_ADDR16_LO,
            RelocationKind::Rel24 => R_PPC_REL24,
            RelocationKind::Rel14 => R_PPC_REL14,
        };
        obj.add_relocation(section_id, object::write::Relocation {
            offset: reloc.offset as u64,
            symbol: symbol_id,
            addend: reloc.addend as i64,
            flags: RelocationFlags::Elf { r_type },
        })?;
    }

    obj.write_stream(BufWriter::new(File::create(&output_path)?))?;
    Ok(())
}

fn print_error(e: &ParseError, filename: &str, contents: &str) -> std::io::Result<()> {
    let begin = e.diagnostics.first().map(|d| d.source.range().start).unwrap_or_default();
    let mut report =
        Report::build(ReportKind::Error, filename, begin).with_message(e.message.clone());
    for (i, diag) in e.diagnostics.iter().enumerate() {
        report.add_label(
            Label::new((filename, diag.source.range()))
                .with_message(diag.message.clone())
                .with_color(diag.color)
                .with_order(i as i32),
        );
    }
    if let Some(ref note) = e.note {
        report = report.with_note(note.clone());
    }
    report.finish().print((filename, Source::from(contents)))
}
