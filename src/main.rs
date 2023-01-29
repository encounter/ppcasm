#![feature(test)]
extern crate core;
extern crate test;

use std::{
    collections::{hash_map::Entry, HashMap},
    error::Error,
    fmt::{Display, Formatter},
    fs,
    fs::File,
    io::{BufRead, BufReader, BufWriter, Read},
    mem::{discriminant, take},
    path::Path,
    str::Chars,
};

use ariadne::{Color, ColorGenerator, Fmt, Label, Report, ReportKind, Source};
use compact_str::CompactString;
use encoding_rs::SHIFT_JIS;
use object::{
    elf::{R_PPC_ADDR16_HA, R_PPC_ADDR16_LO, R_PPC_ADDR32, R_PPC_EMB_SDA21},
    write::{SectionId, SymbolId},
    Architecture, BinaryFormat, Endianness,
};
use parser::Parser;

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
    size: u8,
}

struct Analyzer {
    current_section: Option<CompactString>,
    section_offset: u32,
    replacements: HashMap<CompactString, Operand>,
    symbols: HashMap<CompactString, DefSym>,
    section_data: HashMap<CompactString, Vec<u8>>,
    relocations: Vec<Relocation>,
}

type AnalyzerResult<T> = Result<T, ParseError>;

enum ExpressionResult {
    Number(i64),
    Float(f32),
    Double(f64),
    // Symbol(CompactString),
    Relocation(CompactString, i32),
}

impl Analyzer {
    fn new() -> Self {
        let mut replacements = HashMap::<CompactString, Operand>::new();
        for i in 0..=31 {
            replacements.insert(format!("r{}", i).into(), Operand::Number(i, SourceInfo::new(0)));
            replacements.insert(format!("f{}", i).into(), Operand::Number(i, SourceInfo::new(0)));
        }
        for i in 0..=7 {
            replacements.insert(format!("qr{}", i).into(), Operand::Number(i, SourceInfo::new(0)));
        }
        Self {
            current_section: None,
            section_offset: 0,
            replacements,
            symbols: Default::default(),
            section_data: Default::default(),
            relocations: Default::default(),
        }
    }

    fn process(&mut self, stmt: Statement) -> AnalyzerResult<()> {
        match stmt {
            Statement::Label(sym, source) => self.label(sym, source),
            Statement::Instruction(sym, source, args) => {
                if sym.starts_with('.') {
                    match sym.as_str() {
                        ".include" => {
                            // TODO
                            Ok(())
                        }
                        ".section" => self.section(args, source),
                        ".4byte" => self.byte4(args, source),
                        ".2byte" => self.byte2(args, source),
                        ".byte" => self.byte(args, source),
                        ".balign" => self.balign(args, source),
                        ".global" => self.global(args, source),
                        ".float" => self.float(args, source),
                        ".double" => self.double(args, source),
                        ".lcomm" => self.lcomm(args, source),
                        ".comm" => self.comm(args, source),
                        ".skip" | ".space" => self.space(args, source),
                        ".asciz" => self.asciz(args, source),
                        _ => todo!("{}", sym),
                    }
                } else {
                    // TODO
                    // println!("Stub for {}", sym);
                    for arg in args {
                        match arg.arg {
                            Arg::Offset(base, offs) => {
                                let base_result = self.evaluate(base)?;
                                let offs_result = self.evaluate(offs)?;
                            }
                            Arg::Relocation(base, kind) => {
                                let base_result = self.evaluate(base)?;
                            }
                            Arg::RelocationWithOffset(base, kind, offs) => {
                                let base_result = self.evaluate(base)?;
                                let offs_result = self.evaluate(offs)?;
                            }
                            Arg::Expression(expr) => {
                                let result = self.evaluate(expr)?;
                            }
                        }
                    }
                    self.fill_data(4, 0)?;
                    Ok(())
                }
            }
        }
    }

    fn label(&mut self, sym: CompactString, source: SourceInfo) -> AnalyzerResult<()> {
        if let Some(defsym) = self.symbols.get_mut(&sym) {
            if defsym.address.is_some() {
                return Err(errors::symbol_redefinition(defsym, source));
            }
            // println!(
            //     "Updating {} to address {} (section {})",
            //     sym,
            //     self.section_offset,
            //     self.current_section.as_ref().unwrap()
            // );
            defsym.section = self.current_section.clone();
            defsym.address = Some(self.section_offset);
        } else {
            // println!(
            //     "Creating {} at address {} (section {})",
            //     sym,
            //     self.section_offset,
            //     self.current_section.as_ref().unwrap()
            // );
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

    fn section(&mut self, mut args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        let mut name = CompactString::default();
        let mut flags = CompactString::default();
        let mut kind = CompactString::default();
        for (idx, arg) in args.into_iter().enumerate() {
            match idx {
                0 => name = self.expect_symbol(arg)?,
                1 => flags = self.expect_string(arg)?,
                2 => kind = self.expect_constant(arg)?,
                _ => return Err(errors::extra_arg(".section", &arg)),
            }
        }
        // TODO use flags, type
        self.switch_section(name)?;
        Ok(())
    }

    fn byte4(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        if args.is_empty() {
            // Defaults to 0
            return self.write_data(&[0u8; 4]);
        }
        for value in args {
            match value.arg {
                Arg::Offset(expr, offs) => {
                    todo!()
                }
                Arg::Relocation(expr, kind) => {
                    todo!()
                }
                Arg::RelocationWithOffset(expr, kind, offs) => {
                    todo!()
                }
                Arg::Expression(expr) => {
                    let result = self.evaluate(expr)?;
                    match result {
                        ExpressionResult::Number(n) => {
                            self.write_data(&(n as u32).to_be_bytes())?;
                        }
                        ExpressionResult::Float(_) | ExpressionResult::Double(_) => {
                            return Err(ParseError {
                                message: format!("float value not permitted for .4byte"),
                                // TODO
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
                                size: 4,
                            });
                            self.write_data(&[0u8; 4])?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn byte2(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        // if args.is_empty() {
        //     // Defaults to 0
        //     return self.write_data(&[0u8; 2]);
        // }
        for value in args {
            match value.arg {
                Arg::Offset(expr, offs) => {
                    todo!()
                }
                Arg::Relocation(expr, kind) => {
                    todo!()
                }
                Arg::RelocationWithOffset(expr, kind, offs) => {
                    todo!()
                }
                Arg::Expression(expr) => {
                    let result = self.evaluate(expr)?;
                    match result {
                        ExpressionResult::Number(n) => {
                            self.write_data(&(n as u16).to_be_bytes())?;
                        }
                        ExpressionResult::Float(_) | ExpressionResult::Double(_) => {
                            return Err(ParseError {
                                message: format!("float value not permitted for .2byte"),
                                // TODO
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
                                size: 2,
                            });
                            self.write_data(&[0u8; 2])?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn byte(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        // if args.is_empty() {
        //     // Defaults to 0
        //     return self.write_data(&[0u8; 1]);
        // }
        for value in args {
            match value.arg {
                Arg::Offset(expr, offs) => {
                    todo!()
                }
                Arg::Relocation(expr, kind) => {
                    todo!()
                }
                Arg::RelocationWithOffset(expr, kind, offs) => {
                    todo!()
                }
                Arg::Expression(expr) => {
                    let result = self.evaluate(expr)?;
                    match result {
                        ExpressionResult::Number(n) => {
                            self.write_data(&(n as u8).to_be_bytes())?;
                        }
                        ExpressionResult::Float(_) | ExpressionResult::Double(_) => {
                            return Err(ParseError {
                                message: format!("float value not permitted for .byte"),
                                // TODO
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
                                size: 1,
                            });
                            self.write_data(&[0u8; 1])?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn float(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        for value in args {
            match value.arg {
                Arg::Expression(expr) => {
                    let result = self.evaluate(expr)?;
                    match result {
                        ExpressionResult::Number(n) => {
                            self.write_data(&(n as f32).to_be_bytes())?;
                        }
                        ExpressionResult::Float(n) => {
                            self.write_data(&n.to_be_bytes())?;
                        }
                        ExpressionResult::Double(n) => {
                            self.write_data(&(n as f32).to_be_bytes())?;
                        }
                        ExpressionResult::Relocation(_, _) => {
                            return Err(ParseError {
                                message: format!("expected float value"),
                                // TODO
                                diagnostics: vec![],
                                note: None,
                            });
                        }
                    }
                }
                _ => {
                    return Err(ParseError {
                        message: format!("expected float value"),
                        // TODO
                        diagnostics: vec![],
                        note: None,
                    });
                }
            }
        }
        Ok(())
    }

    fn double(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        for value in args {
            match value.arg {
                Arg::Expression(expr) => {
                    let result = self.evaluate(expr)?;
                    match result {
                        ExpressionResult::Number(n) => {
                            self.write_data(&(n as f64).to_be_bytes())?;
                        }
                        ExpressionResult::Float(n) => {
                            self.write_data(&(n as f64).to_be_bytes())?;
                        }
                        ExpressionResult::Double(n) => {
                            self.write_data(&n.to_be_bytes())?;
                        }
                        ExpressionResult::Relocation(_, _) => {
                            return Err(ParseError {
                                message: format!("expected double value"),
                                // TODO
                                diagnostics: vec![],
                                note: None,
                            });
                        }
                    }
                }
                _ => {
                    return Err(ParseError {
                        message: format!("expected double value"),
                        // TODO
                        diagnostics: vec![],
                        note: None,
                    });
                }
            }
        }
        Ok(())
    }

    fn asciz(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        for value in args {
            let str = self.expect_string(value)?;
            self.write_data(str.as_bytes())?;
            self.fill_data(1, 0)?;
        }
        Ok(())
    }

    fn balign(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        const USAGE: &str = "usage: .balign [align[, fill]]";
        let add_usage = |mut e: ParseError| {
            // e.note = Some(USAGE.into());
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
        let count = ((self.section_offset + align - 1) & !(align - 1)) - self.section_offset;
        if count > 0 {
            self.fill_data(count, fill)?;
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
        self.switch_section(".bss".into())?;
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
        let prev_section = self.current_section.clone();
        self.switch_section(".comm".into())?;
        match self.symbols.entry(sym.clone()) {
            Entry::Occupied(mut entry) => {
                let defsym = entry.get_mut();
                if defsym.address.is_some() {
                    return Err(errors::symbol_redefinition(defsym, source));
                }
                defsym.address = Some(self.section_offset);
                defsym.section = self.current_section.clone();
            }
            Entry::Vacant(entry) => {
                entry.insert(DefSym {
                    name: sym,
                    section: self.current_section.clone(),
                    address: Some(self.section_offset),
                    size: Some(size),
                    kind: None,
                    visibility: Visibility::Global,
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

    fn space(&mut self, args: StatementArgs, source: SourceInfo) -> AnalyzerResult<()> {
        let mut size = 0u32;
        let mut fill = 0u8;
        if args.len() < 1 {
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

    fn write_data(&mut self, bytes: &[u8]) -> AnalyzerResult<()> {
        let curr_section = self.current_section.clone().ok_or(ParseError {
            message: "[internal] write_data called without a section".into(),
            diagnostics: vec![],
            note: None,
        })?;
        // println!("Writing {} bytes to {}", bytes.len(), curr_section);
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
        // println!("Filling {} bytes in {}", count, curr_section);
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
                        BinaryOpKind::Nor => {
                            todo!()
                        }
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
                                // TODO
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
                            BinaryOpKind::Sub => {
                                Ok(ExpressionResult::Relocation(sym, (l - r as i64) as i32))
                            }
                            _ => Err(ParseError {
                                message: format!(
                                    "can't perform {:?} between relocation and number",
                                    kind,
                                ),
                                // TODO
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
                        // TODO
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
                            // TODO
                            diagnostics: vec![],
                            note: None,
                        }),
                    },
                    ExpressionResult::Double(n) => match kind {
                        UnaryOpKind::Pos => Ok(ExpressionResult::Double(n)),
                        UnaryOpKind::Neg => Ok(ExpressionResult::Double(-n)),
                        _ => Err(ParseError {
                            message: format!("can't perform {:?} on float", kind),
                            // TODO
                            diagnostics: vec![],
                            note: None,
                        }),
                    },
                    ExpressionResult::Relocation(_, _) => Err(ParseError {
                        message: format!("can't perform {:?} on relocation", kind),
                        // TODO
                        diagnostics: vec![],
                        note: None,
                    }),
                }
            }
            Expression::Operand(operand) => {
                match operand {
                    Operand::Number(n, source) => Ok(ExpressionResult::Number(n)),
                    Operand::Float(n, source) => Ok(ExpressionResult::Float(n)),
                    Operand::Double(n, source) => Ok(ExpressionResult::Double(n)),
                    Operand::Symbol(sym, source) => {
                        let sym = match sym {
                            Symbol::Regular(sym) => {
                                match sym.as_str() {
                                    "." => {
                                        return Ok(ExpressionResult::Number(
                                            self.section_offset as i64,
                                        ))
                                    }
                                    _ => {}
                                }
                                if let Some(replacement) = self.replacements.get(&sym) {
                                    return match replacement {
                                        Operand::Number(n, _) => Ok(ExpressionResult::Number(*n)),
                                        // TODO: just number??
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
                        if let Some(defsym) = self.symbols.get(&sym) {
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

    fn switch_section(&mut self, name: CompactString) -> AnalyzerResult<()> {
        self.section_offset =
            self.section_data.get(&name).map(|v| v.len() as u32).unwrap_or_default();
        // println!("Entering section {} (offset {:#X})", name, self.section_offset);
        self.current_section = Some(name);
        Ok(())
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let path = Path::new("/home/lstreet/Development/prime/asm/MetroidPrime/Player/CPlayerGun.s");
    let filename =
        path.file_name().map(|s| s.to_string_lossy().to_string()).unwrap_or("[unknown]".into());
    let result = fs::read_to_string(path)?;
    let mut parser = Parser::new(result.as_str());
    let mut analyzer = Analyzer::new();
    loop {
        let stmt = match parser.statement() {
            Ok(stmt) => stmt,
            Err(e) => {
                print_error(e, filename.as_str(), result.as_str())?;
                break;
            }
        };
        // println!("{:?}", stmt);
        match analyzer.process(stmt) {
            Ok(_) => {}
            Err(e) => {
                print_error(e, filename.as_str(), result.as_str())?;
                break;
            }
        }
    }

    let mut obj =
        object::write::Object::new(BinaryFormat::Elf, Architecture::PowerPc, Endianness::Big);
    let mut section_map = HashMap::<CompactString, SectionId>::new();
    for (section_name, data) in analyzer.section_data {
        let (kind, align) = match section_name.as_str() {
            ".text" => (object::SectionKind::Text, 4),
            ".data" => (object::SectionKind::Data, 8),
            ".rodata" => (object::SectionKind::ReadOnlyData, 8),
            ".sdata" => (object::SectionKind::Data, 8),
            ".sdata2" => (object::SectionKind::ReadOnlyData, 8),
            ".bss" => (object::SectionKind::UninitializedData, 8),
            ".sbss" => (object::SectionKind::UninitializedData, 8),
            ".sbss2" => (object::SectionKind::UninitializedData, 8),
            ".ctors" => (object::SectionKind::Data, 4),
            ".comm" => continue,
            _ => todo!("{}", section_name),
        };
        let id = obj.add_section(Vec::new(), section_name.as_bytes().to_vec(), kind);
        section_map.insert(section_name, id);
        let section = obj.section_mut(id);
        match kind {
            object::SectionKind::UninitializedData => {
                section.append_bss(data.len() as u64, align);
            }
            _ => {
                section.set_data(data, align);
            }
        }
    }
    for (_, defsym) in analyzer.symbols {
        obj.add_symbol(object::write::Symbol {
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
                Visibility::Global => object::SymbolScope::Compilation,
                Visibility::Weak => object::SymbolScope::Compilation,
            },
            weak: defsym.visibility == Visibility::Weak,
            section: match defsym.kind {
                Some(SymbolKind::Common) => object::write::SymbolSection::Common,
                _ => {
                    match defsym.section.and_then(|name| section_map.get(name.as_str()).cloned()) {
                        None => object::write::SymbolSection::Undefined,
                        Some(id) => object::write::SymbolSection::Section(id),
                    }
                }
            },
            flags: object::SymbolFlags::None,
        });
    }
    for reloc in analyzer.relocations {
        let section_id = match section_map.get(reloc.section.as_str()).cloned() {
            Some(id) => id,
            None => continue, // TODO warn
        };
        let symbol_id = match obj.symbol_id(reloc.sym.as_bytes()) {
            // TODO: why not hit?
            Some(id) => id,
            None => obj.add_symbol(object::write::Symbol {
                name: reloc.sym.as_bytes().to_vec(),
                value: 0,
                size: 0,
                kind: object::SymbolKind::Unknown,
                scope: object::SymbolScope::Unknown,
                weak: false,
                section: object::write::SymbolSection::Undefined,
                flags: object::SymbolFlags::None,
            }),
        };
        obj.add_relocation(section_id, object::write::Relocation {
            offset: reloc.offset as u64,
            size: reloc.size,
            kind: match reloc.kind {
                RelocationKind::Absolute => object::RelocationKind::Elf(R_PPC_ADDR32),
                RelocationKind::Sda21 => object::RelocationKind::Elf(R_PPC_EMB_SDA21),
                RelocationKind::Ha => object::RelocationKind::Elf(R_PPC_ADDR16_HA),
                RelocationKind::L => object::RelocationKind::Elf(R_PPC_ADDR16_LO),
            },
            encoding: object::RelocationEncoding::Generic,
            symbol: symbol_id,
            addend: reloc.addend as i64,
        })?;
        // println!("reloc: {:?}", reloc);
    }
    obj.write_stream(BufWriter::new(File::create("test.o")?))?;

    // for i in 0..100 {
    //     let mut parser = Parser::new(result.as_str());
    //     loop {
    //         let stmt = match parser.statement() {
    //             Ok(stmt) => stmt,
    //             Err(e) => {
    //                 // print_error(e, filename.as_str(), result.as_str())?;
    //                 break;
    //             }
    //         };
    //     }
    // }
    Ok(())
}

fn print_error(e: ParseError, filename: &str, contents: &str) -> std::io::Result<()> {
    let begin = e.diagnostics.first().map(|d| d.source.range().start).unwrap_or_default();
    let mut report = Report::build(ReportKind::Error, filename, begin).with_message(e.message);
    for (i, diag) in e.diagnostics.into_iter().enumerate() {
        report.add_label(
            Label::new((filename, diag.source.range()))
                .with_message(diag.message)
                .with_color(diag.color)
                .with_order(i as i32),
        );
    }
    if let Some(note) = e.note {
        report = report.with_note(note);
    }
    report.finish().print((filename, Source::from(contents)))
}

#[cfg(test)]
mod tests {
    use test::Bencher;

    use super::*;

    #[bench]
    fn bench_parse(b: &mut Bencher) {
        let path =
            Path::new("/home/lstreet/Development/prime/asm/MetroidPrime/Player/CPlayerGun.s");
        let result = fs::read_to_string(path).unwrap();
        b.iter(|| {
            let mut parser = Parser::new(result.as_str());
            loop {
                if parser.statement().is_err() {
                    break;
                }
            }
        });
    }
}
