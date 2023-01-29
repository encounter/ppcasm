use std::{
    error::Error,
    fmt::{Display, Formatter},
    ops::Range,
};

use ariadne::{Color, ColorGenerator, Fmt};

use crate::{
    parser::{Arg, ArgWithSource, Expression, Operand, StatementArgs, Symbol},
    DefSym, ExpressionResult,
};

#[derive(Debug, PartialEq, Copy, Clone)]
pub(crate) struct SourceInfo {
    pub(crate) begin: u64,
    pub(crate) end: u64,
}

impl SourceInfo {
    pub(crate) fn new(position: u64) -> Self { Self { begin: position, end: position } }

    pub(crate) fn new_range(begin: u64, end: u64) -> Self { Self { begin, end } }

    pub(crate) fn range(&self) -> Range<usize> { self.begin as usize..self.end as usize }
}

impl From<Range<u64>> for SourceInfo {
    fn from(range: Range<u64>) -> Self { Self::new_range(range.start, range.end) }
}

#[derive(Debug, PartialEq)]
pub(crate) struct ParseErrorDiagnostic {
    pub(crate) source: SourceInfo,
    pub(crate) message: String,
    pub(crate) color: Color,
}

#[derive(Debug, PartialEq)]
pub(crate) struct ParseError {
    pub(crate) message: String,
    pub(crate) diagnostics: Vec<ParseErrorDiagnostic>,
    pub(crate) note: Option<String>,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result { f.write_str(self.message.as_str()) }
}

impl Error for ParseError {}

pub(crate) type ParseResult<T> = Result<T, ParseError>;

pub(crate) fn symbol_redefinition(defsym: &DefSym, source: SourceInfo) -> ParseError {
    let mut colors = ColorGenerator::new();
    let a = colors.next();
    let b = colors.next();
    ParseError {
        message: format!("redefinition of symbol '{}'", defsym.name),
        diagnostics: vec![
            ParseErrorDiagnostic {
                source: defsym.source,
                message: format!("previously defined here"),
                color: a,
            },
            ParseErrorDiagnostic { source, message: format!("redefined here"), color: b },
        ],
        note: None,
    }
}

pub(crate) fn extra_arg(directive: &str, arg: &ArgWithSource) -> ParseError {
    let mut colors = ColorGenerator::new();
    let a = colors.next();
    ParseError {
        message: format!("extra argument in {}", directive),
        diagnostics: vec![ParseErrorDiagnostic {
            source: arg.source,
            message: "unexpected argument".into(),
            color: a,
        }],
        note: None,
    }
}

pub(crate) fn missing_arg(
    directive: &str,
    expected: u32,
    args: &StatementArgs,
    source: SourceInfo,
) -> ParseError {
    let last_source = match args.last() {
        Some(arg) => SourceInfo::new(arg.source.end),
        None => SourceInfo::new(source.end),
    };
    let mut colors = ColorGenerator::new();
    let a = colors.next();
    ParseError {
        message: format!("expected at least {} arguments for {}", expected, directive),
        diagnostics: vec![ParseErrorDiagnostic {
            source: last_source,
            message: "missing argument".into(),
            color: a,
        }],
        note: None,
    }
}

pub(crate) fn arg_expected(expected: &str, arg: &ArgWithSource) -> ParseError {
    let found = match arg.arg {
        Arg::Offset(_, _) => "offset",
        Arg::Relocation(_, _) | Arg::RelocationWithOffset(_, _, _) => "relocation",
        Arg::Expression(Expression::Operand(Operand::Number(_, _))) => "number",
        Arg::Expression(Expression::Operand(Operand::Float(_, _)))
        | Arg::Expression(Expression::Operand(Operand::Double(_, _))) => "float",
        Arg::Expression(Expression::Operand(Operand::Symbol(Symbol::Regular(_), _))) => "symbol",
        Arg::Expression(Expression::Operand(Operand::Symbol(Symbol::Quoted(_), _))) => "string",
        Arg::Expression(_) => "expression",
    };
    let mut colors = ColorGenerator::new();
    let a = colors.next();
    ParseError {
        message: format!("expected {}", expected),
        diagnostics: vec![ParseErrorDiagnostic {
            source: arg.source,
            message: format!("found {}", found.fg(a)),
            color: a,
        }],
        note: None,
    }
}

pub(crate) fn result_expected(
    expected: &str,
    result: &ExpressionResult,
    source: SourceInfo,
) -> ParseError {
    let found = match result {
        ExpressionResult::Number(_) => "number",
        ExpressionResult::Float(_) | ExpressionResult::Double(_) => "float",
        ExpressionResult::Relocation(_, _) => "relocation",
    };
    let mut colors = ColorGenerator::new();
    let a = colors.next();
    ParseError {
        message: format!("expected {}", expected),
        diagnostics: vec![ParseErrorDiagnostic {
            source,
            message: format!("evaluated to {}", found.fg(a)),
            color: a,
        }],
        note: None,
    }
}
