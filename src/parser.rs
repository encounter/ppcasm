use core::mem::take;
use std::{
    error::Error,
    fmt::{Display, Formatter},
    iter::Peekable,
    ops::Range,
    str::Chars,
};

use ariadne::{Color, ColorGenerator, Fmt};
use compact_str::CompactString;
use pratt::{Affix, Associativity, PrattParser, Precedence, Result as PrattResult};
use smallvec::SmallVec;
use crate::errors::{ParseError, ParseErrorDiagnostic, ParseResult, SourceInfo};

#[derive(Debug, PartialEq)]
pub(crate) enum Symbol {
    Regular(CompactString),
    Quoted(CompactString),
}

impl Symbol {
    pub(crate) fn string(&self) -> &CompactString {
        match self {
            Symbol::Regular(str) | Symbol::Quoted(str) => str,
        }
    }

    pub(crate) fn take_string(&mut self) -> CompactString {
        match self {
            Symbol::Regular(str) | Symbol::Quoted(str) => take(str),
        }
    }
}

#[derive(Debug, PartialEq)]
pub(crate) enum Operand {
    Number(i64, SourceInfo),
    Float(f32, SourceInfo),
    Double(f64, SourceInfo),
    Symbol(Symbol, SourceInfo),
    // TODO: remove?
    Expression(Box<Expression>),
}

#[derive(Debug, PartialEq)]
pub(crate) enum BinaryOpKind {
    // *
    Mul,
    // /
    Div,
    // %
    Rem,
    // <<
    Shl,
    // >>
    Shr,
    // |
    Or,
    // &
    And,
    // ^
    Xor,
    // !
    Nor,
    // +
    Add,
    // -
    Sub,
    // ==
    Eq,
    // != | <>
    Neq,
    // <
    Lt,
    // >
    Gt,
    // <=
    Le,
    // >=
    Ge,
    // &&
    LAnd,
    // ||
    LOr,
}

#[derive(Debug, PartialEq)]
pub(crate) enum UnaryOpKind {
    // + (no-op)
    Pos,
    // -
    Neg,
    // ~
    Comp,
}

#[derive(Debug, PartialEq)]
pub(crate) enum Expression {
    BinaryOp(Box<Expression>, BinaryOpKind, Box<Expression>),
    UnaryOp(UnaryOpKind, Box<Expression>),
    Operand(Operand),
}

#[derive(Debug)]
enum ExpressionToken {
    Prefix(UnaryOpKind),
    Infix(BinaryOpKind),
    Operand(Operand),
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum RelocationKind {
    Absolute,
    Sda21,
    Ha,
    L,
}

#[derive(Debug, PartialEq)]
pub(crate) enum Arg {
    Offset(Expression, Expression),
    Relocation(Expression, RelocationKind),
    RelocationWithOffset(Expression, RelocationKind, Expression),
    Expression(Expression),
}

impl Display for Arg {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Arg::Offset(_, _) => f.write_str("offset"),
            Arg::Relocation(_, _) => f.write_str("relocation"),
            Arg::RelocationWithOffset(_, _, _) => f.write_str("relocation with offset"),
            Arg::Expression(_) => f.write_str("expression"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub(crate) struct ArgWithSource {
    pub(crate) arg: Arg,
    pub(crate) source: SourceInfo,
}

pub(crate) type StatementArgs = SmallVec<[ArgWithSource; 3]>;

#[derive(Debug, PartialEq)]
pub(crate) enum Statement {
    Label(CompactString, SourceInfo),
    Instruction(CompactString, SourceInfo, StatementArgs),
}

pub(crate) struct Parser<'a> {
    inner: Peekable<Chars<'a>>,
    /// Peeked char for two-char lookahead
    /// (needed for block comment end)
    peek_char: Option<char>,
    position: u64,
}

/// Empty compact_str with max inline capacity
macro_rules! str {
    () => {
        ::compact_str::CompactString::with_capacity(::core::mem::size_of::<::std::string::String>())
    };
}

impl<'a> Parser<'a> {
    pub(crate) fn new(s: &'a str) -> Parser<'a> {
        Self { inner: s.chars().peekable(), peek_char: None, position: 0 }
    }

    fn next(&mut self) -> Option<char> {
        if let Some(c) = self.peek_char.take() {
            return Some(c);
        }
        let result = self.inner.next();
        if result.is_some() {
            self.position += 1;
        }
        result
    }

    fn peek(&mut self) -> Option<char> {
        if let Some(c) = self.peek_char {
            return Some(c);
        }
        self.inner.peek().cloned()
    }

    fn advance(&mut self) {
        if self.peek_char.is_some() {
            self.peek_char = None;
            return;
        }
        if self.inner.next().is_some() {
            self.position += 1;
        }
    }

    fn skip_line_comment(&mut self) {
        loop {
            match self.peek() {
                Some(c) if is_newline(c) => break,
                Some(_) => self.advance(),
                None => break,
            }
        }
    }

    fn skip_block_comment(&mut self) -> bool {
        match self.peek() {
            Some('*') => {
                self.advance();
                loop {
                    match self.peek() {
                        Some('*') => {
                            self.advance();
                            match self.peek() {
                                Some('/') => {
                                    self.advance();
                                    break;
                                }
                                Some(_) => self.advance(),
                                None => break,
                            }
                        }
                        Some(_) => self.advance(),
                        None => break,
                    }
                }
                true
            }
            _ => {
                self.peek_char = Some('/');
                false
            }
        }
    }

    fn skip(&mut self) {
        loop {
            match self.peek() {
                Some(c) if is_whitespace(c) => self.advance(),
                Some('#') => {
                    self.advance();
                    self.skip_line_comment();
                }
                Some('/') => {
                    self.advance();
                    if !self.skip_block_comment() {
                        break;
                    }
                }
                _ => break,
            }
        }
    }

    fn skip_newlines(&mut self) {
        loop {
            match self.peek() {
                Some(c) if is_whitespace(c) || is_newline(c) => self.advance(),
                Some('#') => {
                    self.advance();
                    self.skip_line_comment();
                }
                Some('/') => {
                    self.advance();
                    if !self.skip_block_comment() {
                        break;
                    }
                }
                _ => break,
            }
        }
    }

    fn symbol(&mut self) -> ParseResult<Symbol> {
        self.skip();
        let mut source = self.begin_source();
        let c = self.next().ok_or_else(|| {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            ParseError {
                message: "unexpected end of file".into(),
                diagnostics: vec![ParseErrorDiagnostic {
                    source,
                    message: format!("expected {}", "symbol".fg(a)),
                    color: a,
                }],
                note: None,
            }
        })?;
        let mut result = str!();
        if c == '"' {
            loop {
                match self.peek() {
                    Some('\\') => {
                        self.advance();
                        match self.peek() {
                            Some('b') => {
                                self.advance();
                                result.push('\x08');
                            }
                            Some('f') => {
                                self.advance();
                                result.push('\x0C');
                            }
                            Some('n') => {
                                self.advance();
                                result.push('\n');
                            }
                            Some('r') => {
                                self.advance();
                                result.push('\r');
                            }
                            Some('t') => {
                                self.advance();
                                result.push('\t');
                            }
                            Some('\\') => {
                                self.advance();
                                result.push('\\');
                            }
                            Some('"') => {
                                self.advance();
                                result.push('"');
                            }
                            Some('0') => todo!("octal"),
                            Some('x') => todo!("hex"),
                            Some(c) => {
                                let mut colors = ColorGenerator::new();
                                let a = colors.next();
                                return Err(ParseError {
                                    message: format!("unknown escape sequence '\\{}'", c),
                                    diagnostics: vec![ParseErrorDiagnostic {
                                        source: SourceInfo::new_range(
                                            self.position - 1,
                                            self.position + 1,
                                        ),
                                        message: format!(
                                            "unknown escape sequence {}",
                                            format!("\\{}", c).fg(a)
                                        ),
                                        color: a,
                                    }],
                                    note: None,
                                });
                            }
                            None => {
                                let mut colors = ColorGenerator::new();
                                let a = colors.next();
                                let b = colors.next();
                                return Err(ParseError {
                                    message: "unexpected end of file".into(),
                                    diagnostics: vec![
                                        ParseErrorDiagnostic {
                                            source: self.begin_source(),
                                            message: format!("expected {}", '\"'.fg(a)),
                                            color: a,
                                        },
                                        ParseErrorDiagnostic {
                                            source: SourceInfo::new_range(
                                                source.begin,
                                                source.begin + 1,
                                            ),
                                            message: format!("to match {}", '\"'.fg(b)),
                                            color: b,
                                        },
                                    ],
                                    note: None,
                                });
                            }
                        }
                    }
                    Some('"') => {
                        self.advance();
                        break;
                    }
                    Some(c) => {
                        self.advance();
                        result.push(c);
                    }
                    None => break,
                }
            }
            Ok(Symbol::Quoted(result))
        } else {
            if !is_symbol_start_char(c) {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                return Err(ParseError {
                    message: "expected symbol".into(),
                    diagnostics: vec![ParseErrorDiagnostic {
                        source,
                        message: format!("expected {}", "symbol".fg(a)),
                        color: a,
                    }],
                    note: None,
                });
            }
            result.push(c);
            loop {
                match self.peek() {
                    Some(c) if is_symbol_char(c) => {
                        self.advance();
                        result.push(c);
                    }
                    _ => break,
                }
            }
            Ok(Symbol::Regular(result))
        }
    }

    fn begin_source(&self) -> SourceInfo { SourceInfo::new(self.position) }

    fn end_source(&self, source: &mut SourceInfo) { source.end = self.position; }

    pub(crate) fn statement(&mut self) -> ParseResult<Statement> {
        self.skip_newlines();
        let mut source = self.begin_source();
        let mut symbol = self.symbol()?;
        self.end_source(&mut source);
        self.skip();
        match self.peek() {
            Some(':') => {
                self.advance();
                self.end_source(&mut source);
                Ok(Statement::Label(symbol.take_string(), source))
            }
            Some(c) if is_instruction_separator(c) => {
                self.advance();
                Ok(Statement::Instruction(symbol.take_string(), source, Default::default()))
            }
            Some(_) => {
                let mut args = StatementArgs::new();
                loop {
                    {
                        self.skip();
                        let mut source = self.begin_source();
                        let arg = self.arg()?;
                        self.end_source(&mut source);
                        args.push(ArgWithSource { arg, source });
                    }
                    self.skip();
                    match self.peek() {
                        Some(',') => self.advance(),
                        Some(c) if is_instruction_separator(c) => {
                            self.advance();
                            break;
                        }
                        Some(_) => {
                            return Err(ParseError {
                                message: "expected ',', ';' or new line".into(),
                                diagnostics: vec![ParseErrorDiagnostic {
                                    source,
                                    // TODO
                                    message: "expected separator".to_string(),
                                    color: Default::default(),
                                }],
                                note: Some("Arguments are separated with ','".to_string()),
                            });
                        }
                        None => break,
                    }
                }
                Ok(Statement::Instruction(symbol.take_string(), source, args))
            }
            None => Ok(Statement::Instruction(symbol.take_string(), source, Default::default())),
        }
    }

    fn arg(&mut self) -> ParseResult<Arg> {
        let expression = self.expression()?;
        self.skip();
        let arg = match self.peek() {
            Some('@') => {
                self.advance();
                let mut source = self.begin_source();
                let symbol = self.symbol()?;
                self.end_source(&mut source);
                let kind = match symbol.string().to_ascii_lowercase().as_str() {
                    "sda21" => RelocationKind::Sda21,
                    "ha" => RelocationKind::Ha,
                    "l" => RelocationKind::L,
                    _ => {
                        let mut colors = ColorGenerator::new();
                        let a = colors.next();
                        let b = colors.next();
                        return Err(ParseError {
                            message: format!("unknown relocation type '{}'", symbol.string()),
                            diagnostics: vec![ParseErrorDiagnostic {
                                source,
                                message: format!(
                                    "Unknown relocation type {}",
                                    symbol.string().fg(a)
                                ),
                                color: a,
                            }],
                            note: Some(format!(
                                "Supported relocation types: {}, {}, {}",
                                "ha".fg(b),
                                "l".fg(b),
                                "sda21".fg(b)
                            )),
                        });
                    }
                };
                Arg::Relocation(expression, kind)
            }
            _ => Arg::Expression(expression),
        };
        Ok(match self.peek() {
            Some('(') => {
                let mut source = self.begin_source();
                self.advance();
                let offset_expr = self.expression()?;
                match self.peek() {
                    Some(')') => {
                        self.advance();
                    }
                    _ => {
                        let mut colors = ColorGenerator::new();
                        let a = colors.next();
                        let b = colors.next();
                        return Err(ParseError {
                            message: "unclosed delimiter".into(),
                            diagnostics: vec![
                                ParseErrorDiagnostic {
                                    source: self.begin_source(),
                                    message: format!("expected {}", ')'.fg(a)),
                                    color: a,
                                },
                                ParseErrorDiagnostic {
                                    source: SourceInfo::new_range(source.begin, source.begin + 1),
                                    message: format!("to match {}", '('.fg(b)),
                                    color: b,
                                },
                            ],
                            note: None,
                        });
                    }
                }
                match arg {
                    Arg::Relocation(e, kind) => Arg::RelocationWithOffset(e, kind, offset_expr),
                    Arg::Expression(e) => Arg::Offset(e, offset_expr),
                    _ => unreachable!(),
                }
            }
            _ => arg,
        })
    }

    fn expression(&mut self) -> ParseResult<Expression> {
        self.skip();
        let mut stack = SmallVec::<[ExpressionToken; 3]>::new();
        let mut source = self.begin_source();
        loop {
            if let Some(op) = self.prefix_op() {
                stack.push(ExpressionToken::Prefix(op));
            }
            stack.push(ExpressionToken::Operand(self.operand()?));
            match self.infix_op() {
                Some(op) => stack.push(ExpressionToken::Infix(op)),
                None => break,
            }
        }
        self.end_source(&mut source);
        ExpressionParser.parse(stack.into_iter()).map_err(|e| {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            ParseError {
                message: format!("error processing expression: {}", e),
                diagnostics: vec![ParseErrorDiagnostic {
                    source,
                    // TODO
                    message: format!("expression"),
                    color: a,
                }],
                note: None,
            }
        })
    }

    fn operand(&mut self) -> ParseResult<Operand> {
        self.skip();
        let mut source = self.begin_source();
        match self.peek() {
            Some('(') => {
                let mut source = self.begin_source();
                self.advance();
                let expr = self.expression()?;
                self.skip();
                match self.peek() {
                    Some(')') => {
                        self.advance();
                        Ok(Operand::Expression(Box::new(expr)))
                    }
                    _ => {
                        let mut colors = ColorGenerator::new();
                        let a = colors.next();
                        let b = colors.next();
                        Err(ParseError {
                            message: "unclosed delimiter".into(),
                            diagnostics: vec![
                                ParseErrorDiagnostic {
                                    source: self.begin_source(),
                                    message: format!("expected {}", ')'.fg(a)),
                                    color: a,
                                },
                                ParseErrorDiagnostic {
                                    source: SourceInfo::new_range(source.begin, source.begin + 1),
                                    message: format!("to match {}", '('.fg(b)),
                                    color: b,
                                },
                            ],
                            note: None,
                        })
                    }
                }
            }
            Some('"') => {
                let sym = self.symbol()?;
                self.end_source(&mut source);
                Ok(Operand::Symbol(sym, source))
            }
            Some(c) => {
                if !is_symbol_start_char(c) {
                    let mut colors = ColorGenerator::new();
                    let a = colors.next();
                    return Err(ParseError {
                        message: "expected operand".into(),
                        diagnostics: vec![ParseErrorDiagnostic {
                            source: self.begin_source(),
                            message: format!("expected {}", "operand".fg(a)),
                            color: a,
                        }],
                        note: None,
                    });
                }
                self.advance();
                let mut result = str!();
                let mut radix = 10u32;
                if c == '0' {
                    match self.peek() {
                        Some('d' | 'D') => {
                            self.advance();
                            // TODO consume sign
                            radix = 0;
                        }
                        Some('f' | 'F') => {
                            self.advance();
                            // TODO consume sign
                            radix = 1;
                        }
                        Some('.') => {
                            self.advance();
                            result.push_str("0.");
                            radix = 0;
                        }
                        Some('x' | 'X') => {
                            self.advance();
                            radix = 16;
                        }
                        Some('b' | 'B') => {
                            self.advance();
                            radix = 2;
                        }
                        Some('0'..='7') => {
                            // TODO: error on >7?
                            radix = 8;
                        }
                        Some(c1) if is_symbol_char(c1) => {
                            self.advance();
                            result.push(c);
                            result.push(c1);
                        }
                        None | Some(_) => {
                            return Ok(Operand::Number(0, self.begin_source()));
                        }
                    }
                } else {
                    result.push(c);
                }
                loop {
                    match self.peek() {
                        Some(c) if is_symbol_char(c) => {
                            if radix == 10 && matches!(c, '.' | 'e' | 'E') {
                                radix = 0;
                            }
                            self.advance();
                            result.push(c);
                        }
                        _ => break,
                    }
                }
                self.end_source(&mut source);
                // TODO this sucks
                if radix == 0 {
                    if let Ok(v) = result.parse::<f64>() {
                        return Ok(Operand::Double(v, source));
                    }
                } else if radix == 1 {
                    if let Ok(v) = result.parse::<f32>() {
                        return Ok(Operand::Float(v, source));
                    }
                } else {
                    if let Ok(v) = i64::from_str_radix(result.as_str(), radix) {
                        return Ok(Operand::Number(v, source));
                    }
                }
                return Ok(Operand::Symbol(Symbol::Regular(result), source));
            }
            None => {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                Err(ParseError {
                    message: "unexpected end of file".into(),
                    diagnostics: vec![ParseErrorDiagnostic {
                        source: self.begin_source(),
                        message: format!("expected {}", "operand".fg(a)),
                        color: a,
                    }],
                    note: None,
                })
            }
        }
    }

    fn prefix_op(&mut self) -> Option<UnaryOpKind> {
        self.skip();
        match self.peek() {
            Some('+') => {
                self.advance();
                Some(UnaryOpKind::Pos)
            }
            Some('-') => {
                self.advance();
                Some(UnaryOpKind::Neg)
            }
            Some('~') => {
                self.advance();
                Some(UnaryOpKind::Comp)
            }
            _ => None,
        }
    }

    fn infix_op(&mut self) -> Option<BinaryOpKind> {
        self.skip();
        match self.peek() {
            Some('+') => {
                self.advance();
                Some(BinaryOpKind::Add)
            }
            Some('-') => {
                self.advance();
                Some(BinaryOpKind::Sub)
            }
            Some('*') => {
                self.advance();
                Some(BinaryOpKind::Mul)
            }
            Some('/') => {
                self.advance();
                Some(BinaryOpKind::Div)
            }
            Some('%') => {
                self.advance();
                Some(BinaryOpKind::Rem)
            }
            Some('<') => {
                self.advance();
                match self.peek() {
                    Some('<') => {
                        self.advance();
                        Some(BinaryOpKind::Shl)
                    }
                    Some('>') => {
                        self.advance();
                        Some(BinaryOpKind::Neq)
                    }
                    Some('=') => {
                        self.advance();
                        Some(BinaryOpKind::Le)
                    }
                    _ => Some(BinaryOpKind::Lt),
                }
            }
            Some('>') => {
                self.advance();
                match self.peek() {
                    Some('>') => {
                        self.advance();
                        Some(BinaryOpKind::Shr)
                    }
                    Some('=') => {
                        self.advance();
                        Some(BinaryOpKind::Ge)
                    }
                    _ => Some(BinaryOpKind::Gt),
                }
            }
            Some('|') => {
                self.advance();
                match self.peek() {
                    Some('|') => {
                        self.advance();
                        Some(BinaryOpKind::LOr)
                    }
                    _ => Some(BinaryOpKind::Or),
                }
            }
            Some('&') => {
                self.advance();
                match self.peek() {
                    Some('&') => {
                        self.advance();
                        Some(BinaryOpKind::LAnd)
                    }
                    _ => Some(BinaryOpKind::And),
                }
            }
            Some('^') => {
                self.advance();
                Some(BinaryOpKind::Xor)
            }
            Some('!') => {
                self.advance();
                match self.peek() {
                    Some('=') => {
                        self.advance();
                        Some(BinaryOpKind::Neq)
                    }
                    _ => Some(BinaryOpKind::Nor),
                }
            }
            Some('=') => {
                self.advance();
                match self.peek() {
                    Some('=') => {
                        self.advance();
                        Some(BinaryOpKind::Eq)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

#[inline]
fn is_whitespace(ch: char) -> bool { matches!(ch, ' ' | '\t') }

#[inline]
fn is_newline(ch: char) -> bool { matches!(ch, '\n' | '\r') }

#[inline]
fn is_instruction_separator(ch: char) -> bool { matches!(ch, ';' | '\n' | '\r') }

#[inline]
fn is_symbol_char(c: char) -> bool {
    matches!(c, '_' | '.' | '$') || c.is_alphanumeric()
    // matches!(c, '.' | '$') || unicode_ident::is_xid_continue(c)
}

#[inline]
fn is_symbol_start_char(c: char) -> bool {
    matches!(c, '_' | '.' | '$' | '@') || c.is_alphanumeric()
    // matches!(c, '.' | '$' | '@') || unicode_ident::is_xid_start(c)
}

struct ExpressionParser;

impl<I> PrattParser<I> for ExpressionParser
where I: Iterator<Item = ExpressionToken>
{
    type Error = pratt::NoError;
    type Input = ExpressionToken;
    type Output = Expression;

    // Query information about an operator (Affix, Precedence, Associativity)
    fn query(&mut self, token: &ExpressionToken) -> PrattResult<Affix> {
        Ok(match token {
            ExpressionToken::Infix(BinaryOpKind::LAnd)
            | ExpressionToken::Infix(BinaryOpKind::LOr) => {
                Affix::Infix(Precedence(0), Associativity::Left)
            }
            ExpressionToken::Infix(BinaryOpKind::Add)
            | ExpressionToken::Infix(BinaryOpKind::Sub)
            | ExpressionToken::Infix(BinaryOpKind::Eq)
            | ExpressionToken::Infix(BinaryOpKind::Neq)
            | ExpressionToken::Infix(BinaryOpKind::Lt)
            | ExpressionToken::Infix(BinaryOpKind::Gt)
            | ExpressionToken::Infix(BinaryOpKind::Le)
            | ExpressionToken::Infix(BinaryOpKind::Ge) => {
                Affix::Infix(Precedence(1), Associativity::Left)
            }
            ExpressionToken::Infix(BinaryOpKind::Or)
            | ExpressionToken::Infix(BinaryOpKind::And)
            | ExpressionToken::Infix(BinaryOpKind::Xor)
            | ExpressionToken::Infix(BinaryOpKind::Nor) => {
                Affix::Infix(Precedence(2), Associativity::Left)
            }
            ExpressionToken::Infix(BinaryOpKind::Mul)
            | ExpressionToken::Infix(BinaryOpKind::Div)
            | ExpressionToken::Infix(BinaryOpKind::Rem)
            | ExpressionToken::Infix(BinaryOpKind::Shl)
            | ExpressionToken::Infix(BinaryOpKind::Shr) => {
                Affix::Infix(Precedence(3), Associativity::Left)
            }
            ExpressionToken::Prefix(UnaryOpKind::Neg)
            | ExpressionToken::Prefix(UnaryOpKind::Comp)
            | ExpressionToken::Prefix(UnaryOpKind::Pos) => Affix::Prefix(Precedence(4)),
            ExpressionToken::Operand(_) => Affix::Nilfix,
        })
    }

    // Construct a primary expression, e.g. a number
    fn primary(&mut self, token: ExpressionToken) -> PrattResult<Expression> {
        Ok(match token {
            ExpressionToken::Operand(Operand::Expression(e)) => *e,
            ExpressionToken::Operand(arg) => Expression::Operand(arg),
            _ => unreachable!(),
        })
    }

    // Construct a binary infix expression, e.g. 1+1
    fn infix(
        &mut self,
        lhs: Expression,
        token: ExpressionToken,
        rhs: Expression,
    ) -> PrattResult<Expression> {
        Ok(Expression::BinaryOp(
            Box::new(lhs),
            match token {
                ExpressionToken::Infix(op) => op,
                _ => unreachable!(),
            },
            Box::new(rhs),
        ))
    }

    // Construct a unary prefix expression, e.g. ~1
    fn prefix(&mut self, token: ExpressionToken, rhs: Expression) -> PrattResult<Expression> {
        Ok(Expression::UnaryOp(
            match token {
                ExpressionToken::Prefix(op) => op,
                _ => unreachable!(),
            },
            Box::new(rhs),
        ))
    }

    // Construct a unary postfix expression, e.g. 1?
    fn postfix(&mut self, _lhs: Expression, _token: ExpressionToken) -> PrattResult<Expression> {
        unreachable!()
    }
}

#[cfg(test)]
mod tests {
    use smallvec::smallvec;

    use super::*;

    macro_rules! binary_op {
        ($lhs:expr, $kind:ident, $rhs:expr) => {
            Expression::BinaryOp(Box::new($lhs), BinaryOpKind::$kind, Box::new($rhs))
        };
    }

    macro_rules! unary_op {
        ($kind:ident, $rhs:expr) => {
            Expression::UnaryOp(UnaryOpKind::$kind, Box::new($rhs))
        };
    }

    macro_rules! operand {
        ($kind:ident, $value:expr, $range:expr) => {
            Expression::Operand(Operand::$kind(
                $value,
                SourceInfo::new_range($range.start, $range.end),
            ))
        };
    }

    macro_rules! arg {
        ($kind:ident, $value:expr, $range:expr) => {
            ArgWithSource {
                arg: Arg::$kind($value),
                source: SourceInfo::new_range($range.start, $range.end),
            }
        };
    }

    #[test]
    fn test_parser() {
        assert_eq!(
            Parser::new("test:").statement(),
            Ok(Statement::Label("test".into(), SourceInfo::new_range(0, 5)))
        );
        {
            let mut parser = Parser::new(".te$.st.\t:\".global\"test#ok\r\n.float 0.;bl\t\t2b");
            assert_eq!(
                parser.statement(),
                Ok(Statement::Label(".te$.st.".into(), SourceInfo::new_range(0, 10)))
            );
            assert_eq!(
                parser.statement(),
                Ok(Statement::Instruction(
                    ".global".into(),
                    SourceInfo::new_range(10, 19),
                    smallvec![arg!(
                        Expression,
                        operand!(Symbol, Symbol::Regular("test".into()), 19..23),
                        // TODO fix
                        19..26
                    )]
                ))
            );
            assert_eq!(
                parser.statement(),
                Ok(Statement::Instruction(
                    ".float".into(),
                    SourceInfo::new_range(28, 34),
                    smallvec![arg!(Expression, operand!(Double, 0.0, 35..37), 35..37)]
                ))
            );
            assert_eq!(
                parser.statement(),
                Ok(Statement::Instruction("bl".into(), SourceInfo::new_range(38, 40), smallvec![
                    arg!(
                        Expression,
                        operand!(Symbol, Symbol::Regular("2b".into()), 42..44),
                        42..44
                    )
                ]))
            );
        }
        // assert_eq!(
        //     Parser::new(".global \"__ct__Q214CMemoryCardSys13CCardFileInfoFQ214CMemoryCardSys15EMemoryCardPortRCQ24rstl66basic_string<c,Q24rstl14char_traits<c>,Q24rstl17rmemory_allocator>\"").statement(),
        //     Ok(Statement::Instruction(".global".into(), smallvec![Arg::Expression(operand!(
        //         Symbol,
        //         Symbol::Quoted("__ct__Q214CMemoryCardSys13CCardFileInfoFQ214CMemoryCardSys15EMemoryCardPortRCQ24rstl66basic_string<c,Q24rstl14char_traits<c>,Q24rstl17rmemory_allocator>".into())
        //     ))]))
        // );
        // assert_eq!(
        //     Parser::new("\t.4byte/*block*/(1+2*/*comment*/3-4)+1#test").statement(),
        //     Ok(Statement::Instruction(".4byte".into(), smallvec![Arg::Expression(binary_op!(
        //         binary_op!(
        //             binary_op!(
        //                 operand!(Number, 1),
        //                 Add,
        //                 binary_op!(operand!(Number, 2), Mul, operand!(Number, 3))
        //             ),
        //             Sub,
        //             operand!(Number, 4)
        //         ),
        //         Add,
        //         operand!(Number, 1)
        //     ))]))
        // );
        // assert_eq!(
        //     Parser::new("\t.byte 0x3F, 0x3F, 0x28").statement(),
        //     Ok(Statement::Instruction(".byte".into(), smallvec![
        //         Arg::Expression(operand!(Number, 0x3F)),
        //         Arg::Expression(operand!(Number, 0x3F)),
        //         Arg::Expression(operand!(Number, 0x28)),
        //     ]))
        // );
        // assert_eq!(
        //     Parser::new("lis r4, sZeroVector__9CVector3f@ha").statement(),
        //     Ok(Statement::Instruction("lis".into(), smallvec![
        //         Arg::Expression(operand!(Symbol, Symbol::Regular("r4".into()))),
        //         Arg::Relocation(
        //             operand!(Symbol, Symbol::Regular("sZeroVector__9CVector3f".into())),
        //             RelocationKind::Ha
        //         ),
        //     ]))
        // );
        // assert_eq!(
        //     Parser::new("stfs f2, 0x14(r1)").statement(),
        //     Ok(Statement::Instruction("stfs".into(), smallvec![
        //         Arg::Expression(operand!(Symbol, Symbol::Regular("f2".into()))),
        //         Arg::Offset(operand!(Number, 0x14), operand!(Symbol, Symbol::Regular("r1".into()))),
        //     ]))
        // );
        // assert_eq!(
        //     Parser::new("stwu r1, -0x50(r1)").statement(),
        //     Ok(Statement::Instruction("stwu".into(), smallvec![
        //         Arg::Expression(operand!(Symbol, Symbol::Regular("r1".into()))),
        //         Arg::Offset(
        //             unary_op!(Neg, operand!(Number, 0x50)),
        //             operand!(Symbol, Symbol::Regular("r1".into()))
        //         ),
        //     ]))
        // );
        // assert_eq!(
        //     Parser::new(".4byte (.-+sym)/4").statement(),
        //     Ok(Statement::Instruction(".4byte".into(), smallvec![Arg::Expression(binary_op!(
        //         binary_op!(
        //             operand!(Symbol, Symbol::Regular(".".into())),
        //             Sub,
        //             unary_op!(Pos, operand!(Symbol, Symbol::Regular("sym".into())))
        //         ),
        //         Div,
        //         operand!(Number, 4)
        //     ))]))
        // );
        // assert_eq!(
        //     Parser::new("lwz r5, \"bound_48KHz\"+4@sda21(r13)").statement(),
        //     Ok(Statement::Instruction("lwz".into(), smallvec![
        //         Arg::Expression(operand!(Symbol, Symbol::Regular("r5".into()))),
        //         Arg::RelocationWithOffset(
        //             binary_op!(
        //                 operand!(Symbol, Symbol::Quoted("bound_48KHz".into())),
        //                 Add,
        //                 operand!(Number, 4)
        //             ),
        //             RelocationKind::Sda21,
        //             operand!(Symbol, Symbol::Regular("r13".into()))
        //         ),
        //     ]))
        // );
        // assert_eq!(
        //     Parser::new(".size \"test\\t\", .-\"test\\t\\\"ok\\\"\"").statement(),
        //     Ok(Statement::Instruction(".size".into(), smallvec![
        //         Arg::Expression(operand!(Symbol, Symbol::Quoted("test\t".into()))),
        //         Arg::Expression(binary_op!(
        //             operand!(Symbol, Symbol::Regular(".".into())),
        //             Sub,
        //             operand!(Symbol, Symbol::Quoted("test\t\"ok\"".into()))
        //         )),
        //     ]))
        // );
        // assert_eq!(
        //     Parser::new(".if version >= 1").statement(),
        //     Ok(Statement::Instruction(".if".into(), smallvec![Arg::Expression(binary_op!(
        //         operand!(Symbol, Symbol::Regular("version".into())),
        //         Ge,
        //         operand!(Number, 1)
        //     ))]))
        // );
        // assert_eq!(
        //     Parser::new(".section .sbss2, \"\", @nobits").statement(),
        //     Ok(Statement::Instruction(".section".into(), smallvec![
        //         Arg::Expression(operand!(Symbol, Symbol::Regular(".sbss2".into()))),
        //         Arg::Expression(operand!(Symbol, Symbol::Quoted("".into()))),
        //         Arg::Expression(operand!(Symbol, Symbol::Regular("@nobits".into()))),
        //     ]))
        // );
    }
}
