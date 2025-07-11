use std::{
    collections::HashMap,
    fmt, fs,
    path::{Path, PathBuf},
};

use crate::lexer::{Lexer, Span, Token, TokenKind};

#[derive(Debug, Clone)]
pub struct Program {
    pub defs: HashMap<Box<str>, (PathBuf, Def)>,
    pub includes: Vec<(PathBuf, Span)>,
}

impl Program {
    pub fn flatten_includes(
        self,
        path: PathBuf,
        dir: &Path,
        opened_files: &mut Vec<PathBuf>,
    ) -> Result<HashMap<Box<str>, (PathBuf, Def)>, (PathBuf, SyntaxError)> {
        let mut new_defs = self.defs;
        for (include, loc) in self.includes {
            if !opened_files.contains(&include) {
                let include_path = dir.join(&include);
                let Ok(src) = fs::read_to_string(&include_path) else {
                    return Err((path, SyntaxError::CouldntFindInclude(include, loc)));
                };
                let absolute = include_path
                    .canonicalize()
                    .unwrap_or_else(|_| panic!("couldn't find absolute path"));
                opened_files.push(absolute.clone());
                let program = Parser::new(include.clone(), &src)
                    .program()
                    .map_err(|e| (include.clone(), e))?;
                let defs = program.flatten_includes(
                    absolute.clone(),
                    absolute.parent().unwrap_or(Path::new("/")),
                    opened_files,
                )?;
                for (name, def) in defs {
                    if !new_defs.contains_key(&name) {
                        new_defs.insert(name, def);
                    }
                }
            }
        }
        Ok(new_defs)
    }
}

#[derive(Debug, Clone)]
pub struct Def {
    pub name: Box<str>,
    pub branches: Vec<(Case, Expr)>,
}

#[derive(Debug, Clone)]
pub struct Case {
    pub pat: Pattern,
    pub guard: Option<Expr>,
}

impl Case {
    pub fn parts(self) -> (Pattern, Option<Expr>) {
        (self.pat, self.guard)
    }
}

#[derive(Debug, Clone)]
pub enum PatternKind {
    Wildcard,
    Unit,
    Void,
    Number(f64),
    Named(Box<str>),
    String(Box<str>),
    Cons(Box<Pattern>, Box<Pattern>),
    Grouped(Box<Pattern>),
    Object { obj: Box<[Pattern]>, spread: Spread },
}

#[derive(Debug, Clone)]
pub enum Spread {
    Wild,
    Ident(Box<str>),
    None,
}

#[derive(Debug, Clone)]
pub struct Pattern {
    kind: PatternKind,
    span: Span,
}

impl Pattern {
    fn new(kind: PatternKind, span: Span) -> Self {
        Self { span, kind }
    }

    pub fn parts(self) -> (PatternKind, Span) {
        (self.kind, self.span)
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Unit,
    Void,
    Number(f64),
    Named(Box<str>),
    String(Box<str>),
    Grouped(Box<Expr>),
    Object(Box<[Expr]>),
    Binary {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        op: Op,
        op_span: Span,
    },
    Let {
        pattern: Pattern,
        body: Box<Expr>,
        next: Box<Expr>,
    },
}

#[derive(Debug, Clone)]
pub struct Expr {
    kind: ExprKind,
    span: Span,
}

impl Expr {
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn parts(self) -> (ExprKind, Span) {
        (self.kind, self.span)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Op {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,

    Concat,

    Greater,
    Less,
    Equal,

    Bang,
    Cons,
    PipeInto,
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Op::Add => "`+`",
                Op::Subtract => "`-`",
                Op::Multiply => "`*`",
                Op::Divide => "`/`",
                Op::Modulo => "`%`",

                Op::Concat => "`++`",

                Op::Greater => "`>`",
                Op::Less => "`<`",
                Op::Equal => "`=`",

                Op::Cons => "`,`",
                Op::Bang => "`!`",
                Op::PipeInto => "`|>`",
            }
        )
    }
}

#[derive(Debug, Clone)]
pub enum SyntaxError {
    Expected { expected: TokenKind, found: Token },
    Unexpected(Token),
    CouldntFindInclude(PathBuf, Span),
}

fn escape(s: &str) -> String {
    let mut res = String::new();
    let mut chars = s[1..].chars();
    while let Some(c) = chars.next() {
        match c {
            '"' => break,
            '\\' => {
                if let Some(c) = chars.next() {
                    res.push(match c {
                        'n' => '\n',
                        't' => '\t',
                        'r' => '\r',
                        '"' => '"',
                        '\\' => '\\',
                        _ => continue,
                    })
                }
            }
            _ => res.push(c),
        }
    }
    res
}

pub struct Parser<'src> {
    path: PathBuf,
    lexer: Lexer<'src>,
}

impl<'src> Parser<'src> {
    pub fn new(path: PathBuf, src: &'src str) -> Self {
        Self {
            path,
            lexer: Lexer::new(src),
        }
    }

    fn expect(&mut self, tk: TokenKind) -> Result<Token, SyntaxError> {
        let token = self.lexer.token();
        if token.kind() == tk {
            Ok(token)
        } else {
            Err(SyntaxError::Expected {
                expected: tk,
                found: token,
            })
        }
    }

    pub fn program(&mut self) -> Result<Program, SyntaxError> {
        let mut defs = HashMap::new();
        let mut includes = Vec::new();
        while self.lexer.peek_token().kind() != TokenKind::Eof {
            if let TokenKind::Include = self.lexer.peek_token().kind() {
                self.lexer.token();
                let filename = self.expect(TokenKind::String)?;
                let span = filename.span();
                let filename = escape(self.lexer.slice(filename));
                includes.push((filename.into(), span));
            } else {
                let def = self.def()?;
                defs.insert(def.name.clone(), (self.path.clone(), def));
            }
        }
        Ok(Program { defs, includes })
    }

    fn def(&mut self) -> Result<Def, SyntaxError> {
        let ident = self.expect(TokenKind::Identifier)?;
        let name = self.lexer.slice(ident);
        self.expect(TokenKind::Colon)?;
        let mut branches = Vec::new();
        branches.push(self.branch()?);
        while self.lexer.peek_token().kind() != TokenKind::Semicolon {
            branches.push(self.branch()?);
        }
        self.expect(TokenKind::Semicolon)?;
        Ok(Def {
            name: name.into(),
            branches,
        })
    }

    fn branch(&mut self) -> Result<(Case, Expr), SyntaxError> {
        let case = self.case()?;
        self.expect(TokenKind::Arrow)?;
        let expr = self.expr()?;
        Ok((case, expr))
    }

    fn case(&mut self) -> Result<Case, SyntaxError> {
        let pat = self.pattern()?;
        if let TokenKind::Pipe = self.lexer.peek_token().kind() {
            self.lexer.token();
            let guard = self.expr()?;
            Ok(Case {
                pat,
                guard: Some(guard),
            })
        } else {
            Ok(Case { pat, guard: None })
        }
    }

    fn pattern(&mut self) -> Result<Pattern, SyntaxError> {
        let lhs = self.primary_pattern()?;
        Ok(if let TokenKind::Comma = self.lexer.peek_token().kind() {
            self.lexer.token();
            let rhs = self.pattern()?;
            let span = Span::new(lhs.span.start(), rhs.span.end());
            Pattern::new(PatternKind::Cons(Box::new(lhs), Box::new(rhs)), span)
        } else {
            lhs
        })
    }

    fn primary_pattern(&mut self) -> Result<Pattern, SyntaxError> {
        let token = self.lexer.token();
        Ok(match token.kind() {
            TokenKind::Number => Pattern::new(
                PatternKind::Number(self.lexer.slice(token).parse().unwrap()),
                token.span(),
            ),
            TokenKind::String => Pattern::new(
                PatternKind::String(escape(self.lexer.slice(token)).into_boxed_str()),
                token.span(),
            ),
            TokenKind::Wildcard => Pattern::new(PatternKind::Wildcard, token.span()),
            TokenKind::Identifier => Pattern::new(
                PatternKind::Named(self.lexer.slice(token).into()),
                token.span(),
            ),
            TokenKind::At => Pattern::new(PatternKind::Unit, token.span()),
            TokenKind::Question => Pattern::new(PatternKind::Void, token.span()),
            TokenKind::LeftParen => {
                let pattern = self.pattern()?;
                let rparen = self.expect(TokenKind::RightParen)?;
                Pattern::new(
                    PatternKind::Grouped(Box::new(pattern)),
                    Span::new(token.span().start(), rparen.span().end()),
                )
            }
            TokenKind::LeftBrace => {
                let mut patterns = Vec::new();
                let mut spread = Spread::None;
                while self.lexer.peek_token().kind() != TokenKind::RightBrace {
                    if self.lexer.peek_token().kind() == TokenKind::Colon {
                        self.lexer.token();
                        spread = if self.lexer.peek_token().kind() == TokenKind::Identifier {
                            let tok = self.lexer.token();
                            Spread::Ident(self.lexer.slice(tok).into())
                        } else {
                            Spread::Wild
                        };
                        break;
                    }
                    patterns.push(self.pattern()?);
                }
                let end = self.expect(TokenKind::RightBrace)?.span().end();
                Pattern::new(
                    PatternKind::Object {
                        obj: patterns.into_boxed_slice(),
                        spread,
                    },
                    Span::new(token.span().start(), end),
                )
            }
            _ => return Err(SyntaxError::Unexpected(token)),
        })
    }

    fn expr(&mut self) -> Result<Expr, SyntaxError> {
        if let TokenKind::Let = self.lexer.peek_token().kind() {
            let (start, _) = self.lexer.token().span().parts();
            let pattern = self.pattern()?;
            self.expect(TokenKind::BackArrow)?;
            let body = self.expr()?;
            let next = self.expr()?;
            let end = next.span.end();
            Ok(Expr::new(
                ExprKind::Let {
                    pattern,
                    body: Box::new(body),
                    next: Box::new(next),
                },
                Span::new(start, end),
            ))
        } else {
            self.bang_expr()
        }
    }

    /*



    */

    fn bang_expr(&mut self) -> Result<Expr, SyntaxError> {
        let mut lhs = self.cons_expr()?;
        while let TokenKind::Bang = self.lexer.peek_token().kind() {
            let op = self.lexer.token();
            let rhs = self.cons_expr()?;
            let span = Span::new(lhs.span.start(), rhs.span.end());
            lhs = Expr::new(
                ExprKind::Binary {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    op: Op::Bang,
                    op_span: op.span(),
                },
                span,
            );
        }
        Ok(lhs)
    }

    fn cons_expr(&mut self) -> Result<Expr, SyntaxError> {
        let lhs = self.compare_expr()?;
        Ok(if let TokenKind::Comma = self.lexer.peek_token().kind() {
            let op = self.lexer.token();
            let rhs = self.cons_expr()?;
            let span = Span::new(lhs.span.start(), rhs.span.end());
            Expr::new(
                ExprKind::Binary {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    op: Op::Cons,
                    op_span: op.span(),
                },
                span,
            )
        } else {
            lhs
        })
    }

    fn compare_expr(&mut self) -> Result<Expr, SyntaxError> {
        let mut lhs = self.additive_expr()?;
        while let TokenKind::Greater | TokenKind::Less | TokenKind::Equal =
            self.lexer.peek_token().kind()
        {
            let op = self.lexer.token();
            let op_op = match op.kind() {
                TokenKind::Greater => Op::Greater,
                TokenKind::Less => Op::Less,
                TokenKind::Equal => Op::Equal,
                _ => unreachable!(),
            };
            let rhs = self.additive_expr()?;
            let span = Span::new(lhs.span.start(), rhs.span.end());
            lhs = Expr::new(
                ExprKind::Binary {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    op: op_op,
                    op_span: op.span(),
                },
                span,
            );
        }

        Ok(lhs)
    }

    fn additive_expr(&mut self) -> Result<Expr, SyntaxError> {
        let mut lhs = self.term()?;
        while let TokenKind::Plus | TokenKind::Minus | TokenKind::PlusPlus =
            self.lexer.peek_token().kind()
        {
            let op = self.lexer.token();
            let op_op = match op.kind() {
                TokenKind::Plus => Op::Add,
                TokenKind::Minus => Op::Subtract,
                TokenKind::PlusPlus => Op::Concat,
                _ => unreachable!(),
            };
            let rhs = self.term()?;
            let span = Span::new(lhs.span.start(), rhs.span.end());
            lhs = Expr::new(
                ExprKind::Binary {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    op: op_op,
                    op_span: op.span(),
                },
                span,
            );
        }

        Ok(lhs)
    }

    fn term(&mut self) -> Result<Expr, SyntaxError> {
        let mut lhs = self.apply_expr()?;
        while let TokenKind::Star | TokenKind::Slash | TokenKind::Percent =
            self.lexer.peek_token().kind()
        {
            let op = self.lexer.token();
            let op_op = match op.kind() {
                TokenKind::Star => Op::Multiply,
                TokenKind::Slash => Op::Divide,
                TokenKind::Percent => Op::Modulo,
                _ => unreachable!(),
            };
            let rhs = self.apply_expr()?;
            let span = Span::new(lhs.span.start(), rhs.span.end());
            lhs = Expr::new(
                ExprKind::Binary {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    op: op_op,
                    op_span: op.span(),
                },
                span,
            );
        }

        Ok(lhs)
    }

    fn apply_expr(&mut self) -> Result<Expr, SyntaxError> {
        let mut lhs = self.primary()?;
        while let TokenKind::PipeInto = self.lexer.peek_token().kind() {
            let op = self.lexer.token();
            let rhs = self.primary()?;
            let span = Span::new(lhs.span.start(), rhs.span.end());
            lhs = Expr::new(
                ExprKind::Binary {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    op: Op::PipeInto,
                    op_span: op.span(),
                },
                span,
            );
        }
        Ok(lhs)
    }

    fn primary(&mut self) -> Result<Expr, SyntaxError> {
        let token = self.lexer.token();
        Ok(match token.kind() {
            TokenKind::String => Expr::new(
                ExprKind::String({
                    let s = self.lexer.slice(token);
                    escape(&s).into_boxed_str()
                }),
                token.span(),
            ),
            TokenKind::Number => Expr::new(
                ExprKind::Number(self.lexer.slice(token).parse().unwrap()),
                token.span(),
            ),
            TokenKind::At => Expr::new(ExprKind::Unit, token.span()),
            TokenKind::Question => Expr::new(ExprKind::Void, token.span()),
            TokenKind::Identifier => Expr::new(
                ExprKind::Named(self.lexer.slice(token).into()),
                token.span(),
            ),
            TokenKind::LeftParen => {
                let expr = self.expr()?;
                let rparen = self.expect(TokenKind::RightParen)?;
                Expr::new(
                    ExprKind::Grouped(Box::new(expr)),
                    Span::new(token.span().start(), rparen.span().end()),
                )
            }
            TokenKind::LeftBrace => {
                let mut exprs = Vec::new();
                while self.lexer.peek_token().kind() != TokenKind::RightBrace {
                    exprs.push(self.expr()?);
                }
                let (_, end) = self.expect(TokenKind::RightBrace)?.span().parts();
                Expr::new(
                    ExprKind::Object(exprs.into_boxed_slice()),
                    Span::new(token.span().start(), end),
                )
            }
            _ => return Err(SyntaxError::Unexpected(token)),
        })
    }
}
