use crate::{
    lexer::Span,
    parser::{Case, Def, Expr, ExprKind, Op, Pattern, PatternKind, Spread},
};
use std::{
    collections::HashMap,
    fmt,
    io::{self, Read, Write},
    path::{Path, PathBuf},
    rc::Rc,
};

#[derive(Clone)]
pub enum Value {
    Unit,
    Void,
    Number(f64),
    String(Box<str>),
    Object(Box<[Value]>),
    Native(Box<str>),
    Function(Box<str>),
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        if value { Value::Unit } else { Value::Void }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Number(lhs), Value::Number(rhs)) => lhs == rhs,
            (Value::String(lhs), Value::String(rhs)) => lhs == rhs,
            (Value::Unit, Value::Unit) => true,
            (Value::Void, Value::Void) => true,
            (Value::Object(lhs), Value::Object(rhs)) => lhs == rhs,
            _ => false,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Number(n) => write!(f, "{n}"),
            Value::String(s) => write!(f, "{s}"),
            Value::Unit => write!(f, "@"),
            Value::Void => write!(f, "?"),
            Value::Object(o) => write!(
                f,
                "{{{}}}",
                o.iter()
                    .map(|v| v.to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            Value::Native(_) => write!(f, "<fn>"),
            Value::Function(d) => write!(f, "<fn:{}>", d),
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::String(s) => write!(f, "{s:?}"),
            Value::Object(o) => write!(
                f,
                "{{{}}}",
                o.iter()
                    .map(|v| format!("{v:?}"))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            _ => write!(f, "{self}"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum RuntimeErrorKind {
    UndefinedBinding(Box<str>),
    DoesntSupportTypes {
        lhs: Value,
        rhs: Value,
        op: Op,
        op_span: Span,
    },
    UnmatchedValue {
        value: Value,
        func: Box<str>,
    },
    UnmatchedLet {
        value: Value,
    },
    Explicit(Box<str>),
}

#[derive(Debug, Clone)]
pub struct RuntimeError {
    kind: RuntimeErrorKind,
    span: Span,
    path: PathBuf,
}

impl RuntimeError {
    fn new(path: PathBuf, kind: RuntimeErrorKind, span: Span) -> Self {
        Self { path, kind, span }
    }
}

fn get_line_col(source: &str, index: usize) -> (usize, usize) {
    source
        .chars()
        .take(index)
        .fold((1, 1), |(line, column), ch| match ch {
            '\n' => (line + 1, 1),
            _ => (line, column + 1),
        })
}

pub fn report_error(err: RuntimeError, out: &mut impl Write) -> io::Result<()> {
    let mut span = err.span;
    let (reason, note) = match err.kind {
        RuntimeErrorKind::Explicit(s) => (s, Some("explicit error".into())),
        RuntimeErrorKind::UndefinedBinding(n) => (format!("undefined binding: {n}").into(), None),
        RuntimeErrorKind::UnmatchedValue { value, func } => (
            format!("unmatched value for function `{func}`").into(),
            Some(format!("the value: {value:?}").into()),
        ),
        RuntimeErrorKind::DoesntSupportTypes {
            lhs,
            rhs,
            op,
            op_span,
        } => {
            span = op_span;
            (
                format!("operation {op} is not supported").into(),
                Some(format!("left hand side: {lhs:?}\nright hand side: {rhs:?}").into_boxed_str()),
            )
        }
        RuntimeErrorKind::UnmatchedLet { value } => (
            "unmatched value for `let` binding".into(),
            Some(format!("the value: {value:?}").into()),
        ),
    };

    let src = std::fs::read_to_string(&err.path).unwrap();
    let (start, end) = span.parts();
    let (ln, col) = get_line_col(&src, start);
    let source_ln = src.lines().nth(ln - 1).unwrap_or_default();

    writeln!(out, "ERROR: {reason}")?;
    writeln!(out, " --> {}:{ln}:{col}", err.path.display())?;
    writeln!(out, "  {source_ln}")?;
    writeln!(out, "  {}{}", " ".repeat(col - 1), "^".repeat(end - start))?;

    if let Some(note) = note {
        for note_ln in note.lines() {
            if note_ln.is_empty() {
                writeln!(out)?;
            } else {
                writeln!(out, "NOTE: {note_ln}")?;
            }
        }
    }

    Ok(())
}

type Builtins = HashMap<Box<str>, Rc<dyn Fn(Value) -> Result<Value, RuntimeErrorKind>>>;

#[derive(Clone)]
pub struct Interpreter {
    funcs: HashMap<Box<str>, (PathBuf, Vec<(Case, Expr)>)>,
    builtins: Builtins,
}

impl Default for Interpreter {
    fn default() -> Self {
        let mut builtins: Builtins = HashMap::new();
        builtins.insert(
            ".print".into(),
            Rc::new(|v| {
                use std::io::Write;
                let mut stdout = std::io::stdout();
                print!("{v}");
                stdout.flush().unwrap();
                Ok(Value::Void)
            }),
        );
        builtins.insert(
            ".read_line".into(),
            Rc::new(|_| {
                let stdin = std::io::stdin();
                let mut input = String::new();
                stdin.read_line(&mut input).unwrap();
                Ok(Value::String(input.into_boxed_str()))
            }),
        );
        builtins.insert(
            ".read_all".into(),
            Rc::new(|_| {
                let mut stdin = std::io::stdin();
                let mut input = Vec::new();
                stdin.read_to_end(&mut input).unwrap();
                let input = String::from_utf8(input)
                    .map_err(|_| RuntimeErrorKind::Explicit("invalid utf-8 from stdin".into()))?;
                Ok(Value::String(input.into_boxed_str()))
            }),
        );
        builtins.insert(
            ".read_file".into(),
            Rc::new(|v| {
                let Value::String(v) = v else {
                    return Err(RuntimeErrorKind::Explicit(
                        "expected string for `.read_file`".into(),
                    ));
                };
                Ok(match std::fs::read_to_string(v.as_ref()) {
                    Ok(src) => {
                        Value::Object(Box::new([Value::Unit, Value::String(src.into_boxed_str())]))
                    }
                    Err(err) => Value::Object(Box::new([
                        Value::Void,
                        Value::String(err.to_string().into_boxed_str()),
                    ])),
                })
            }),
        );
        builtins.insert(
            ".absolute".into(),
            Rc::new(|v| {
                let Value::String(v) = v else {
                    return Err(RuntimeErrorKind::Explicit(
                        "expected string for `.read_file`".into(),
                    ));
                };
                Ok(match std::fs::canonicalize(v.as_ref()) {
                    Ok(src) => Value::Object(Box::new([
                        Value::Unit,
                        Value::String(src.to_string_lossy().to_owned().into()),
                    ])),
                    Err(err) => Value::Object(Box::new([
                        Value::Void,
                        Value::String(err.to_string().into_boxed_str()),
                    ])),
                })
            }),
        );
        builtins.insert(
            ".char".into(),
            Rc::new(|v| {
                let Value::Number(v) = v else {
                    return Err(RuntimeErrorKind::Explicit(
                        "invalid value to coorse into char".into(),
                    ));
                };
                Ok(Value::String(
                    ((v.floor() as u8) as char).to_string().into_boxed_str(),
                ))
            }),
        );
        builtins.insert(
            ".bytes".into(),
            Rc::new(|v| {
                let Value::String(v) = v else {
                    return Err(RuntimeErrorKind::Explicit(
                        "expected string for `.bytes`".into(),
                    ));
                };
                Ok(v.bytes().rfold(Value::Void, |acc, ch| {
                    Value::Object(Box::new([Value::Number(ch.into()), acc]))
                }))
            }),
        );
        builtins.insert(
            ".length".into(),
            Rc::new(|v| {
                let Value::String(v) = v else {
                    return Err(RuntimeErrorKind::Explicit(
                        "expected string for `.length`".into(),
                    ));
                };
                Ok(Value::Number(v.len() as f64))
            }),
        );
        builtins.insert(
            ".index".into(),
            Rc::new(|v| {
                let Value::Object(v) = v else {
                    return Err(RuntimeErrorKind::Explicit(
                        "expected (int, string) for `.index`".into(),
                    ));
                };
                let [Value::Number(n), Value::String(s)] = &*v else {
                    return Err(RuntimeErrorKind::Explicit(
                        "expected (int, string) for `.index`".into(),
                    ));
                };
                Ok(match s.chars().nth(n.floor() as usize) {
                    Some(c) => Value::String(c.to_string().into_boxed_str()),
                    None => Value::Void,
                })
            }),
        );
        builtins.insert(
            ".error".into(),
            Rc::new(|v| Err(RuntimeErrorKind::Explicit(v.to_string().into_boxed_str()))),
        );
        builtins.insert(
            ".type".into(),
            Rc::new(|v| {
                Ok(Value::String(
                    match v {
                        Value::Unit => "unit",
                        Value::Void => "void",
                        Value::String(_) => "string",
                        Value::Object(_) => "object",
                        Value::Function(_) | Value::Native(_) => "function",
                        Value::Number(_) => "number",
                    }
                    .into(),
                ))
            }),
        );
        builtins.insert(
            ".inspect".into(),
            Rc::new(|v| Ok(Value::String(format!("{v:?}").into_boxed_str()))),
        );
        builtins.insert(
            ".split".into(),
            Rc::new(|v| {
                let Value::String(v) = v else {
                    return Err(RuntimeErrorKind::Explicit(
                        "`.split` only works on strings".into(),
                    ));
                };

                Ok(v.chars().rfold(Value::Void, |acc, ch| {
                    Value::Object(Box::new([
                        Value::String(ch.to_string().into_boxed_str()),
                        acc,
                    ]))
                }))
            }),
        );
        Self {
            funcs: HashMap::new(),
            builtins,
        }
    }
}

impl Interpreter {
    pub fn register(&mut self, defs: Vec<(PathBuf, Vec<Def>)>) {
        for (path, defs) in defs {
            for def in defs {
                self.funcs.insert(def.name, (path.clone(), def.branches));
            }
        }
    }

    fn eval_expr(
        &self,
        path: &Path,
        expr: Expr,
        locals: &mut HashMap<Box<str>, Value>,
    ) -> Result<Value, RuntimeError> {
        let (kind, span) = expr.parts();
        match kind {
            ExprKind::Grouped(e) => self.eval_expr(path, *e, locals),
            ExprKind::Unit => Ok(Value::Unit),
            ExprKind::Void => Ok(Value::Void),
            ExprKind::Number(number) => Ok(Value::Number(number)),
            ExprKind::String(string) => Ok(Value::String(string)),
            ExprKind::Object(obj) => Ok({
                let mut vals = Vec::with_capacity(obj.len());
                for exp in obj {
                    vals.push(self.eval_expr(path, exp, locals)?);
                }
                Value::Object(vals.into_boxed_slice())
            }),
            ExprKind::Named(name) => {
                if let Some(v) = locals.get(&name) {
                    Ok(v.clone())
                } else if self.builtins.contains_key(&name) {
                    Ok(Value::Native(name))
                } else if self.funcs.contains_key(&name) {
                    Ok(Value::Function(name))
                } else {
                    Err(RuntimeError::new(
                        path.to_owned(),
                        RuntimeErrorKind::UndefinedBinding(name),
                        span,
                    ))
                }
            }
            ExprKind::Let {
                pattern,
                body,
                next,
            } => {
                let (kind, span) = body.parts();
                let value = self.eval_expr(path, Expr::new(kind, span), locals)?;
                if !self.apply_pattern(&value, pattern, locals)? {
                    return Err(RuntimeError::new(
                        path.to_owned(),
                        RuntimeErrorKind::UnmatchedLet { value },
                        span,
                    ));
                }
                self.eval_expr(path, *next, locals)
            }
            ExprKind::Binary {
                lhs,
                rhs,
                op,
                op_span,
            } => {
                let lhs = self.eval_expr(path, *lhs, locals)?;
                let rhs = self.eval_expr(path, *rhs, locals)?;

                match (lhs, rhs, op) {
                    (Value::Number(lhs), Value::Number(rhs), Op::Add) => {
                        Ok(Value::Number(lhs + rhs))
                    }
                    (Value::Number(lhs), Value::Number(rhs), Op::Subtract) => {
                        Ok(Value::Number(lhs - rhs))
                    }
                    (Value::Number(lhs), Value::Number(rhs), Op::Multiply) => {
                        Ok(Value::Number(lhs * rhs))
                    }
                    (Value::Number(lhs), Value::Number(rhs), Op::Modulo) => {
                        Ok(Value::Number(lhs % rhs))
                    }
                    (Value::Number(lhs), Value::Number(rhs), Op::Divide) => {
                        Ok(Value::Number(lhs / rhs))
                    }
                    (Value::Number(lhs), Value::Number(rhs), Op::Greater) => Ok((lhs > rhs).into()),
                    (Value::Number(lhs), Value::Number(rhs), Op::Less) => Ok((lhs < rhs).into()),
                    (Value::String(lhs), Value::String(rhs), Op::Concat) => {
                        Ok(Value::String(format!("{lhs}{rhs}").into_boxed_str()))
                    }
                    (Value::Object(lhs), Value::Object(rhs), Op::Concat) => {
                        let mut lhs = Vec::from(lhs);
                        lhs.append(&mut Vec::from(rhs));
                        Ok(Value::Object(lhs.into_boxed_slice()))
                    }
                    (lhs, Value::Native(f), Op::PipeInto) => self.builtins[&f](lhs)
                        .map_err(|e| RuntimeError::new(path.to_owned(), e, span)),
                    (lhs, Value::Function(f), Op::PipeInto) => Ok(self.apply_func(&f, lhs, span)?),
                    (
                        lhs,
                        rhs,
                        Op::Add
                        | Op::Subtract
                        | Op::Multiply
                        | Op::Divide
                        | Op::Modulo
                        | Op::Greater
                        | Op::Less
                        | Op::Concat
                        | Op::PipeInto,
                    ) => Err(RuntimeError::new(
                        path.to_owned(),
                        RuntimeErrorKind::DoesntSupportTypes {
                            lhs,
                            rhs,
                            op,
                            op_span,
                        },
                        span,
                    )),
                    (lhs, rhs, Op::Equal) => Ok((lhs == rhs).into()),
                    (lhs, rhs, Op::Cons) => Ok(Value::Object(Box::new([lhs, rhs]))),

                    (_, rhs, Op::Bang) => Ok(rhs),
                }
            }
        }
    }

    pub fn run(&mut self, args: Vec<String>) -> Result<Option<Value>, RuntimeError> {
        if self.funcs.contains_key("main") {
            Ok(Some(self.apply_func(
                "main",
                args.into_iter().rfold(Value::Void, |acc, arg| {
                    Value::Object(Box::new([Value::String(arg.into_boxed_str()), acc]))
                }),
                Span::new(0, 0),
            )?))
        } else {
            Ok(None)
        }
    }

    fn apply_func(&self, func: &str, value: Value, span: Span) -> Result<Value, RuntimeError> {
        let mut locals = HashMap::new();
        let (path, branches) = self.funcs[func].clone();
        for (case, expr) in branches {
            let inner_locals = HashMap::new();
            if self.apply_case(&path, value.clone(), case, &mut locals)? {
                locals.extend(inner_locals);
                return self.eval_expr(&path, expr, &mut locals);
            }
        }
        Err(RuntimeError::new(
            path,
            RuntimeErrorKind::UnmatchedValue {
                value,
                func: func.into(),
            },
            span,
        ))
    }

    fn apply_case(
        &self,
        path: &Path,
        val: Value,
        case: Case,
        locals: &mut HashMap<Box<str>, Value>,
    ) -> Result<bool, RuntimeError> {
        let (pat, guard) = case.parts();
        let res = self.apply_pattern(&val, pat, locals)?;
        Ok(if let Some(guard) = guard {
            if res {
                let value = self.eval_expr(path, guard, locals)?;
                value != Value::Void
            } else {
                false
            }
        } else {
            res
        })
    }

    fn apply_pattern(
        &self,
        val: &Value,
        pattern: Pattern,
        locals: &mut HashMap<Box<str>, Value>,
    ) -> Result<bool, RuntimeError> {
        let (kind, _) = pattern.parts();
        Ok(match (val, kind) {
            (val, PatternKind::Grouped(p)) => self.apply_pattern(val, *p, locals)?,
            (v, PatternKind::Named(n)) => {
                locals.insert(n, v.clone());
                true
            }
            (_, PatternKind::Wildcard) => true,
            (Value::Unit, PatternKind::Unit) => true,
            (Value::Void, PatternKind::Void) => true,
            (Value::Number(n1), PatternKind::Number(n2)) => *n1 == n2,
            (Value::String(s1), PatternKind::String(s2)) => *s1 == s2,
            (Value::Object(obj), PatternKind::Cons(p1, p2)) => {
                let [v1, v2] = &**obj else { return Ok(false) };
                self.apply_pattern(v1, *p1, locals)? && self.apply_pattern(v2, *p2, locals)?
            }
            (Value::Object(obj), PatternKind::Object { obj: pat, spread }) => {
                let pat_len = pat.len();
                let (res, binding) = match spread {
                    Spread::None => (obj.len() == pat_len, None),
                    Spread::Ident(ident) => (obj.len() >= pat_len, Some(ident)),
                    Spread::Wild => (obj.len() >= pat_len, None),
                };
                res && {
                    for (val, p) in obj.into_iter().zip(pat.into_iter()) {
                        if !self.apply_pattern(val, p, locals)? {
                            return Ok(false);
                        }
                    }

                    if let Some(binding) = binding {
                        locals.insert(binding, Value::Object(Box::from(&obj[pat_len..])));
                    }

                    true
                }
            }
            _ => false,
        })
    }
}
