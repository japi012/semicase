use std::{fmt, str::CharIndices};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    Identifier,
    Wildcard,

    String,
    Number,

    Plus,
    Minus,
    Arrow,
    BackArrow,
    Star,
    Slash,
    Percent,

    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,

    PlusPlus,
    Comma,
    Colon,
    Semicolon,
    At,
    Question,
    Bang,
    Pipe,
    PipeInto,

    Greater,
    Less,
    Equal,

    Include,
    Let,

    Eof,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TokenKind::Identifier => "identifier",
                TokenKind::Wildcard => "`_`",

                TokenKind::String => "string",
                TokenKind::Number => "number",

                TokenKind::Plus => "`+`",
                TokenKind::Minus => "`-`",
                TokenKind::Arrow => "`->`",
                TokenKind::BackArrow => "`<-`",
                TokenKind::Star => "`*`",
                TokenKind::Slash => "`/`",
                TokenKind::Percent => "`%`",

                TokenKind::LeftParen => "`(`",
                TokenKind::RightParen => "`)`",
                TokenKind::LeftBrace => "`{`",
                TokenKind::RightBrace => "`}`",

                TokenKind::PlusPlus => "`++`",
                TokenKind::Comma => "`,`",
                TokenKind::Colon => "`:`",
                TokenKind::Semicolon => "`;`",
                TokenKind::At => "`@`",
                TokenKind::Question => "`?`",
                TokenKind::Bang => "`!`",
                TokenKind::Pipe => "`|`",
                TokenKind::PipeInto => "`|>`",

                TokenKind::Greater => "`>`",
                TokenKind::Less => "`<`",
                TokenKind::Equal => "`=`",

                TokenKind::Include => "keyword `include`",
                TokenKind::Let => "keyword `let`",

                TokenKind::Eof => "end of file",
            }
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Token {
    kind: TokenKind,
    span: Span,
}

impl Token {
    fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> TokenKind {
        self.kind
    }

    pub fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Span {
    start: usize,
    end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn parts(&self) -> (usize, usize) {
        (self.start, self.end)
    }

    pub fn start(&self) -> usize {
        self.start
    }

    pub fn end(&self) -> usize {
        self.end
    }
}

#[derive(Debug, Clone)]
pub struct Lexer<'src> {
    src: &'src str,
    chars: CharIndices<'src>,
}

impl<'src> Lexer<'src> {
    pub fn new(src: &'src str) -> Self {
        Self {
            src,
            chars: src.char_indices(),
        }
    }

    fn peek(&self) -> Option<(usize, char)> {
        let mut chars = self.chars.clone();
        chars.next()
    }

    pub fn peek_token(&self) -> Token {
        let mut cloned = self.clone();
        cloned.token()
    }

    fn skip_whitespace(&mut self) {
        while self.peek().is_some_and(|(_, c)| c.is_whitespace()) {
            self.chars.next();
        }
        while self.peek().is_some_and(|(_, c)| c == '#') {
            while self.peek().is_some_and(|(_, c)| c != '\n') {
                self.chars.next();
            }
            while self.peek().is_some_and(|(_, c)| c.is_whitespace()) {
                self.chars.next();
            }
        }
    }

    pub fn slice(&self, token: Token) -> &'src str {
        let (start, end) = token.span.parts();
        &self.src[start..end]
    }

    pub fn token(&mut self) -> Token {
        self.skip_whitespace();

        let Some((index, c)) = self.chars.next() else {
            return Token::new(
                TokenKind::Eof,
                Span::new(self.src.len(), self.src.len() + 1),
            );
        };

        match c {
            '(' => Token::new(TokenKind::LeftParen, Span::new(index, index + 1)),
            ')' => Token::new(TokenKind::RightParen, Span::new(index, index + 1)),
            '{' => Token::new(TokenKind::LeftBrace, Span::new(index, index + 1)),
            '}' => Token::new(TokenKind::RightBrace, Span::new(index, index + 1)),
            ':' => Token::new(TokenKind::Colon, Span::new(index, index + 1)),
            ';' => Token::new(TokenKind::Semicolon, Span::new(index, index + 1)),
            ',' => Token::new(TokenKind::Comma, Span::new(index, index + 1)),
            '>' => Token::new(TokenKind::Greater, Span::new(index, index + 1)),
            '<' => {
                if let Some((_, '-')) = self.peek() {
                    self.chars.next();
                    Token::new(TokenKind::BackArrow, Span::new(index, index + 2))
                } else {
                    Token::new(TokenKind::Less, Span::new(index, index + 1))
                }
            }
            '=' => Token::new(TokenKind::Equal, Span::new(index, index + 1)),
            '+' => {
                if let Some((_, '+')) = self.peek() {
                    self.chars.next();
                    Token::new(TokenKind::PlusPlus, Span::new(index, index + 2))
                } else {
                    Token::new(TokenKind::Plus, Span::new(index, index + 1))
                }
            }
            '-' => {
                if let Some((_, '>')) = self.peek() {
                    self.chars.next();
                    Token::new(TokenKind::Arrow, Span::new(index, index + 2))
                } else {
                    Token::new(TokenKind::Minus, Span::new(index, index + 1))
                }
            }
            '*' => Token::new(TokenKind::Star, Span::new(index, index + 1)),
            '/' => Token::new(TokenKind::Slash, Span::new(index, index + 1)),
            '%' => Token::new(TokenKind::Percent, Span::new(index, index + 1)),
            '@' => Token::new(TokenKind::At, Span::new(index, index + 1)),
            '?' => Token::new(TokenKind::Question, Span::new(index, index + 1)),
            '!' => Token::new(TokenKind::Bang, Span::new(index, index + 1)),
            '|' => {
                if let Some((_, '>')) = self.peek() {
                    self.chars.next();
                    Token::new(TokenKind::PipeInto, Span::new(index, index + 2))
                } else {
                    Token::new(TokenKind::Pipe, Span::new(index, index + 1))
                }
            }
            '"' => {
                let mut last = index + 1;
                while self.peek().is_some_and(|(_, c)| c != '"') {
                    let (_, c) = self.chars.next().unwrap();
                    last += 1;
                    if c == '\\' && self.chars.next().is_some() {
                        last += 1;
                    }
                }

                if let Some((l, _)) = self.chars.next() {
                    last = l + 1;
                }

                Token::new(TokenKind::String, Span::new(index, last))
            }
            c if c.is_ascii_digit() => {
                let mut last = index + 1;
                let mut is_float = false;
                while self
                    .peek()
                    .is_some_and(|(_, c)| c.is_ascii_digit() || c == '.')
                {
                    if self.peek().unwrap().1 == '.' && is_float {
                        break;
                    }
                    let (_, c) = self.chars.next().unwrap();
                    if c == '.' {
                        is_float = true;
                    }
                    last += 1;
                }
                Token::new(TokenKind::Number, Span::new(index, last))
            }

            _ => {
                let mut last = index + 1;
                const SPECIAL: &str = "+-*/%><=(){}:;,@?!|";
                while self
                    .peek()
                    .is_some_and(|(_, c)| !c.is_whitespace() && !SPECIAL.contains(c))
                {
                    self.chars.next();
                    last += 1;
                }

                let word = &self.src[index..last];

                Token::new(
                    match word {
                        "include" => TokenKind::Include,
                        "let" => TokenKind::Let,
                        "_" => TokenKind::Wildcard,
                        _ => TokenKind::Identifier,
                    },
                    Span::new(index, last),
                )
            }
        }
    }
}
