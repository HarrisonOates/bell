use crate::{
    report::{Diagnostic, Location, Result, Status},
    work::Work,
};
use hddl_analyzer::{
    LexicalAnalyzer, LexicalErrorType, NumberType, PunctuationType, Token, TokenPosition,
};
use std::collections::BTreeSet;

#[derive(Clone, Debug)]
pub(crate) struct Node {
    pub text: Option<String>,
    pub children: Vec<Node>,
    pub location: Location,
    span: std::ops::Range<usize>,
}

impl Node {
    pub fn atom(&self) -> Result<&str> {
        self.text
            .as_deref()
            .ok_or_else(|| self.error("expected a symbol"))
    }
    pub fn list(&self) -> Result<&[Node]> {
        if self.text.is_some() {
            Err(self.error("expected a parenthesized expression"))
        } else {
            Ok(&self.children)
        }
    }
    pub fn head(&self) -> &str {
        self.children
            .first()
            .and_then(|x| x.text.as_deref())
            .unwrap_or("")
    }
    pub fn error(&self, message: impl Into<String>) -> Diagnostic {
        Diagnostic::input("syntax", message).at(self.location.clone())
    }
    pub fn name(&self) -> Result<String> {
        let s = self.atom()?;
        if !s.as_bytes().first().is_some_and(u8::is_ascii_alphabetic)
            || !s
                .bytes()
                .all(|c| c.is_ascii_alphanumeric() || c == b'-' || c == b'_')
        {
            return Err(self.error(format!("expected a ground name, found {s}")));
        }
        Ok(s.into())
    }
}

// HDDL-Parser supplies tokenization. This small reader also enforces a single
// complete document and bounded nesting before calling its domain/problem parser.
pub(crate) fn document(bytes: &Vec<u8>, file: &str, work: &mut Work) -> Result<Node> {
    work.charge(bytes.len() as u64 / 64 + 1);
    let source = std::str::from_utf8(bytes)
        .map_err(|_| Diagnostic::input("encoding", "input must be UTF-8"))?;
    let lines: Vec<_> = source.lines().collect();
    let mut offset = 0;
    let line_starts: Vec<_> = source
        .split_inclusive('\n')
        .map(|line| {
            let start = offset;
            offset += line.len();
            start
        })
        .collect();
    let lexer = LexicalAnalyzer::with_tab_width(bytes, 1);
    let mut stack: Vec<Node> = vec![];
    let mut root = None;
    loop {
        work.tick();
        let token = match lexer.get_token() {
            Ok(t) => t,
            Err(e)
                if file == "plan"
                    && e.error_type == LexicalErrorType::InvalidKeyword
                    && matches!(e.lexeme.as_str(), "decomposition" | "root" | "unsolvable") =>
            {
                Token::Identifier("")
            }
            Err(e) if !e.lexeme.is_empty() && e.lexeme.bytes().all(|b| b.is_ascii_digit()) => {
                return Err(Diagnostic::new(Status::LimitExceeded,"integer_range","integer literal exceeds the parsing dependency's range (0..=9223372036854775807)").at(Location::new(file,e.position)));
            }
            Err(e) => {
                return Err(
                    Diagnostic::input("lexical", e.to_string()).at(Location::new(file, e.position))
                );
            }
        };
        let pos = lexer.get_last_token_position();
        let location = Location::new(file, pos);
        let start = line_starts
            .get(pos.line as usize)
            .copied()
            .unwrap_or(bytes.len())
            + pos.column as usize;
        match token {
            Token::EOF => break,
            Token::Punctuator(PunctuationType::LParentheses) => {
                if stack.len() >= 128 {
                    return Err(Diagnostic::new(
                        Status::LimitExceeded,
                        "nesting_limit",
                        "input nesting exceeds 128 levels",
                    )
                    .at(location));
                }
                if stack.is_empty() && root.is_some() {
                    return Err(
                        Diagnostic::input("trailing_input", "expected end of file").at(location)
                    );
                }
                stack.push(Node {
                    text: None,
                    children: vec![],
                    location,
                    span: start..start + 1,
                });
            }
            Token::Punctuator(PunctuationType::RParentheses) => {
                let mut node = stack.pop().ok_or_else(|| {
                    Diagnostic::input("syntax", "unmatched closing parenthesis").at(location)
                })?;
                node.span.end = start + 1;
                if let Some(parent) = stack.last_mut() {
                    parent.children.push(node);
                } else {
                    root = Some(node);
                }
            }
            _ => {
                if let Token::Identifier(name) = &token
                    && !name.is_empty()
                {
                    let name = name.strip_prefix('?').unwrap_or(name);
                    if !name.as_bytes().first().is_some_and(u8::is_ascii_alphabetic)
                        || !name
                            .bytes()
                            .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
                    {
                        return Err(Diagnostic::input(
                            "identifier",
                            "names must begin with an ASCII letter",
                        )
                        .at(location));
                    }
                }
                if matches!(token, Token::Number(NumberType::Real(_))) {
                    return Err(Diagnostic::input(
                        "integer_required",
                        "IPC costs must be non-negative integer literals",
                    )
                    .at(location));
                }
                // Tokens are ASCII; comment text may be Unicode. Byte slicing
                // avoids rescanning a one-line certificate for every token.
                let line = lines.get(pos.line as usize).unwrap_or(&"");
                let start = pos.column as usize;
                let text = line
                    .get(start..start + pos.length as usize)
                    .ok_or_else(|| {
                        Diagnostic::input("encoding", "non-ASCII token").at(location.clone())
                    })?
                    .to_string();
                let parent = stack.last_mut().ok_or_else(|| {
                    Diagnostic::input("syntax", "expected a parenthesized document")
                        .at(location.clone())
                })?;
                parent.children.push(Node {
                    text: Some(text),
                    children: vec![],
                    location,
                    span: line_starts[pos.line as usize] + start
                        ..line_starts[pos.line as usize] + start + pos.length as usize,
                });
            }
        }
    }
    if let Some(unclosed) = stack.last() {
        return Err(unclosed.error("unclosed parenthesis"));
    }
    root.ok_or_else(|| Diagnostic::input("empty_input", format!("{file} file is empty")))
}

pub(crate) fn model_syntax(node: &Node) -> Result<()> {
    let parts = node.list()?;
    if parts.len() < 2 || node.head() != "define" {
        return Err(node.error("expected (define ...)"));
    }
    let header = parts[1].list()?;
    if header.len() != 2 || !matches!(parts[1].head(), "domain" | "problem") {
        return Err(parts[1].error("expected (domain name) or (problem name)"));
    }
    header[1].name()?;
    let mut seen = BTreeSet::new();
    for block in &parts[2..] {
        block.list()?;
        let head = block.head();
        if !matches!(head, ":action" | ":method" | ":task") && !seen.insert(head) {
            return Err(block.error(format!("duplicate {head} block")));
        }
        check_keys(block)?;
        supported_syntax(block)?;
    }
    if parts[1].head() == "problem" && !seen.contains(":init") {
        return Err(node.error("problem must contain an :init block (which may be empty)"));
    }
    Ok(())
}

fn check_keys(node: &Node) -> Result<()> {
    let mut keys = BTreeSet::new();
    for child in node.children.iter().skip(1) {
        if let Some(text) = &child.text {
            let key = match text.as_str() {
                ":tasks" | ":subtasks" | ":ordered-tasks" | ":ordered-subtasks" => ":tasks",
                ":order" | ":ordering" => ":ordering",
                x => x,
            };
            if key.starts_with(':') && !keys.insert(key) {
                return Err(child.error(format!("duplicate {key}")));
            }
        }
    }
    Ok(())
}

fn supported_syntax(node: &Node) -> Result<()> {
    if matches!(node.head(), "oneof" | "probabilistic" | "either") {
        return Err(
            Diagnostic::unsupported(format!("{} is not supported", node.head()))
                .at(node.location.clone()),
        );
    }
    if node.head() == "<" && node.children.len() < 3 {
        return Err(node.error("ordering needs a predecessor and at least one successor"));
    }
    for child in &node.children {
        supported_syntax(child)?;
    }
    Ok(())
}

// The parser uses Empty both for () and for a connective's closing token.
// Spell empty conditions as (and) so nested truth constants cannot terminate
// an and/or early. Keep an insertion map for diagnostics and negative init.
pub(crate) struct ParserSource {
    pub bytes: Vec<u8>,
    insertions: Vec<(usize, Location)>,
}

impl ParserSource {
    pub fn new(root: &Node, source: &[u8], work: &mut Work) -> Result<Self> {
        let mut insertions = vec![];
        for block in root.children.iter().skip(2) {
            match block.head() {
                ":goal" => {
                    if let Some(condition) = block.children.get(1) {
                        condition_syntax(condition, &mut insertions)?;
                    }
                }
                ":action" | ":method" => {
                    for pair in block.children.windows(2) {
                        match pair[0].text.as_deref() {
                            Some(":precondition") => condition_syntax(&pair[1], &mut insertions)?,
                            Some(":effect") => effect_syntax(&pair[1], &mut insertions)?,
                            _ => (),
                        }
                    }
                }
                _ => (),
            }
        }
        insertions.sort_by_key(|(offset, _)| *offset);
        work.charge((source.len() / 64 + insertions.len() * 3 + 1) as u64);
        let mut bytes = Vec::with_capacity(source.len() + insertions.len() * 3);
        let mut start = 0;
        for (offset, _) in &insertions {
            bytes.extend_from_slice(&source[start..*offset]);
            bytes.extend_from_slice(b"and");
            start = *offset;
        }
        bytes.extend_from_slice(&source[start..]);
        Ok(Self { bytes, insertions })
    }

    pub fn shifted_position(&self, (line, column): (u32, u32)) -> (u32, u32) {
        let shift = self
            .insertions
            .iter()
            .filter(|(_, at)| at.line == line + 1 && at.column <= column)
            .count() as u32
            * 3;
        (line, column + shift)
    }

    pub fn restore_location(&self, location: &mut Location) {
        let mut shift = 0;
        for (_, at) in &self.insertions {
            if at.line == location.line && at.column + shift < location.column {
                shift += (location.column - (at.column + shift + 1)).min(3);
            }
        }
        location.column -= shift;
    }

    pub fn restore_error(&self, mut error: Diagnostic) -> Diagnostic {
        if let Some(location) = &mut error.location {
            self.restore_location(location);
            if error.code == "parse"
                && error.message.starts_with('[')
                && let Some((_, rest)) = error.message.split_once("]:")
            {
                error.message = format!("[{}:{}]:{rest}", location.line, location.column);
            }
        }
        error
    }
}

fn condition_syntax(node: &Node, insertions: &mut Vec<(usize, Location)>) -> Result<()> {
    if node.text.is_none() && node.children.is_empty() {
        insertions.push((node.span.start + 1, node.location.clone()));
    }
    match node.head() {
        "when" => return Err(node.error("conditions use imply; when is an effect")),
        "and" | "or" | "not" | "imply" => {
            for child in node.children.iter().skip(1) {
                condition_syntax(child, insertions)?;
            }
        }
        "forall" | "exists" => {
            if let Some(body) = node.children.get(2) {
                condition_syntax(body, insertions)?;
            }
        }
        _ => (),
    }
    Ok(())
}

fn effect_syntax(node: &Node, insertions: &mut Vec<(usize, Location)>) -> Result<()> {
    match node.head() {
        "imply" => return Err(node.error("conditional effects use when; imply is a condition")),
        "when" => {
            if let Some(guard) = node.children.get(1) {
                condition_syntax(guard, insertions)?;
            }
            if let Some(body) = node.children.get(2) {
                effect_syntax(body, insertions)?;
            }
        }
        "forall" => {
            if let Some(body) = node.children.get(2) {
                effect_syntax(body, insertions)?;
            }
        }
        "and" | "not" => {
            for child in node.children.iter().skip(1) {
                effect_syntax(child, insertions)?;
            }
        }
        _ => (),
    }
    Ok(())
}

// The dependency's initial-state AST stores only positive atoms. Remove only
// each explicit negative literal's wrapper before parsing, preserving offsets;
// the model then checks the parsed atom's type and records its negative polarity.
pub(crate) fn initial_polarities(node: &Node, bytes: &mut [u8]) -> Result<BTreeSet<(u32, u32)>> {
    let mut negative = BTreeSet::new();
    for block in &node.children {
        if block.head() != ":init" {
            continue;
        }
        for literal in &block.children[1..] {
            if literal.head() != "not" {
                continue;
            }
            if literal.children.len() != 2 {
                return Err(literal.error("expected (not (predicate arguments...))"));
            }
            let inner = &literal.children[1];
            if inner.list()?.is_empty() {
                return Err(inner.error("expected a predicate"));
            }
            for term in &inner.children {
                term.name()?;
            }
            let pos = &inner.children[0].location;
            negative.insert((pos.line - 1, pos.column - 1));
            for span in [
                literal.span.start..inner.span.start,
                inner.span.end..literal.span.end,
            ] {
                for byte in &mut bytes[span] {
                    if !byte.is_ascii_whitespace() {
                        *byte = b' ';
                    }
                }
            }
        }
    }
    Ok(negative)
}

pub(crate) fn parser_error(file: &str, error: hddl_analyzer::ParsingError) -> Diagnostic {
    let pos = match &error {
        hddl_analyzer::ParsingError::Lexiacal(e) => e.position,
        hddl_analyzer::ParsingError::Syntactic(e) => e.position,
        _ => TokenPosition::default(),
    };
    Diagnostic::input("parse", error.to_string()).at(Location::new(file, pos))
}
