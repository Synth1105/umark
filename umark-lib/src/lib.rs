//! `umark-lib` is a lightweight Markdown-to-HTML parser implemented in Rust.
//!
//! It exposes two parsing modes:
//! - regular parsing (`parse*`): keeps inline/raw HTML
//! - safe parsing (`safe_parse*`): rejects script tags and any raw HTML
//!
//! # Flavor overview
//! - `MarkdownFlavor::CommonMark`: core CommonMark-style behavior
//! - `MarkdownFlavor::Gfm`: CommonMark + tables, task lists, strikethrough,
//!   literal autolinks, footnotes, and Mermaid chart blocks
//!
//! # Quick example
//! ```
//! use umark_lib::parse;
//!
//! let html = parse("# Hello");
//! assert!(html.contains("<h1>Hello</h1>"));
//! ```
//!
//! # Safe parsing example
//! ```
//! use umark_lib::safe_parse;
//!
//! assert!(safe_parse("plain text").is_ok());
//! assert!(safe_parse("x <span>y</span>").is_err());
//! ```
//!
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::fs;

/// Controls which Markdown feature set is enabled during parsing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MarkdownFlavor {
    /// Parse with CommonMark-style baseline features.
    CommonMark,
    /// Parse with GitHub Flavored Markdown extensions enabled.
    Gfm,
}

#[derive(Debug)]
struct MarkdownSecurityError;

impl fmt::Display for MarkdownSecurityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "raw html tag is not allowed in safe_parse")
    }
}

impl Error for MarkdownSecurityError {}

const RAW_HTML_OMITTED_MARKER: &str = "<!-- raw HTML omitted -->";
const MERMAID_BOOTSTRAP: &str = "<script src=\"https://cdn.jsdelivr.net/npm/mermaid@11/dist/mermaid.min.js\"></script>\n<script>if (typeof mermaid !== \"undefined\") { mermaid.initialize({ startOnLoad: true }); }</script>\n";

#[derive(Debug, Clone, Copy)]
struct ParserConfig {
    omit_raw_html: bool,
    enable_tables: bool,
    enable_task_list: bool,
    enable_strikethrough: bool,
    enable_autolink_literals: bool,
    enable_footnotes: bool,
    enable_charts: bool,
}

impl ParserConfig {
    fn from_flavor(flavor: MarkdownFlavor) -> Self {
        match flavor {
            MarkdownFlavor::CommonMark => Self {
                omit_raw_html: false,
                enable_tables: false,
                enable_task_list: false,
                enable_strikethrough: false,
                enable_autolink_literals: false,
                enable_footnotes: false,
                enable_charts: false,
            },
            MarkdownFlavor::Gfm => Self {
                omit_raw_html: false,
                enable_tables: true,
                enable_task_list: true,
                enable_strikethrough: true,
                enable_autolink_literals: true,
                enable_footnotes: true,
                enable_charts: true,
            },
        }
    }

    fn with_raw_html_omitted(mut self) -> Self {
        self.omit_raw_html = true;
        self
    }
}

#[derive(Default, Clone)]
struct DefinitionStore {
    links: HashMap<String, String>,
    footnotes: HashMap<String, String>,
    skip_lines: HashSet<usize>,
}

struct Parser<'a> {
    lines: Vec<&'a str>,
    defs: DefinitionStore,
    footnote_order: Vec<String>,
    config: ParserConfig,
}

/// Parse Markdown with the default flavor (`MarkdownFlavor::Gfm`) and return HTML.
///
/// # Examples
/// ```
/// use umark_lib::parse;
///
/// let html = parse("~~done~~");
/// assert!(html.contains("<del>done</del>"));
/// ```
pub fn parse(input: &str) -> String {
    parse_with_flavor(input, MarkdownFlavor::Gfm)
}

/// Parse Markdown with an explicit flavor and return HTML.
///
/// # Examples
/// ```
/// use umark_lib::{parse_with_flavor, MarkdownFlavor};
///
/// let gfm = parse_with_flavor("| a | b |\n|---|---|\n| 1 | 2 |", MarkdownFlavor::Gfm);
/// let commonmark = parse_with_flavor("| a | b |\n|---|---|\n| 1 | 2 |", MarkdownFlavor::CommonMark);
///
/// assert!(gfm.contains("<table>"));
/// assert!(!commonmark.contains("<table>"));
/// ```
pub fn parse_with_flavor(input: &str, flavor: MarkdownFlavor) -> String {
    parse_internal(input, ParserConfig::from_flavor(flavor))
}

/// Parse Markdown safely with the default flavor (`MarkdownFlavor::Gfm`).
///
/// This rejects:
/// - `<script ...>` tags (case-insensitive)
/// - any raw HTML blocks or inline raw HTML tags
///
/// # Examples
/// ```
/// use umark_lib::safe_parse;
///
/// assert!(safe_parse("**safe** text").is_ok());
/// assert!(safe_parse("<script>alert(1)</script>").is_err());
/// ```
pub fn safe_parse(input: &str) -> Result<String, Box<dyn Error>> {
    safe_parse_with_flavor(input, MarkdownFlavor::Gfm)
}

/// Parse Markdown safely with an explicit flavor.
///
/// # Examples
/// ```
/// use umark_lib::{safe_parse_with_flavor, MarkdownFlavor};
///
/// let html = safe_parse_with_flavor("~~x~~", MarkdownFlavor::CommonMark).unwrap();
/// assert!(!html.contains("<del>x</del>"));
/// ```
pub fn safe_parse_with_flavor(
    input: &str,
    flavor: MarkdownFlavor,
) -> Result<String, Box<dyn Error>> {
    reject_script_tag(input)?;
    let rendered = parse_internal(
        input,
        ParserConfig::from_flavor(flavor).with_raw_html_omitted(),
    );
    if rendered.contains(RAW_HTML_OMITTED_MARKER) {
        return Err(Box::new(MarkdownSecurityError));
    }
    Ok(rendered)
}

/// Parse Markdown from a file and write rendered HTML to another file using GFM.
///
/// In GFM mode, if Mermaid chart blocks are detected, a Mermaid runtime bootstrap
/// script is appended so charts can render when opening the output file in a browser.
///
/// # Examples
/// ```
/// use std::time::{SystemTime, UNIX_EPOCH};
/// use umark_lib::parse_from_file;
///
/// let suffix = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
/// let mut input = std::env::temp_dir();
/// let mut output = std::env::temp_dir();
/// input.push(format!("umark_parse_input_{suffix}.md"));
/// output.push(format!("umark_parse_output_{suffix}.html"));
///
/// std::fs::write(&input, "# Title").unwrap();
/// parse_from_file(input.to_str().unwrap(), output.to_str().unwrap()).unwrap();
///
/// let html = std::fs::read_to_string(&output).unwrap();
/// assert!(html.contains("<h1>Title</h1>"));
///
/// let _ = std::fs::remove_file(&input);
/// let _ = std::fs::remove_file(&output);
/// ```
pub fn parse_from_file(path: &str, output_path: &str) -> Result<(), Box<dyn Error>> {
    parse_from_file_with_flavor(path, output_path, MarkdownFlavor::Gfm)
}

/// Parse Markdown from a file with an explicit flavor and write HTML to a file.
///
/// In GFM mode, Mermaid runtime bootstrap is appended only when Mermaid blocks are found.
///
/// # Examples
/// ```
/// use std::time::{SystemTime, UNIX_EPOCH};
/// use umark_lib::{parse_from_file_with_flavor, MarkdownFlavor};
///
/// let suffix = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
/// let mut input = std::env::temp_dir();
/// let mut output = std::env::temp_dir();
/// input.push(format!("umark_parse_flavor_input_{suffix}.md"));
/// output.push(format!("umark_parse_flavor_output_{suffix}.html"));
///
/// std::fs::write(&input, "| a | b |\n|---|---|\n| 1 | 2 |").unwrap();
/// parse_from_file_with_flavor(
///     input.to_str().unwrap(),
///     output.to_str().unwrap(),
///     MarkdownFlavor::CommonMark,
/// ).unwrap();
///
/// let html = std::fs::read_to_string(&output).unwrap();
/// assert!(!html.contains("<table>"));
///
/// let _ = std::fs::remove_file(&input);
/// let _ = std::fs::remove_file(&output);
/// ```
pub fn parse_from_file_with_flavor(
    path: &str,
    output_path: &str,
    flavor: MarkdownFlavor,
) -> Result<(), Box<dyn Error>> {
    let content = fs::read_to_string(path)?;
    let rendered = parse_with_flavor(&content, flavor);
    let rendered = with_chart_runtime_if_needed(rendered, flavor);
    fs::write(output_path, rendered)?;
    Ok(())
}

/// Safely parse Markdown from a file and write output HTML with default GFM flavor.
///
/// This enforces the same safety rules as [`safe_parse`].
///
/// # Examples
/// ```
/// use std::time::{SystemTime, UNIX_EPOCH};
/// use umark_lib::safe_parse_from_file;
///
/// let suffix = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
/// let mut input = std::env::temp_dir();
/// let mut output = std::env::temp_dir();
/// input.push(format!("umark_safe_input_{suffix}.md"));
/// output.push(format!("umark_safe_output_{suffix}.html"));
///
/// std::fs::write(&input, "safe text").unwrap();
/// assert!(safe_parse_from_file(input.to_str().unwrap(), output.to_str().unwrap()).is_ok());
///
/// let _ = std::fs::remove_file(&input);
/// let _ = std::fs::remove_file(&output);
/// ```
pub fn safe_parse_from_file(path: &str, output_path: &str) -> Result<(), Box<dyn Error>> {
    safe_parse_from_file_with_flavor(path, output_path, MarkdownFlavor::Gfm)
}

/// Safely parse Markdown from a file with an explicit flavor and write HTML to a file.
///
/// # Examples
/// ```
/// use std::time::{SystemTime, UNIX_EPOCH};
/// use umark_lib::{safe_parse_from_file_with_flavor, MarkdownFlavor};
///
/// let suffix = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
/// let mut input = std::env::temp_dir();
/// let mut output = std::env::temp_dir();
/// input.push(format!("umark_safe_flavor_input_{suffix}.md"));
/// output.push(format!("umark_safe_flavor_output_{suffix}.html"));
///
/// std::fs::write(&input, "<div>raw html</div>").unwrap();
/// let result = safe_parse_from_file_with_flavor(
///     input.to_str().unwrap(),
///     output.to_str().unwrap(),
///     MarkdownFlavor::Gfm,
/// );
/// assert!(result.is_err());
///
/// let _ = std::fs::remove_file(&input);
/// let _ = std::fs::remove_file(&output);
/// ```
pub fn safe_parse_from_file_with_flavor(
    path: &str,
    output_path: &str,
    flavor: MarkdownFlavor,
) -> Result<(), Box<dyn Error>> {
    let content = fs::read_to_string(path)?;
    let rendered = safe_parse_with_flavor(&content, flavor)?;
    fs::write(output_path, rendered)?;
    Ok(())
}

fn parse_internal(input: &str, config: ParserConfig) -> String {
    let normalized = normalize_newlines(input);
    let lines: Vec<&str> = normalized.lines().collect();
    let defs = collect_definitions(&lines, config);
    let mut parser = Parser {
        lines,
        defs,
        footnote_order: Vec::new(),
        config,
    };
    parser.parse_blocks()
}

fn with_chart_runtime_if_needed(mut rendered: String, flavor: MarkdownFlavor) -> String {
    if flavor == MarkdownFlavor::Gfm
        && rendered.contains("<pre class=\"mermaid\">")
        && !rendered.contains("mermaid.initialize(")
    {
        rendered.push('\n');
        rendered.push_str(MERMAID_BOOTSTRAP);
    }
    rendered
}

fn reject_script_tag(input: &str) -> Result<(), Box<dyn Error>> {
    if contains_script_tag(input) {
        return Err(Box::new(MarkdownSecurityError));
    }
    Ok(())
}

fn contains_script_tag(input: &str) -> bool {
    let lowered = input.to_ascii_lowercase();
    let bytes = lowered.as_bytes();
    let mut i = 0usize;

    while i < bytes.len() {
        if bytes[i] != b'<' {
            i += 1;
            continue;
        }
        let mut j = i + 1;
        while j < bytes.len() && bytes[j].is_ascii_whitespace() {
            j += 1;
        }
        if j < bytes.len() && bytes[j] == b'/' {
            j += 1;
            while j < bytes.len() && bytes[j].is_ascii_whitespace() {
                j += 1;
            }
        }
        if j + 6 > bytes.len() {
            i += 1;
            continue;
        }
        if &lowered[j..j + 6] == "script" {
            let next = bytes.get(j + 6).copied().unwrap_or(b'>');
            if next.is_ascii_whitespace() || next == b'>' || next == b'/' {
                return true;
            }
        }
        i += 1;
    }
    false
}

impl<'a> Parser<'a> {
    fn parse_blocks(&mut self) -> String {
        let mut pos = 0usize;
        let mut out = String::new();

        while pos < self.lines.len() {
            if self.is_skipped(pos) || self.lines[pos].trim().is_empty() {
                pos += 1;
                continue;
            }

            if let Some((level, text, next)) = parse_setext_heading(&self.lines, pos) {
                let heading_text = text.trim().to_string();
                out.push_str(&format!(
                    "<h{level}>{}</h{level}>\n",
                    self.parse_inlines(&heading_text)
                ));
                pos = next;
                continue;
            }

            if is_thematic_break(self.lines[pos]) {
                out.push_str("<hr />\n");
                pos += 1;
                continue;
            }

            if let Some((level, text)) = parse_atx_heading(self.lines[pos]) {
                out.push_str(&format!(
                    "<h{level}>{}</h{level}>\n",
                    self.parse_inlines(text.trim())
                ));
                pos += 1;
                continue;
            }

            if is_fence_start(self.lines[pos]) {
                let (html, next) = self.parse_fenced_code(pos);
                out.push_str(&html);
                pos = next;
                continue;
            }

            if is_indented_code_line(self.lines[pos]) {
                let (html, next) = self.parse_indented_code(pos);
                out.push_str(&html);
                pos = next;
                continue;
            }

            if is_blockquote_line(self.lines[pos]) {
                let (html, next) = self.parse_blockquote(pos);
                out.push_str(&html);
                pos = next;
                continue;
            }

            if is_html_line(self.lines[pos]) {
                let (html, next) = self.parse_html_block(pos);
                out.push_str(&html);
                pos = next;
                continue;
            }

            if self.config.enable_tables && is_table_header(&self.lines, pos) {
                let (html, next) = self.parse_table(pos);
                out.push_str(&html);
                pos = next;
                continue;
            }

            if parse_list_prefix(self.lines[pos]).is_some() {
                let (html, next) = self.parse_list(pos);
                out.push_str(&html);
                pos = next;
                continue;
            }

            let (html, next) = self.parse_paragraph(pos);
            out.push_str(&html);
            pos = next;
        }

        if self.config.enable_footnotes && !self.footnote_order.is_empty() {
            out.push_str(&self.render_footnotes());
        }

        out
    }

    fn parse_subdocument(&mut self, markdown: &str) -> String {
        let normalized = normalize_newlines(markdown);
        let lines: Vec<&str> = normalized.lines().collect();
        let mut nested = Parser {
            lines,
            defs: self.defs.clone(),
            footnote_order: Vec::new(),
            config: self.config,
        };
        let html = nested.parse_blocks();
        for id in nested.footnote_order {
            self.note_footnote(id);
        }
        html
    }

    fn parse_fenced_code(&self, start: usize) -> (String, usize) {
        let first = self.lines[start].trim_start();
        let fence_char = first.chars().next().unwrap_or('`');
        let fence_len = first.chars().take_while(|c| *c == fence_char).count();
        let info = first[fence_len..].trim();
        let mut pos = start + 1;
        let mut code_lines = Vec::new();

        while pos < self.lines.len() {
            let line = self.lines[pos].trim_start();
            if is_fence_closing_line(line, fence_char, fence_len) {
                pos += 1;
                break;
            }
            code_lines.push(self.lines[pos]);
            pos += 1;
        }

        let code_raw = code_lines.join("\n");
        let code = html_escape(&code_raw);
        let lang = info.split_whitespace().next().unwrap_or("");
        let is_mermaid = self.config.enable_charts && lang.eq_ignore_ascii_case("mermaid");

        let html = if is_mermaid {
            format!("<pre class=\"mermaid\">{}</pre>\n", code)
        } else if info.is_empty() {
            format!("<pre><code>{}</code></pre>\n", code)
        } else {
            format!(
                "<pre><code class=\"language-{}\">{}</code></pre>\n",
                html_attr_escape(lang),
                code
            )
        };
        (html, pos)
    }

    fn parse_indented_code(&self, start: usize) -> (String, usize) {
        let mut pos = start;
        let mut code_lines = Vec::new();

        while pos < self.lines.len() {
            let line = self.lines[pos];
            if line.trim().is_empty() {
                code_lines.push("");
                pos += 1;
                continue;
            }

            if let Some(stripped) = strip_indented_code_prefix(line) {
                code_lines.push(stripped);
                pos += 1;
            } else {
                break;
            }
        }

        let code = html_escape(&code_lines.join("\n"));
        (format!("<pre><code>{}</code></pre>\n", code), pos)
    }

    fn parse_blockquote(&mut self, start: usize) -> (String, usize) {
        let mut pos = start;
        let mut parts = Vec::new();

        while pos < self.lines.len() {
            let line = self.lines[pos];
            if line.trim().is_empty() {
                parts.push(String::new());
                pos += 1;
                continue;
            }
            if !is_blockquote_line(line) {
                break;
            }
            parts.push(strip_blockquote_prefix(line).to_string());
            pos += 1;
        }

        let body = parts.join("\n");
        let inner = self.parse_subdocument(&body);
        (format!("<blockquote>\n{}</blockquote>\n", inner), pos)
    }

    fn parse_html_block(&self, start: usize) -> (String, usize) {
        if !self.config.omit_raw_html {
            let mut pos = start;
            while pos < self.lines.len() {
                if self.lines[pos].trim().is_empty() {
                    break;
                }
                pos += 1;
            }
            let raw = self.lines[start..pos].join("\n");
            return (format!("{raw}\n"), pos);
        }

        let mut pos = start;
        while pos < self.lines.len() {
            if self.lines[pos].trim().is_empty() {
                break;
            }
            pos += 1;
        }
        (format!("{RAW_HTML_OMITTED_MARKER}\n"), pos)
    }

    fn parse_table(&mut self, start: usize) -> (String, usize) {
        let headers = split_table_row(self.lines[start]);
        let aligns = parse_table_alignments(self.lines[start + 1]);
        let mut pos = start + 2;
        let mut rows: Vec<Vec<String>> = Vec::new();

        while pos < self.lines.len() {
            if self.is_skipped(pos) || self.lines[pos].trim().is_empty() {
                break;
            }
            if !self.lines[pos].contains('|') {
                break;
            }
            rows.push(split_table_row(self.lines[pos]));
            pos += 1;
        }

        let mut out = String::new();
        out.push_str("<table>\n<thead>\n<tr>");
        for (idx, cell) in headers.into_iter().enumerate() {
            push_table_cell_open(&mut out, "th", aligns.get(idx).copied().flatten());
            out.push_str(&self.parse_inlines(cell.trim()));
            out.push_str("</th>");
        }
        out.push_str("</tr>\n</thead>\n<tbody>\n");

        for row in rows {
            out.push_str("<tr>");
            for (idx, cell) in row.into_iter().enumerate() {
                push_table_cell_open(&mut out, "td", aligns.get(idx).copied().flatten());
                out.push_str(&self.parse_inlines(cell.trim()));
                out.push_str("</td>");
            }
            out.push_str("</tr>\n");
        }

        out.push_str("</tbody>\n</table>\n");
        (out, pos)
    }

    fn parse_list(&mut self, start: usize) -> (String, usize) {
        let (first_kind, _, base_indent) = parse_list_prefix_with_indent(self.lines[start])
            .unwrap_or((ListKind::Unordered, "", 0));
        let mut pos = start;
        let mut out = String::new();

        match first_kind {
            ListKind::Unordered => out.push_str("<ul>\n"),
            ListKind::Ordered(start_num) => {
                if start_num != 1 {
                    out.push_str(&format!("<ol start=\"{start_num}\">\n"));
                } else {
                    out.push_str("<ol>\n");
                }
            }
        }

        while pos < self.lines.len() {
            if self.is_skipped(pos) {
                break;
            }

            let Some((kind, item_line, indent)) = parse_list_prefix_with_indent(self.lines[pos])
            else {
                break;
            };
            if indent != base_indent || !same_kind_value(kind, first_kind) {
                break;
            }

            let mut item_parts = vec![item_line.to_string()];
            pos += 1;
            let mut loose = false;

            while pos < self.lines.len() {
                if self.is_skipped(pos) {
                    break;
                }

                let line = self.lines[pos];
                if line.trim().is_empty() {
                    loose = true;
                    item_parts.push(String::new());
                    pos += 1;
                    continue;
                }

                if let Some((next_kind, _, next_indent)) = parse_list_prefix_with_indent(line) {
                    if next_indent == base_indent && same_kind_value(next_kind, first_kind) {
                        break;
                    }
                    if next_indent <= base_indent && !same_kind_value(next_kind, first_kind) {
                        break;
                    }
                }

                if leading_indent(line) <= base_indent
                    && is_block_start(&self.lines, pos, self.config)
                {
                    break;
                }

                item_parts.push(dedent_list_continuation(line, base_indent).to_string());
                pos += 1;
            }

            out.push_str("<li>");

            let mut checkbox: Option<bool> = None;
            if self.config.enable_task_list && matches!(first_kind, ListKind::Unordered) {
                if let Some((checked, rest)) = parse_task_item(&item_parts[0]) {
                    checkbox = Some(checked);
                    item_parts[0] = rest.to_string();
                }
            }

            if let Some(checked) = checkbox {
                if checked {
                    out.push_str("<input type=\"checkbox\" checked=\"\" disabled=\"\" /> ");
                } else {
                    out.push_str("<input type=\"checkbox\" disabled=\"\" /> ");
                }
            }

            let item_markdown = item_parts.join("\n");
            let rendered = self.parse_subdocument(&item_markdown);
            if !loose {
                if let Some(stripped) = strip_single_paragraph_wrapper(&rendered) {
                    out.push_str(stripped);
                } else {
                    out.push_str(&rendered);
                }
            } else {
                out.push_str(&rendered);
            }
            out.push_str("</li>\n");
        }

        match first_kind {
            ListKind::Unordered => out.push_str("</ul>\n"),
            ListKind::Ordered(_) => out.push_str("</ol>\n"),
        }

        (out, pos)
    }

    fn parse_paragraph(&mut self, start: usize) -> (String, usize) {
        let mut pos = start;
        let mut parts = Vec::new();

        while pos < self.lines.len() {
            if self.is_skipped(pos) || self.lines[pos].trim().is_empty() {
                break;
            }
            if pos != start && is_block_start(&self.lines, pos, self.config) {
                break;
            }
            parts.push(self.lines[pos]);
            pos += 1;
        }

        let text = parts.join("\n");
        (format!("<p>{}</p>\n", self.parse_inlines(&text)), pos)
    }

    fn parse_inlines(&mut self, text: &str) -> String {
        let mut out = String::new();
        let mut i = 0usize;

        while i < text.len() {
            let rest = &text[i..];

            if rest.starts_with("\\\n") {
                out.push_str("<br />\n");
                i += 2;
                continue;
            }

            if rest.starts_with('\n') {
                match detect_hard_break(text, i) {
                    HardBreak::Spaces => {
                        trim_trailing_spaces(&mut out);
                        out.push_str("<br />\n");
                    }
                    HardBreak::Backslash => {
                        if out.ends_with('\\') {
                            out.pop();
                        }
                        out.push_str("<br />\n");
                    }
                    HardBreak::None => out.push('\n'),
                }
                i += 1;
                continue;
            }

            if let Some((ch, consumed)) = parse_escaped_char(rest) {
                push_escaped_char(&mut out, ch);
                i += consumed;
                continue;
            }

            if rest.starts_with('`') {
                if let Some((content, consumed)) = parse_code_span(rest) {
                    out.push_str("<code>");
                    out.push_str(&html_escape(content));
                    out.push_str("</code>");
                    i += consumed;
                    continue;
                }
            }

            if self.config.enable_footnotes && rest.starts_with("[^") {
                if let Some(end) = rest.find(']') {
                    let raw_id = &rest[2..end];
                    let key = normalize_key(raw_id);
                    if self.defs.footnotes.contains_key(&key) {
                        let index = self.note_footnote(key.clone());
                        let safe = footnote_id(&key);
                        out.push_str(&format!(
                            "<sup class=\"footnote-ref\"><a href=\"#fn-{safe}\" id=\"fnref-{safe}\">{index}</a></sup>"
                        ));
                        i += end + 1;
                        continue;
                    }
                }
            }

            if rest.starts_with("![") {
                if let Some((html, consumed)) = self.parse_image(rest) {
                    out.push_str(&html);
                    i += consumed;
                    continue;
                }
            }

            if rest.starts_with('[') {
                if let Some((html, consumed)) = self.parse_link_like(rest) {
                    out.push_str(&html);
                    i += consumed;
                    continue;
                }
            }

            if let Some((html, consumed)) = parse_angle_autolink(rest) {
                out.push_str(&html);
                i += consumed;
                continue;
            }

            if let Some((raw, consumed)) = parse_inline_html(rest) {
                if !self.config.omit_raw_html {
                    out.push_str(raw);
                } else {
                    out.push_str(RAW_HTML_OMITTED_MARKER);
                }
                i += consumed;
                continue;
            }

            if self.config.enable_autolink_literals {
                if let Some((href, text_value, consumed)) = parse_autolink_literal(rest) {
                    let href_escaped = html_escape(&href);
                    let text_escaped = html_escape(&text_value);
                    out.push_str(&format!("<a href=\"{href_escaped}\">{text_escaped}</a>"));
                    i += consumed;
                    continue;
                }
            }

            if let Some((content, consumed)) = wrapped(rest, "**") {
                out.push_str("<strong>");
                out.push_str(&self.parse_inlines(content));
                out.push_str("</strong>");
                i += consumed;
                continue;
            }

            if let Some((content, consumed)) = wrapped(rest, "__") {
                out.push_str("<strong>");
                out.push_str(&self.parse_inlines(content));
                out.push_str("</strong>");
                i += consumed;
                continue;
            }

            if self.config.enable_strikethrough {
                if let Some((content, consumed)) = wrapped(rest, "~~") {
                    out.push_str("<del>");
                    out.push_str(&self.parse_inlines(content));
                    out.push_str("</del>");
                    i += consumed;
                    continue;
                }
            }

            if let Some((content, consumed)) = wrapped(rest, "*") {
                out.push_str("<em>");
                out.push_str(&self.parse_inlines(content));
                out.push_str("</em>");
                i += consumed;
                continue;
            }

            if let Some((content, consumed)) = wrapped(rest, "_") {
                out.push_str("<em>");
                out.push_str(&self.parse_inlines(content));
                out.push_str("</em>");
                i += consumed;
                continue;
            }

            if let Some(ch) = rest.chars().next() {
                push_escaped_char(&mut out, ch);
                i += ch.len_utf8();
            } else {
                break;
            }
        }

        out
    }

    fn parse_image(&mut self, rest: &str) -> Option<(String, usize)> {
        let (alt, consumed_label) = parse_bracketed_label(&rest[1..])?;
        let after = &rest[1 + consumed_label..];

        let (url, consumed_after) = parse_inline_link_target(after)?;
        let html = format!(
            "<img src=\"{}\" alt=\"{}\" />",
            html_attr_escape(&url),
            html_attr_escape(alt)
        );
        Some((html, 1 + consumed_label + consumed_after))
    }

    fn parse_link_like(&mut self, rest: &str) -> Option<(String, usize)> {
        let (label, consumed_label) = parse_bracketed_label(rest)?;
        let after = &rest[consumed_label..];

        if let Some((url, consumed_after)) = parse_inline_link_target(after) {
            let html = format!(
                "<a href=\"{}\">{}</a>",
                html_attr_escape(&url),
                self.parse_inlines(label)
            );
            return Some((html, consumed_label + consumed_after));
        }

        if after.starts_with('[') {
            let (raw_ref, consumed_ref) = parse_bracketed_label(after)?;
            let key = if raw_ref.trim().is_empty() {
                normalize_key(label)
            } else {
                normalize_key(raw_ref)
            };
            if let Some(url) = self.defs.links.get(&key) {
                let html = format!(
                    "<a href=\"{}\">{}</a>",
                    html_attr_escape(url),
                    self.parse_inlines(label)
                );
                return Some((html, consumed_label + consumed_ref));
            }
        }

        let key = normalize_key(label);
        if let Some(url) = self.defs.links.get(&key) {
            let html = format!(
                "<a href=\"{}\">{}</a>",
                html_attr_escape(url),
                self.parse_inlines(label)
            );
            return Some((html, consumed_label));
        }

        None
    }

    fn note_footnote(&mut self, id: String) -> usize {
        if let Some(idx) = self.footnote_order.iter().position(|x| x == &id) {
            idx + 1
        } else {
            self.footnote_order.push(id);
            self.footnote_order.len()
        }
    }

    fn render_footnotes(&mut self) -> String {
        let mut out = String::new();
        out.push_str("<section class=\"footnotes\">\n<ol>\n");

        let footnote_ids = self.footnote_order.clone();
        for id in footnote_ids {
            let safe = footnote_id(&id);
            let text = self.defs.footnotes.get(&id).cloned().unwrap_or_default();
            out.push_str(&format!(
                "<li id=\"fn-{safe}\">{} <a href=\"#fnref-{safe}\" class=\"footnote-backref\">↩</a></li>\n",
                self.parse_inlines(text.trim())
            ));
        }

        out.push_str("</ol>\n</section>\n");
        out
    }

    fn is_skipped(&self, line: usize) -> bool {
        self.defs.skip_lines.contains(&line)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ListKind {
    Unordered,
    Ordered(usize),
}

fn normalize_newlines(input: &str) -> String {
    input.replace("\r\n", "\n").replace('\r', "\n")
}

fn collect_definitions(lines: &[&str], config: ParserConfig) -> DefinitionStore {
    let mut defs = DefinitionStore::default();
    let mut i = 0usize;

    while i < lines.len() {
        let line = lines[i].trim();

        if let Some((id, url)) = parse_link_definition(line) {
            defs.links.insert(normalize_key(id), url.to_string());
            defs.skip_lines.insert(i);
            i += 1;
            continue;
        }

        if config.enable_footnotes {
            if let Some((id, first_text)) = parse_footnote_definition(line) {
                let mut text_parts = vec![first_text.to_string()];
                defs.skip_lines.insert(i);
                i += 1;

                while i < lines.len() {
                    let next = lines[i];
                    if next.starts_with("    ") || next.starts_with('\t') {
                        text_parts.push(next.trim().to_string());
                        defs.skip_lines.insert(i);
                        i += 1;
                    } else {
                        break;
                    }
                }

                defs.footnotes
                    .insert(normalize_key(id), text_parts.join(" "));
                continue;
            }
        }

        i += 1;
    }

    defs
}

fn parse_atx_heading(line: &str) -> Option<(usize, &str)> {
    let trimmed = line.trim_start();
    let mut count = 0usize;
    for ch in trimmed.chars() {
        if ch == '#' {
            count += 1;
        } else {
            break;
        }
    }
    if count == 0 || count > 6 {
        return None;
    }
    let rest = trimmed[count..].trim_start();
    if rest.is_empty() {
        return None;
    }
    Some((count, rest.trim_end_matches('#').trim_end()))
}

fn parse_setext_heading<'a>(lines: &'a [&str], pos: usize) -> Option<(usize, &'a str, usize)> {
    if pos + 1 >= lines.len() {
        return None;
    }
    if lines[pos].trim().is_empty() {
        return None;
    }
    if !can_be_setext_content_line(lines[pos]) {
        return None;
    }

    let underline = lines[pos + 1].trim();
    if is_setext_underline(underline, '=') {
        return Some((1, lines[pos], pos + 2));
    }
    if is_setext_underline(underline, '-') {
        return Some((2, lines[pos], pos + 2));
    }
    None
}

fn can_be_setext_content_line(line: &str) -> bool {
    !line.trim().is_empty()
        && !is_thematic_break(line)
        && parse_atx_heading(line).is_none()
        && !is_fence_start(line)
        && !is_indented_code_line(line)
        && !is_blockquote_line(line)
        && !is_html_line(line)
        && parse_list_prefix(line).is_none()
}

fn is_setext_underline(line: &str, marker: char) -> bool {
    let trimmed = line.trim();
    !trimmed.is_empty() && trimmed.chars().all(|ch| ch == marker) && trimmed.len() >= 3
}

fn is_thematic_break(line: &str) -> bool {
    let trimmed = line.trim();
    if trimmed.len() < 3 {
        return false;
    }
    let candidate: String = trimmed.chars().filter(|c| !c.is_whitespace()).collect();
    if candidate.len() < 3 {
        return false;
    }
    candidate.chars().all(|ch| ch == '-')
        || candidate.chars().all(|ch| ch == '*')
        || candidate.chars().all(|ch| ch == '_')
}

fn is_fence_start(line: &str) -> bool {
    let trimmed = line.trim_start();
    trimmed.starts_with("```") || trimmed.starts_with("~~~")
}

fn is_indented_code_line(line: &str) -> bool {
    strip_indented_code_prefix(line).is_some()
}

fn strip_indented_code_prefix(line: &str) -> Option<&str> {
    if let Some(stripped) = line.strip_prefix("    ") {
        return Some(stripped);
    }
    line.strip_prefix('\t')
}

fn is_blockquote_line(line: &str) -> bool {
    line.trim_start().starts_with('>')
}

fn strip_blockquote_prefix(line: &str) -> &str {
    let trimmed = line.trim_start();
    let tail = trimmed.strip_prefix('>').unwrap_or(trimmed);
    tail.strip_prefix(' ').unwrap_or(tail)
}

fn is_html_line(line: &str) -> bool {
    line.trim_start().starts_with('<')
}

fn is_table_header(lines: &[&str], pos: usize) -> bool {
    if pos + 1 >= lines.len() {
        return false;
    }
    if !lines[pos].contains('|') {
        return false;
    }
    is_table_separator(lines[pos + 1])
}

fn is_table_separator(line: &str) -> bool {
    let trimmed = line.trim();
    if !trimmed.contains('-') {
        return false;
    }
    let cells = split_table_row(trimmed);
    if cells.is_empty() {
        return false;
    }
    cells.into_iter().all(|cell| {
        let c = cell.trim();
        c.len() >= 3 && c.chars().all(|ch| ch == '-' || ch == ':')
    })
}

fn split_table_row(line: &str) -> Vec<String> {
    line.trim()
        .trim_matches('|')
        .split('|')
        .map(|s| s.trim().to_string())
        .collect()
}

fn parse_list_prefix(line: &str) -> Option<(ListKind, &str)> {
    parse_list_prefix_with_indent(line).map(|(kind, rest, _)| (kind, rest))
}

fn parse_list_prefix_with_indent(line: &str) -> Option<(ListKind, &str, usize)> {
    let indent = leading_indent(line);
    let trimmed = line.trim_start_matches([' ', '\t']);
    if trimmed.len() < 2 {
        return None;
    }

    if (trimmed.starts_with("- ") || trimmed.starts_with("* ") || trimmed.starts_with("+ "))
        && trimmed.len() > 2
    {
        return Some((ListKind::Unordered, &trimmed[2..], indent));
    }

    let mut digits_end = 0usize;
    for (idx, ch) in trimmed.char_indices() {
        if ch.is_ascii_digit() {
            digits_end = idx + ch.len_utf8();
        } else {
            break;
        }
    }

    if digits_end == 0 || digits_end + 2 > trimmed.len() {
        return None;
    }

    let marker = trimmed.as_bytes()[digits_end] as char;
    if marker != '.' && marker != ')' {
        return None;
    }
    if trimmed.as_bytes()[digits_end + 1] != b' ' {
        return None;
    }

    let start = trimmed[..digits_end].parse::<usize>().ok()?;
    Some((ListKind::Ordered(start), &trimmed[digits_end + 2..], indent))
}

fn same_kind_value(current: ListKind, expected: ListKind) -> bool {
    matches!(
        (current, expected),
        (ListKind::Unordered, ListKind::Unordered) | (ListKind::Ordered(_), ListKind::Ordered(_))
    )
}

fn leading_indent(line: &str) -> usize {
    let mut count = 0usize;
    for ch in line.chars() {
        match ch {
            ' ' => count += 1,
            '\t' => count += 4,
            _ => break,
        }
    }
    count
}

fn dedent_list_continuation(line: &str, base_indent: usize) -> &str {
    if leading_indent(line) <= base_indent {
        return line.trim_start();
    }
    let mut removed_cols = 0usize;
    let mut byte_idx = 0usize;
    for (idx, ch) in line.char_indices() {
        match ch {
            ' ' => {
                removed_cols += 1;
                byte_idx = idx + 1;
            }
            '\t' => {
                removed_cols += 4;
                byte_idx = idx + 1;
            }
            _ => break,
        }
        if removed_cols >= base_indent + 2 {
            break;
        }
    }
    &line[byte_idx..]
}

fn strip_single_paragraph_wrapper(html: &str) -> Option<&str> {
    if !html.starts_with("<p>") || !html.ends_with("</p>\n") {
        return None;
    }
    if html[3..html.len() - 5].contains("\n<p>") {
        return None;
    }
    Some(&html[3..html.len() - 5])
}

fn is_fence_closing_line(line: &str, marker: char, min_len: usize) -> bool {
    let trimmed = line.trim_end();
    let count = trimmed.chars().take_while(|c| *c == marker).count();
    if count < min_len {
        return false;
    }
    trimmed[count..].trim().is_empty()
}

fn parse_table_alignments(separator_line: &str) -> Vec<Option<&'static str>> {
    split_table_row(separator_line)
        .into_iter()
        .map(|cell| {
            let c = cell.trim();
            let starts = c.starts_with(':');
            let ends = c.ends_with(':');
            match (starts, ends) {
                (true, true) => Some("center"),
                (true, false) => Some("left"),
                (false, true) => Some("right"),
                (false, false) => None,
            }
        })
        .collect()
}

fn push_table_cell_open(out: &mut String, tag: &str, align: Option<&str>) {
    if let Some(al) = align {
        out.push_str(&format!("<{tag} align=\"{al}\">"));
    } else {
        out.push_str(&format!("<{tag}>"));
    }
}

fn is_block_start(lines: &[&str], pos: usize, config: ParserConfig) -> bool {
    parse_setext_heading(lines, pos).is_some()
        || is_thematic_break(lines[pos])
        || parse_atx_heading(lines[pos]).is_some()
        || is_fence_start(lines[pos])
        || is_indented_code_line(lines[pos])
        || is_blockquote_line(lines[pos])
        || is_html_line(lines[pos])
        || parse_list_prefix(lines[pos]).is_some()
        || (config.enable_tables && is_table_header(lines, pos))
}

fn parse_task_item(item: &str) -> Option<(bool, &str)> {
    let trimmed = item.trim_start();
    if trimmed.len() < 4 || !trimmed.starts_with('[') {
        return None;
    }
    let close = trimmed.find(']')?;
    let marker = &trimmed[1..close];
    let checked = match marker.to_ascii_lowercase().as_str() {
        "x" => true,
        " " => false,
        _ => return None,
    };
    let rest = trimmed[close + 1..].trim_start();
    Some((checked, rest))
}

fn parse_link_definition(line: &str) -> Option<(&str, &str)> {
    if !line.starts_with('[') || line.starts_with("[^") {
        return None;
    }
    let close = line.find("]:")?;
    let id = line[1..close].trim();
    let url = line[close + 2..].trim();
    if id.is_empty() || url.is_empty() {
        return None;
    }
    Some((id, url))
}

fn parse_footnote_definition(line: &str) -> Option<(&str, &str)> {
    if !line.starts_with("[^") {
        return None;
    }
    let close = line.find("]:")?;
    let id = line[2..close].trim();
    let text = line[close + 2..].trim();
    if id.is_empty() {
        return None;
    }
    Some((id, text))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HardBreak {
    None,
    Spaces,
    Backslash,
}

fn detect_hard_break(text: &str, newline_idx: usize) -> HardBreak {
    if newline_idx == 0 {
        return HardBreak::None;
    }

    let bytes = text.as_bytes();
    let mut idx = newline_idx;
    let mut spaces = 0usize;
    while idx > 0 && bytes[idx - 1] == b' ' {
        spaces += 1;
        idx -= 1;
    }

    if spaces >= 2 {
        return HardBreak::Spaces;
    }
    if idx > 0 && bytes[idx - 1] == b'\\' {
        return HardBreak::Backslash;
    }
    HardBreak::None
}

fn trim_trailing_spaces(out: &mut String) {
    while out.ends_with(' ') {
        out.pop();
    }
}

fn parse_inline_link_target(after: &str) -> Option<(String, usize)> {
    if !after.starts_with('(') {
        return None;
    }
    let bytes = after.as_bytes();
    let mut i = 1usize;

    while i < bytes.len() && bytes[i].is_ascii_whitespace() {
        i += 1;
    }
    if i >= bytes.len() {
        return None;
    }

    let url_start = i;
    let url: String;

    if bytes[i] == b'<' {
        i += 1;
        let start = i;
        while i < bytes.len() && bytes[i] != b'>' {
            if bytes[i] == b'\n' {
                return None;
            }
            i += 1;
        }
        if i >= bytes.len() {
            return None;
        }
        url = after[start..i].to_string();
        i += 1;
    } else {
        let mut depth = 0usize;
        while i < bytes.len() {
            let ch = bytes[i] as char;
            if ch == '\\' && i + 1 < bytes.len() {
                i += 2;
                continue;
            }
            if ch == '(' {
                depth += 1;
                i += 1;
                continue;
            }
            if ch == ')' {
                if depth == 0 {
                    break;
                }
                depth -= 1;
                i += 1;
                continue;
            }
            if ch.is_ascii_whitespace() && depth == 0 {
                break;
            }
            i += 1;
        }
        if i <= url_start {
            return None;
        }
        url = after[url_start..i].to_string();
    }

    while i < bytes.len() && bytes[i].is_ascii_whitespace() {
        i += 1;
    }

    if i < bytes.len() && (bytes[i] == b'"' || bytes[i] == b'\'' || bytes[i] == b'(') {
        let quote = bytes[i];
        let closing = if quote == b'(' { b')' } else { quote };
        i += 1;
        while i < bytes.len() && bytes[i] != closing {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                i += 2;
            } else {
                i += 1;
            }
        }
        if i >= bytes.len() {
            return None;
        }
        i += 1;
        while i < bytes.len() && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
    }

    if i >= bytes.len() || bytes[i] != b')' {
        return None;
    }

    Some((url, i + 1))
}

fn parse_autolink_literal(text: &str) -> Option<(String, String, usize)> {
    if text.starts_with("https://") || text.starts_with("http://") {
        let link = parse_url_like_token(text)?;
        return Some((link.to_string(), link.to_string(), link.len()));
    }
    if text.starts_with("www.") {
        let link = parse_url_like_token(text)?;
        return Some((format!("http://{link}"), link.to_string(), link.len()));
    }
    if let Some((email, consumed)) = parse_email_literal(text) {
        return Some((format!("mailto:{email}"), email, consumed));
    }
    None
}

fn parse_url_like_token(text: &str) -> Option<&str> {
    let mut end = 0usize;
    for (idx, ch) in text.char_indices() {
        if ch.is_whitespace() || ch == '<' {
            break;
        }
        end = idx + ch.len_utf8();
    }
    if end == 0 {
        return None;
    }

    let mut link_end = end;
    while link_end > 0 {
        let ch = text[..link_end].chars().next_back().unwrap_or('\0');
        if matches!(ch, '.' | ',' | ';' | ':' | '!' | '?') {
            link_end -= ch.len_utf8();
        } else {
            break;
        }
    }
    if link_end == 0 {
        return None;
    }
    Some(&text[..link_end])
}

fn parse_email_literal(text: &str) -> Option<(String, usize)> {
    let mut end = 0usize;
    let mut at_pos: Option<usize> = None;

    for (idx, ch) in text.char_indices() {
        if ch.is_whitespace() || ch == '<' {
            break;
        }
        if ch == '@' {
            at_pos = Some(idx);
        }
        end = idx + ch.len_utf8();
    }

    if end == 0 {
        return None;
    }
    let mut candidate_end = end;
    while candidate_end > 0 {
        let ch = text[..candidate_end].chars().next_back().unwrap_or('\0');
        if matches!(ch, '.' | ',' | ';' | ':' | '!' | '?') {
            candidate_end -= ch.len_utf8();
        } else {
            break;
        }
    }
    if candidate_end == 0 {
        return None;
    }

    let candidate = &text[..candidate_end];
    let at = at_pos?;
    if at == 0 || at >= candidate.len() - 1 {
        return None;
    }

    let local = &candidate[..at];
    let domain = &candidate[at + 1..];
    if !is_email_local(local) || !is_email_domain(domain) {
        return None;
    }
    Some((candidate.to_string(), candidate_end))
}

fn is_email_local(local: &str) -> bool {
    !local.is_empty()
        && local.chars().all(|ch| {
            ch.is_ascii_alphanumeric()
                || matches!(
                    ch,
                    '!' | '#'
                        | '$'
                        | '%'
                        | '&'
                        | '\''
                        | '*'
                        | '+'
                        | '-'
                        | '/'
                        | '='
                        | '?'
                        | '^'
                        | '_'
                        | '`'
                        | '{'
                        | '|'
                        | '}'
                        | '~'
                        | '.'
                )
        })
}

fn is_email_domain(domain: &str) -> bool {
    if domain.is_empty() || !domain.contains('.') {
        return false;
    }
    for label in domain.split('.') {
        if label.is_empty() || label.starts_with('-') || label.ends_with('-') {
            return false;
        }
        if !label
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || ch == '-')
        {
            return false;
        }
    }
    true
}

fn parse_angle_autolink(text: &str) -> Option<(String, usize)> {
    if !text.starts_with('<') {
        return None;
    }
    let end = text.find('>')?;
    let inner = &text[1..end];
    if inner.starts_with("http://") || inner.starts_with("https://") {
        let esc = html_escape(inner);
        return Some((format!("<a href=\"{esc}\">{esc}</a>"), end + 1));
    }
    if inner.contains('@') && !inner.contains(' ') {
        let esc = html_escape(inner);
        return Some((format!("<a href=\"mailto:{esc}\">{esc}</a>"), end + 1));
    }
    None
}

fn parse_inline_html(text: &str) -> Option<(&str, usize)> {
    if !text.starts_with('<') {
        return None;
    }

    if text.starts_with("<!--") {
        let end = text.find("-->")?;
        return Some((&text[..end + 3], end + 3));
    }
    if text.starts_with("<?") {
        let end = text.find("?>")?;
        return Some((&text[..end + 2], end + 2));
    }
    if text.starts_with("<!") {
        let end = text.find('>')?;
        return Some((&text[..end + 1], end + 1));
    }

    let bytes = text.as_bytes();
    if bytes.len() < 3 {
        return None;
    }

    let mut i = 1usize;
    if bytes[i] == b'/' {
        i += 1;
    }

    let mut saw_alpha = false;
    while i < bytes.len() {
        let ch = bytes[i] as char;
        if ch.is_ascii_alphanumeric() || ch == '-' {
            saw_alpha = true;
            i += 1;
            continue;
        }
        break;
    }
    if !saw_alpha {
        return None;
    }

    while i < bytes.len() {
        if bytes[i] == b'>' {
            return Some((&text[..i + 1], i + 1));
        }
        if bytes[i] == b'\n' {
            return None;
        }
        i += 1;
    }
    None
}

fn parse_code_span(text: &str) -> Option<(&str, usize)> {
    let ticks = text.chars().take_while(|c| *c == '`').count();
    if ticks == 0 {
        return None;
    }
    let marker = "`".repeat(ticks);
    let rest = &text[ticks..];
    let end = rest.find(&marker)?;
    Some((&rest[..end], ticks + end + ticks))
}

fn parse_escaped_char(text: &str) -> Option<(char, usize)> {
    if !text.starts_with('\\') {
        return None;
    }
    let mut chars = text.chars();
    chars.next()?;
    let ch = chars.next()?;
    Some((ch, 1 + ch.len_utf8()))
}

fn parse_bracketed_label(text: &str) -> Option<(&str, usize)> {
    if !text.starts_with('[') {
        return None;
    }

    let bytes = text.as_bytes();
    let mut i = 1usize;
    let mut depth = 0usize;

    while i < bytes.len() {
        match bytes[i] {
            b'\\' => {
                i += 1;
                if i < bytes.len() {
                    i += 1;
                }
            }
            b'[' => {
                depth += 1;
                i += 1;
            }
            b']' => {
                if depth == 0 {
                    return Some((&text[1..i], i + 1));
                }
                depth -= 1;
                i += 1;
            }
            _ => i += 1,
        }
    }

    None
}

fn wrapped<'a>(text: &'a str, marker: &str) -> Option<(&'a str, usize)> {
    if !text.starts_with(marker) {
        return None;
    }
    if text.len() <= marker.len() * 2 {
        return None;
    }
    let tail = &text[marker.len()..];
    let end = tail.find(marker)?;
    if end == 0 {
        return None;
    }
    Some((&tail[..end], marker.len() + end + marker.len()))
}

fn normalize_key(text: &str) -> String {
    text.trim().to_ascii_lowercase()
}

fn footnote_id(key: &str) -> String {
    let mut out = String::with_capacity(key.len());
    for ch in key.chars() {
        if ch.is_ascii_alphanumeric() || ch == '-' || ch == '_' {
            out.push(ch);
        } else {
            out.push('-');
        }
    }
    out
}

fn push_escaped_char(out: &mut String, ch: char) {
    match ch {
        '&' => out.push_str("&amp;"),
        '<' => out.push_str("&lt;"),
        '>' => out.push_str("&gt;"),
        '"' => out.push_str("&quot;"),
        '\'' => out.push_str("&#39;"),
        _ => out.push(ch),
    }
}

fn html_escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for ch in text.chars() {
        push_escaped_char(&mut out, ch);
    }
    out
}

fn html_attr_escape(text: &str) -> String {
    html_escape(text)
}

#[cfg(test)]
mod tests {
    use super::{parse, parse_with_flavor, safe_parse, safe_parse_with_flavor, MarkdownFlavor};

    #[test]
    fn renders_table_in_gfm() {
        let md = "| a | b |\n|---|---|\n| 1 | 2 |";
        let html = parse(md);
        assert!(html.contains("<table>"));
        assert!(html.contains("<thead>"));
        assert!(html.contains("<tbody>"));
    }

    #[test]
    fn does_not_render_table_in_commonmark() {
        let md = "| a | b |\n|---|---|\n| 1 | 2 |";
        let html = parse_with_flavor(md, MarkdownFlavor::CommonMark);
        assert!(!html.contains("<table>"));
    }

    #[test]
    fn renders_strikethrough_only_in_gfm() {
        let gfm = parse_with_flavor("~~done~~", MarkdownFlavor::Gfm);
        let cm = parse_with_flavor("~~done~~", MarkdownFlavor::CommonMark);
        assert!(gfm.contains("<del>done</del>"));
        assert!(!cm.contains("<del>done</del>"));
    }

    #[test]
    fn renders_task_list_only_in_gfm() {
        let gfm = parse_with_flavor("- [x] finish", MarkdownFlavor::Gfm);
        let cm = parse_with_flavor("- [x] finish", MarkdownFlavor::CommonMark);
        assert!(gfm.contains("type=\"checkbox\""));
        assert!(!cm.contains("type=\"checkbox\""));
    }

    #[test]
    fn renders_autolink_literal_only_in_gfm() {
        let gfm = parse_with_flavor("visit https://example.com now", MarkdownFlavor::Gfm);
        let cm = parse_with_flavor("visit https://example.com now", MarkdownFlavor::CommonMark);
        assert!(gfm.contains("<a href=\"https://example.com\">https://example.com</a>"));
        assert!(!cm.contains("<a href=\"https://example.com\">https://example.com</a>"));
    }

    #[test]
    fn renders_footnotes_only_in_gfm() {
        let md = "note[^1]\n\n[^1]: footnote";
        let gfm = parse_with_flavor(md, MarkdownFlavor::Gfm);
        let cm = parse_with_flavor(md, MarkdownFlavor::CommonMark);
        assert!(gfm.contains("footnote-ref"));
        assert!(gfm.contains("footnotes"));
        assert!(!cm.contains("footnote-ref"));
    }

    #[test]
    fn renders_reference_links() {
        let md = "[Rust]\n\n[Rust]: https://www.rust-lang.org/";
        let html = parse(md);
        assert!(html.contains("<a href=\"https://www.rust-lang.org/\">Rust</a>"));
    }

    #[test]
    fn blocks_script_in_safe_parse() {
        let md = "<script>alert(1)</script>";
        assert!(safe_parse(md).is_err());
    }

    #[test]
    fn safe_parse_flavor_works() {
        let html = safe_parse_with_flavor("~~x~~", MarkdownFlavor::CommonMark).unwrap();
        assert!(!html.contains("<del>x</del>"));
    }

    #[test]
    fn renders_ordered_list_with_start() {
        let html = parse("3. three\n4. four");
        assert!(html.contains("<ol start=\"3\">"));
        assert!(html.contains("<li>three</li>"));
    }

    #[test]
    fn renders_nested_list() {
        let html = parse("- parent\n  - child\n- next");
        assert!(html.matches("<ul>").count() >= 2);
        assert!(html.contains("child"));
    }

    #[test]
    fn parses_link_with_title_and_parentheses() {
        let html = parse("[x](https://example.com/a_(b) \"title\")");
        assert!(html.contains("href=\"https://example.com/a_(b)\""));
    }

    #[test]
    fn renders_gfm_literal_www_and_email_autolinks() {
        let html = parse_with_flavor(
            "visit www.example.com or me@example.com",
            MarkdownFlavor::Gfm,
        );
        assert!(html.contains("href=\"http://www.example.com\""));
        assert!(html.contains("href=\"mailto:me@example.com\""));
    }

    #[test]
    fn renders_hard_line_breaks() {
        let html_spaces = parse("a  \nb");
        let html_backslash = parse("a\\\nb");
        assert!(html_spaces.contains("a<br />\nb"));
        assert!(html_backslash.contains("a<br />\nb"));
    }

    #[test]
    fn parse_preserves_inline_html_in_gfm_and_commonmark() {
        let cm = parse_with_flavor("x <span>y</span>", MarkdownFlavor::CommonMark);
        let gfm = parse_with_flavor("x <span>y</span>", MarkdownFlavor::Gfm);
        assert!(cm.contains("<span>y</span>"));
        assert!(gfm.contains("<span>y</span>"));
    }

    #[test]
    fn parse_preserves_html_block_in_gfm_and_commonmark() {
        let cm = parse_with_flavor("<div>\ninside\n</div>", MarkdownFlavor::CommonMark);
        let gfm = parse_with_flavor("<div>\ninside\n</div>", MarkdownFlavor::Gfm);
        assert!(cm.contains("<div>"));
        assert!(cm.contains("</div>"));
        assert!(gfm.contains("<div>"));
        assert!(gfm.contains("</div>"));
    }

    #[test]
    fn safe_parse_rejects_inline_html() {
        let cm = safe_parse_with_flavor("x <span>y</span>", MarkdownFlavor::CommonMark);
        let gfm = safe_parse_with_flavor("x <span>y</span>", MarkdownFlavor::Gfm);
        assert!(cm.is_err());
        assert!(gfm.is_err());
    }

    #[test]
    fn safe_parse_rejects_html_block() {
        let cm = safe_parse_with_flavor("<div>\ninside\n</div>", MarkdownFlavor::CommonMark);
        let gfm = safe_parse_with_flavor("<div>\ninside\n</div>", MarkdownFlavor::Gfm);
        assert!(cm.is_err());
        assert!(gfm.is_err());
    }

    #[test]
    fn supports_setext_heading_and_blockquote() {
        let html = parse("Title\n---\n\n> quote");
        assert!(html.contains("<h2>Title</h2>"));
        assert!(html.contains("<blockquote>"));
    }

    #[test]
    fn supports_table_alignment_in_gfm() {
        let md = "| a | b | c |\n| :-- | :-: | --: |\n| 1 | 2 | 3 |";
        let html = parse(md);
        assert!(html.contains("<th align=\"left\">a</th>"));
        assert!(html.contains("<th align=\"center\">b</th>"));
        assert!(html.contains("<th align=\"right\">c</th>"));
    }

    #[test]
    fn renders_mermaid_chart_in_gfm() {
        let md = "```mermaid\nflowchart TD\nA-->B\n```";
        let html = parse_with_flavor(md, MarkdownFlavor::Gfm);
        assert!(html.contains("<pre class=\"mermaid\">flowchart TD\nA--&gt;B</pre>"));
    }

    #[test]
    fn keeps_mermaid_as_code_in_commonmark() {
        let md = "```mermaid\nflowchart TD\nA-->B\n```";
        let html = parse_with_flavor(md, MarkdownFlavor::CommonMark);
        assert!(html
            .contains("<pre><code class=\"language-mermaid\">flowchart TD\nA--&gt;B</code></pre>"));
    }

    #[test]
    fn appends_mermaid_runtime_for_gfm_file_output() {
        let html = super::with_chart_runtime_if_needed(
            "<pre class=\"mermaid\">graph TD\nA--&gt;B</pre>\n".to_string(),
            MarkdownFlavor::Gfm,
        );
        assert!(html.contains("mermaid.min.js"));
        assert!(html.contains("mermaid.initialize({ startOnLoad: true })"));
    }

    #[test]
    fn does_not_append_mermaid_runtime_for_commonmark() {
        let html = super::with_chart_runtime_if_needed(
            "<pre><code class=\"language-mermaid\">graph TD\nA--&gt;B</code></pre>\n".to_string(),
            MarkdownFlavor::CommonMark,
        );
        assert!(!html.contains("mermaid.min.js"));
    }

    #[test]
    fn safe_parse_blocks_script_variants() {
        assert!(safe_parse("<script>alert(1)</script>").is_err());
        assert!(safe_parse("<ScRiPt src=x></ScRiPt>").is_err());
        assert!(safe_parse("< / script >").is_err());
        assert!(safe_parse("<  script>").is_err());
    }

    #[test]
    fn renders_link_wrapped_image_badge() {
        let md = "[![Telegram](https://img.shields.io/badge/Telegram-2CA5E0?logo=telegram&logoColor=white)](https://t.me/+Ka9i6CNwe71hMWQy)";
        let html = parse(md);
        assert!(html.contains(
            "<a href=\"https://t.me/+Ka9i6CNwe71hMWQy\"><img src=\"https://img.shields.io/badge/Telegram-2CA5E0?logo=telegram&amp;logoColor=white\" alt=\"Telegram\" /></a>"
        ));
    }

    #[test]
    fn renders_discord_and_telegram_badges_together() {
        let md = "![Discord](https://discord.gg/2xrMh7qX6m)⠀[![Telegram](https://img.shields.io/badge/Telegram-2CA5E0?logo=telegram&logoColor=white)](https://t.me/+Ka9i6CNwe71hMWQy)";
        let html = parse(md);
        assert!(html.contains("<img src=\"https://discord.gg/2xrMh7qX6m\" alt=\"Discord\" />"));
        assert!(html.contains(
            "<a href=\"https://t.me/+Ka9i6CNwe71hMWQy\"><img src=\"https://img.shields.io/badge/Telegram-2CA5E0?logo=telegram&amp;logoColor=white\" alt=\"Telegram\" /></a>"
        ));
    }
}
