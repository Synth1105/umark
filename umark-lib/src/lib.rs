//! # umark-lib
//! Full-featured library version of umark.
//! Supports Headings, Links, Images, Lists, Blockquotes, and Syntax Highlighting.

use std::error::Error;
use regex::Regex;
use tree_sitter::{Language, Node, Parser};
use std::fs::{read_to_string, write};
pub fn parse(markdown: &str) -> Result<String, Box<dyn Error>> {
    let mut result = markdown.to_string();

    // 1. Code Block (Priority 1: Should not be parsed by other rules)
    let code_block_re = Regex::new(r"(?s)```(\w*)\s*\n(.*?)```")?;
    result = code_block_re.replace_all(&result, |caps: &regex::Captures| {
        let lang = caps.get(1).map_or("", |m| m.as_str()).to_lowercase();
        let code = caps.get(2).map_or("", |m| m.as_str());

        if lang.is_empty() {
            return format!("<pre><code>{}</code></pre>", html_escape(code));
        }

        match highlight_code(&lang, code) {
            Ok(html) => format!("<pre><code class=\"language-{}\">{}</code></pre>", lang, html),
            Err(_) => format!("<pre><code>{}</code></pre>", html_escape(code))
        }
    }).to_string();

    // 2. Headings (# h1, ## h2, ...)
    for i in (1..=6).rev() {
        let pattern = format!(r"(?m)^{} (.+)$", "#".repeat(i));
        let re = Regex::new(&pattern)?;
        result = re.replace_all(&result, format!("<h{}>$1</h{}>", i, i)).to_string();
    }

    // 3. Images (![alt](url))
    let img_re = Regex::new(r"!\[(.*?)\]\((.*?)\)")?;
    result = img_re.replace_all(&result, "<img src=\"$2\" alt=\"$1\">").to_string();

    // 4. Links ([text](url))
    let link_re = Regex::new(r"\[(.*?)\]\((.*?)\)")?;
    result = link_re.replace_all(&result, "<a href=\"$2\">$1</a>").to_string();

    // 5. Blockquotes (> text)
    let quote_re = Regex::new(r"(?m)^> (.*)$")?;
    result = quote_re.replace_all(&result, "<blockquote>$1</blockquote>").to_string();

    // 6. Horizontal Rules (---)
    let hr_re = Regex::new(r"(?m)^---$")?;
    result = hr_re.replace_all(&result, "<hr>").to_string();

    // 7. Inline Formatting (Bold, Italic, Strike)
    let bold_italic = Regex::new(r"\*\*\*(.+?)\*\*\*")?;
    result = bold_italic.replace_all(&result, "<strong><i>$1</i></strong>").to_string();

    let bold = Regex::new(r"\*\*(.+?)\*\*")?;
    result = bold.replace_all(&result, "<strong>$1</strong>").to_string();

    let line = Regex::new(r"~~(.+?)~~")?;
    result = line.replace_all(&result, "<s>$1</s>").to_string();

    let italic = Regex::new(r"\*(.+?)\*")?;
    result = italic.replace_all(&result, "<i>$1</i>").to_string();

    // 8. Simple Unordered Lists (* item or - item)
    let list_re = Regex::new(r"(?m)^[\*\-] (.*)$")?;
    result = list_re.replace_all(&result, "<li>$1</li>").to_string();
    // Wrap consecutive <li> tags in <ul> (Simplified logic)
    let ul_fix = Regex::new(r"(<li>.*</li>)")?; // Note: In a real parser, this needs state tracking
    
    Ok(result)
}

fn parse_to_file( md_file:&str , html_file:&str ) -> Result<() , Box<dyn Error>>{
    let md = read_to_string(md_file)?;
    let html = parse(md)?;
    write(&html_file , html)?;
    ()
}

fn highlight_code(lang: &str, code: &str) -> Result<String, Box<dyn Error>> {
    let language = get_language(lang)?;
    let mut parser = Parser::new();
    parser.set_language(&language)?;
    let tree = parser.parse(code, None).ok_or("Parse failed")?;
    let root = tree.root_node();
    let mut highlighted = String::new();
    let mut last_end = 0;
    highlight_node(root, code, &mut last_end, &mut highlighted);
    if last_end < code.len() {
        highlighted.push_str(&html_escape(&code[last_end..]));
    }
    Ok(highlighted)
}

fn get_language(lang: &str) -> Result<Language, Box<dyn Error>> {
    Ok(match lang {
        "rust" | "rs" => tree_sitter_rust::LANGUAGE.into(),
        "js" | "javascript" => tree_sitter_javascript::LANGUAGE.into(),
        "python" | "py" => tree_sitter_python::LANGUAGE.into(),
        "html" => tree_sitter_html::LANGUAGE.into(),
        "c" => tree_sitter_c::LANGUAGE.into(),
        "cpp" | "c++" => tree_sitter_cpp::LANGUAGE.into(),
        "go" => tree_sitter_go::LANGUAGE.into(),
        "ruby" | "rb" => tree_sitter_ruby::LANGUAGE.into(),
        "java" => tree_sitter_java::LANGUAGE.into(),
        _ => return Err("Unsupported language".into()),
    })
}

fn highlight_node(node: Node, source: &str, last_end: &mut usize, output: &mut String) {
    let start = node.start_byte();
    let end = node.end_byte();
    if start > *last_end {
        output.push_str(&html_escape(&source[*last_end..start]));
        *last_end = start;
    }
    let kind = node.kind();
    let class = match kind {
        "comment" | "line_comment" | "block_comment" => "comment",
        "keyword" | "fn" | "let" | "use" | "mod" | "pub" | "struct" | "enum" | "match" => "keyword",
        "function" | "function_item" | "identifier" | "call_expression" => "function",
        "string" | "string_literal" => "string",
        "number" | "integer_literal" | "float_literal" => "number",
        "type_identifier" | "primitive_type" => "type",
        _ => "",
    };
    if !class.is_empty() && (node.child_count() == 0 || kind == "string" || kind == "comment") {
        output.push_str(&format!("<span class=\"h-{}\">{}</span>", class, html_escape(&source[start..end])));
        *last_end = end;
    } else {
        let mut cursor = node.walk();
        if cursor.goto_first_child() {
            loop {
                highlight_node(cursor.node(), source, last_end, output);
                if !cursor.goto_next_sibling() { break; }
            }
        }
        if node.child_count() == 0 && end > *last_end {
            output.push_str(&html_escape(&source[*last_end..end]));
            *last_end = end;
        }
    }
}

fn html_escape(text: &str) -> String {
    text.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_parse_complex_markdown() {
        let md = "# Title\nThis is [link](https://google.com)\n> quote\n---";
        let html = parse(md).unwrap();
        assert!(html.contains("<h1>Title</h1>"));
        assert!(html.contains("<a href=\"https://google.com\">link</a>"));
        assert!(html.contains("<blockquote>quote</blockquote>"));
        assert!(html.contains("<hr>"));
    }
}
