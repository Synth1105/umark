use regex::Regex;
use std::collections::HashMap;
use std::error::Error;
use std::fs;
use tree_sitter::{Language, Node, Parser};

/// 마크다운 문자열을 HTML로 변환합니다.
pub fn parse(input: &str) -> String {
    let mut stash: HashMap<String, String> = HashMap::new();
    let mut index: usize = 0;

    // 1. 코드 블록 보호 (Tree-sitter 하이라이팅 적용)
    let mut result = protect_code_blocks(input, &mut stash, &mut index);

    // 2. 전체 텍스트를 "빈 줄" 단위로 나누어 블록(Block) 생성
    let blocks: Vec<&str> = result.split("\n\n").collect();
    let mut html_blocks = Vec::new();

    for block in blocks {
        let trimmed = block.trim();
        if trimmed.is_empty() { continue; }

        // 보호된 코드 블록 토큰인 경우 그대로 유지
        if trimmed.starts_with("@@CODEBLOCK") {
            html_blocks.push(trimmed.to_string());
            continue;
        }

        // 블록 타입 판별 및 변환
        html_blocks.push(process_block(trimmed));
    }

    result = html_blocks.join("\n");

    // 3. 보호된 코드 블록 복원
    for i in (0..index).rev() {
        let token = format!("@@CODEBLOCK{}@@", i);
        if let Some(html) = stash.get(&token) {
            result = result.replace(&token, html);
        }
    }

    result
}

/// 각 블록(단락, 제목, 리스트 등)을 판별하여 내부 인라인 요소를 처리합니다.
fn process_block(block: &str) -> String {
    let first_line = block.lines().next().unwrap_or("");

    // 1. 제목 (#)
    if first_line.starts_with('#') {
        let re = Regex::new(r"^(#{1,6})\s+(.*)$").unwrap();
        if let Some(caps) = re.captures(first_line) {
            let level = caps[1].len();
            return format!("<h{}>{}</h{}>", level, parse_inline(&caps[2]), level);
        }
    }

    // 2. 수평선 (---)
    if block == "---" {
        return "<hr>".to_string();
    }

    // 3. 인용구 (>)
    if first_line.starts_with("> ") {
        let content: String = block.lines()
            .map(|l| if l.starts_with("> ") { &l[2..] } else { l })
            .collect::<Vec<_>>().join(" ");
        return format!("<blockquote>{}</blockquote>", parse_inline(&content));
    }

    // 4. 리스트 (단순 리스트 처리)
    if first_line.starts_with("* ") || first_line.starts_with("- ") {
        let items: String = block.lines()
            .map(|l| format!("<li>{}</li>", parse_inline(&l[2..])))
            .collect::<Vec<_>>().join("");
        return format!("<ul>{}</ul>", items);
    }

    // 5. 일반 단락 (Paragraph) - 가장 흔한 케이스
    // 줄바꿈으로 나뉜 문장들을 하나로 합쳐서 인라인 파싱을 돌립니다.
    let paragraph_content = block.lines().collect::<Vec<_>>().join(" ");
    format!("<p>{}</p>", parse_inline(&paragraph_content))
}

/// 문장 내부의 인라인 요소(링크, 강조, 이미지)를 파싱합니다.
fn parse_inline(text: &str) -> String {
    let mut result = text.to_string();

    // 인라인 코드 (`)
    let inline_code = Regex::new(r"`([^`]+)`").unwrap();
    result = inline_code.replace_all(&result, "<code>$1</code>").to_string();

    // 이미지 (![alt](url)) - 링크보다 먼저 처리
    let img_re = Regex::new(r"!\[([^\]]*)\]\(([^\)]+)\)").unwrap();
    result = img_re.replace_all(&result, r#"<img src="$2" alt="$1">"#).to_string();

    // 링크 ([text](url)) - 말씀하신 "URL과 텍스트가 섞인 경우"를 처리
    // Regex를 더 엄격하게 [^\]] 등으로 지정하여 경계를 명확히 합니다.
    let link_re = Regex::new(r"\[([^\]]+)\]\(([^\)]+)\)").unwrap();
    result = link_re.replace_all(&result, r#"<a href="$2">$1</a>"#).to_string();

    // 굵게+기울임 (***)
    let bi = Regex::new(r"\*\*\*(.*?)\*\*\*").unwrap();
    result = bi.replace_all(&result, "<strong><em>$1</em></strong>").to_string();

    // 굵게 (**)
    let b = Regex::new(r"\*\*(.*?)\*\*").unwrap();
    result = b.replace_all(&result, "<strong>$1</strong>").to_string();

    // 기울임 (*)
    let i = Regex::new(r"\*(.*?)\*").unwrap();
    result = i.replace_all(&result, "<em>$1</em>").to_string();

    result
}

// ===============================
// Tree-sitter & 유틸리티 로직 (생략 없이 유지)
// ===============================

fn protect_code_blocks(input: &str, stash: &mut HashMap<String, String>, index: &mut usize) -> String {
    let re = Regex::new(r"(?s)```(\w*)\s*\n(.*?)```").unwrap();
    re.replace_all(input, |caps: &regex::Captures| {
        let lang = caps.get(1).map_or("", |m| m.as_str()).to_lowercase();
        let code = caps.get(2).map_or("", |m| m.as_str());
        let token = format!("@@CODEBLOCK{}@@", index);

        let highlighted = if lang.is_empty() {
            format!("<pre><code>{}</code></pre>", html_escape(code))
        } else {
            match highlight_code(&lang, code) {
                Ok(html) => format!("<pre><code class=\"language-{}\">{}</code></pre>", lang, html),
                Err(_) => format!("<pre><code>{}</code></pre>", html_escape(code)),
            }
        };

        stash.insert(token.clone(), highlighted);
        *index += 1;
        token
    }).to_string()
}

fn highlight_code(lang: &str, code: &str) -> Result<String, Box<dyn Error>> {
    let language = get_language(lang)?;
    let mut parser = Parser::new();
    parser.set_language(&language)?;
    let tree = parser.parse(code, None).ok_or("Parse failed")?;
    let mut highlighted = String::new();
    let mut last_end = 0;
    highlight_node(tree.root_node(), code, &mut last_end, &mut highlighted);
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
        "comment" | "line_comment" => "comment",
        "keyword" | "fn" | "let" | "pub" | "struct" | "match" => "keyword",
        "function" | "identifier" => "function",
        "string" => "string",
        "number" => "number",
        _ => "",
    };
    if !class.is_empty() && node.child_count() == 0 {
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
    }
}

fn html_escape(text: &str) -> String {
    text.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
}

pub fn parse_from_file(path: &str, output_path: &str) -> Result<(), Box<dyn Error>> {
    let content = fs::read_to_string(path)?;
    fs::write(output_path, parse(&content))?;
    Ok(())
}
