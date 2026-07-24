//! `--fix`: apply the machine-applicable repairs carried by post-suppression
//! findings — insert PHPDoc docblocks/tags into the analyzed sources.
//!
//! All fixes for one declaration share a [`FixAnchor`]; they merge into a single
//! docblock (`@param` lines first, then `@return`, then `@var`). Application is
//! all-or-nothing per file: conflicting/overlapping edits, a file that changed
//! on disk since analysis, or a non-UTF-8 source (its lossy decode differs from
//! the disk bytes) skip the whole file — a wrong write is worse than a missed
//! fix.

use crate::Finding;
use php_diagnostics::{DocTagFix, FixAnchor};
use std::collections::HashMap;
use std::path::Path;

/// What [`apply_fixes`] did.
#[derive(Debug, Default)]
pub struct FixSummary {
    /// Findings whose fix was written.
    pub findings_fixed: usize,
    /// Files rewritten on disk.
    pub files_changed: usize,
    /// Paths rewritten (one per changed file; lets multi-round callers count
    /// unique files).
    pub changed_paths: Vec<String>,
    /// Files skipped (changed on disk / non-UTF-8 / conflicting edits), with
    /// the reason.
    pub files_skipped: Vec<(String, &'static str)>,
}

/// Apply every fix in `findings` (already post-suppression). `sources` maps the
/// findings' paths to the analyzed source text; `root` resolves those relative
/// paths on disk.
pub fn apply_fixes(
    findings: &[Finding],
    sources: &HashMap<String, String>,
    root: &Path,
) -> FixSummary {
    let mut by_file: HashMap<&str, Vec<&DocTagFix>> = HashMap::new();
    for f in findings {
        if let Some(fix) = &f.fix {
            by_file.entry(f.path.as_str()).or_default().push(fix);
        }
    }
    let mut summary = FixSummary::default();
    let mut paths: Vec<&&str> = by_file.keys().collect();
    paths.sort_unstable();
    for path in paths {
        let fixes = &by_file[*path];
        let Some(analyzed) = sources.get(*path) else {
            summary.files_skipped.push(((*path).to_string(), "source not retained"));
            continue;
        };
        let abs = root.join(*path);
        // The disk bytes must equal the analyzed source exactly — this one check
        // covers concurrent edits AND non-UTF-8 files (whose lossy decode is not
        // byte-identical to disk), so spans are valid and the write is lossless.
        match std::fs::read(&abs) {
            Ok(bytes) if bytes == analyzed.as_bytes() => {}
            Ok(_) => {
                summary
                    .files_skipped
                    .push(((*path).to_string(), "changed on disk or non-UTF-8"));
                continue;
            }
            Err(_) => {
                summary.files_skipped.push(((*path).to_string(), "unreadable"));
                continue;
            }
        }
        let Some(rewritten) = apply_to_source(analyzed, fixes) else {
            summary
                .files_skipped
                .push(((*path).to_string(), "conflicting edits"));
            continue;
        };
        if std::fs::write(&abs, &rewritten).is_err() {
            summary.files_skipped.push(((*path).to_string(), "write failed"));
            continue;
        }
        summary.findings_fixed += fixes.len();
        summary.files_changed += 1;
        summary.changed_paths.push((*path).to_string());
    }
    summary
}

/// Apply `fixes` to one file's source. Pure; `None` when any materialized edits
/// would overlap (apply nothing for the file rather than guess).
pub(crate) fn apply_to_source(source: &str, fixes: &[&DocTagFix]) -> Option<String> {
    let eol = if source.contains("\r\n") { "\r\n" } else { "\n" };

    // Group by anchor; each group becomes one edit. Keyed on the anchor's
    // byte position; the group keeps the first-seen anchor/indent.
    let mut groups: Vec<(&DocTagFix, Vec<&DocTagFix>)> = Vec::new();
    for fix in fixes {
        match groups.iter_mut().find(|(g, _)| g.anchor == fix.anchor) {
            Some((_, members)) => members.push(fix),
            None => groups.push((fix, vec![fix])),
        }
    }

    let mut edits: Vec<(u32, u32, String)> = Vec::new();
    for (head, mut members) in groups {
        // Param < Return < Var; stable, so same-kind tags keep emission order
        // (the parameter rule emits in declaration order).
        members.sort_by_key(|f| f.kind);
        // The same tag suggested twice for one declaration is a conflict.
        let mut tags: Vec<&str> = members.iter().map(|f| f.tag.as_str()).collect();
        tags.dedup();
        let indent = &head.indent;
        match &head.anchor {
            FixAnchor::NewDocAt(off) => {
                let block = if let [tag] = tags[..] {
                    format!("{indent}/** {tag} */{eol}")
                } else {
                    let mut b = format!("{indent}/**{eol}");
                    for tag in &tags {
                        b.push_str(&format!("{indent} * {tag}{eol}"));
                    }
                    b.push_str(&format!("{indent} */{eol}"));
                    b
                };
                edits.push((*off, *off, block));
            }
            FixAnchor::ExistingDoc(span) => {
                let doc = source.get(span.start as usize..span.end as usize)?;
                let rewritten = insert_tags_into_doc(doc, &tags, indent, eol)?;
                edits.push((span.start, span.end, rewritten));
            }
        }
    }

    // Apply back-to-front. Two inserts at the same offset (or any overlap)
    // would be ambiguous — treat as a conflict.
    edits.sort_by_key(|(start, _, _)| *start);
    if edits
        .windows(2)
        .any(|w| w[0].0 == w[1].0 || w[0].1 > w[1].0)
    {
        return None;
    }
    let mut out = source.to_string();
    for (start, end, text) in edits.into_iter().rev() {
        out.replace_range(start as usize..end as usize, &text);
    }
    Some(out)
}

/// Add `tags` to an existing docblock, before its closing `*/`. A single-line
/// `/** body */` is expanded to a multi-line block; a multi-line block gets
/// `* @tag` lines above the closing line, using that line's own indentation.
fn insert_tags_into_doc(doc: &str, tags: &[&str], indent: &str, eol: &str) -> Option<String> {
    if !doc.starts_with("/**") || !doc.ends_with("*/") {
        return None;
    }
    if let Some((before_close, _)) = doc.rsplit_once('\n') {
        // Multi-line: re-use the closing line's leading whitespace for the new
        // tag lines (it aligns the existing ` * ` column, tabs included).
        let close_line = &doc[before_close.len() + 1..];
        let close_ws = &close_line[..close_line.len() - close_line.trim_start().len()];
        let mut out = String::with_capacity(doc.len() + tags.len() * 32);
        out.push_str(before_close);
        for tag in tags {
            out.push_str(eol);
            out.push_str(close_ws);
            out.push_str("* ");
            out.push_str(tag);
        }
        out.push_str(eol);
        out.push_str(close_line);
        Some(out)
    } else {
        // Single line `/** body */` → multi-line with the body preserved.
        let body = doc["/**".len()..doc.len() - "*/".len()].trim();
        let mut out = format!("/**{eol}");
        if !body.is_empty() {
            out.push_str(&format!("{indent} * {body}{eol}"));
        }
        for tag in tags {
            out.push_str(&format!("{indent} * {tag}{eol}"));
        }
        out.push_str(&format!("{indent} */"));
        Some(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_diagnostics::DocTagKind;
    use php_span::Span;

    fn fix(anchor: FixAnchor, kind: DocTagKind, tag: &str, indent: &str) -> DocTagFix {
        DocTagFix {
            anchor,
            kind,
            tag: tag.to_string(),
            indent: indent.to_string(),
        }
    }

    #[test]
    fn single_tag_inserts_single_line_block() {
        let src = "<?php\nclass C {\n    public function f() {}\n}\n";
        let off = src.find("    public").unwrap() as u32;
        let f = fix(FixAnchor::NewDocAt(off), DocTagKind::Return, "@return int", "    ");
        let out = apply_to_source(src, &[&f]).unwrap();
        assert_eq!(
            out,
            "<?php\nclass C {\n    /** @return int */\n    public function f() {}\n}\n"
        );
    }

    #[test]
    fn params_and_return_merge_into_one_block_in_order() {
        let src = "<?php\nclass C {\n    public function f($a, $b) {}\n}\n";
        let off = src.find("    public").unwrap() as u32;
        // Deliberately emitted out of order: return first, then params.
        let r = fix(FixAnchor::NewDocAt(off), DocTagKind::Return, "@return int", "    ");
        let a = fix(FixAnchor::NewDocAt(off), DocTagKind::Param, "@param string $a", "    ");
        let b = fix(FixAnchor::NewDocAt(off), DocTagKind::Param, "@param bool $b", "    ");
        let out = apply_to_source(src, &[&r, &a, &b]).unwrap();
        assert_eq!(
            out,
            "<?php\nclass C {\n    /**\n     * @param string $a\n     * @param bool $b\n     * @return int\n     */\n    public function f($a, $b) {}\n}\n"
        );
    }

    #[test]
    fn inserts_into_existing_multiline_doc() {
        let src = "<?php\n/**\n * Does things.\n */\nfunction f() {}\n";
        let doc = "/**\n * Does things.\n */";
        let at = src.find(doc).unwrap() as u32;
        let f = fix(
            FixAnchor::ExistingDoc(Span::new(at, at + doc.len() as u32)),
            DocTagKind::Return,
            "@return int",
            "",
        );
        let out = apply_to_source(src, &[&f]).unwrap();
        assert_eq!(
            out,
            "<?php\n/**\n * Does things.\n * @return int\n */\nfunction f() {}\n"
        );
    }

    #[test]
    fn expands_single_line_doc() {
        let src = "<?php\nclass C {\n    /** Hi. */\n    public function f() {}\n}\n";
        let at = src.find("/** Hi. */").unwrap() as u32;
        let f = fix(
            FixAnchor::ExistingDoc(Span::new(at, at + 10)),
            DocTagKind::Return,
            "@return int",
            "    ",
        );
        let out = apply_to_source(src, &[&f]).unwrap();
        assert_eq!(
            out,
            "<?php\nclass C {\n    /**\n     * Hi.\n     * @return int\n     */\n    public function f() {}\n}\n"
        );
    }

    #[test]
    fn tab_indentation_is_preserved() {
        let src = "<?php\nclass C {\n\tpublic function f() {}\n}\n";
        let off = src.find("\tpublic").unwrap() as u32;
        let f = fix(FixAnchor::NewDocAt(off), DocTagKind::Return, "@return int", "\t");
        let out = apply_to_source(src, &[&f]).unwrap();
        assert_eq!(
            out,
            "<?php\nclass C {\n\t/** @return int */\n\tpublic function f() {}\n}\n"
        );
    }

    #[test]
    fn crlf_files_get_crlf_blocks() {
        let src = "<?php\r\nfunction f() {}\r\n";
        let off = src.find("function").unwrap() as u32;
        let f = fix(FixAnchor::NewDocAt(off), DocTagKind::Return, "@return int", "");
        let out = apply_to_source(src, &[&f]).unwrap();
        assert_eq!(out, "<?php\r\n/** @return int */\r\nfunction f() {}\r\n");
    }

    #[test]
    fn multiple_declarations_apply_back_to_front() {
        let src = "<?php\nfunction a() {}\nfunction b() {}\n";
        let a_off = src.find("function a").unwrap() as u32;
        let b_off = src.find("function b").unwrap() as u32;
        let fa = fix(FixAnchor::NewDocAt(a_off), DocTagKind::Return, "@return int", "");
        let fb = fix(FixAnchor::NewDocAt(b_off), DocTagKind::Return, "@return bool", "");
        let out = apply_to_source(src, &[&fa, &fb]).unwrap();
        assert_eq!(
            out,
            "<?php\n/** @return int */\nfunction a() {}\n/** @return bool */\nfunction b() {}\n"
        );
    }

    #[test]
    fn overlapping_edits_conflict() {
        // Two distinct ExistingDoc anchors overlapping byte ranges → None.
        let src = "<?php\n/** a */\nfunction f() {}\n";
        let at = src.find("/** a */").unwrap() as u32;
        let f1 = fix(
            FixAnchor::ExistingDoc(Span::new(at, at + 8)),
            DocTagKind::Return,
            "@return int",
            "",
        );
        let f2 = fix(
            FixAnchor::ExistingDoc(Span::new(at + 1, at + 8)),
            DocTagKind::Var,
            "@var int",
            "",
        );
        assert_eq!(apply_to_source(src, &[&f1, &f2]), None);
    }

    #[test]
    fn duplicate_tags_for_one_anchor_dedup() {
        let src = "<?php\nfunction f() {}\n";
        let off = src.find("function").unwrap() as u32;
        let f1 = fix(FixAnchor::NewDocAt(off), DocTagKind::Return, "@return int", "");
        let f2 = fix(FixAnchor::NewDocAt(off), DocTagKind::Return, "@return int", "");
        let out = apply_to_source(src, &[&f1, &f2]).unwrap();
        assert_eq!(out, "<?php\n/** @return int */\nfunction f() {}\n");
    }
}
