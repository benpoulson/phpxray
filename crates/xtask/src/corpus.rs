//! Shared `.phpt` corpus traversal.

use crate::phpt;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

#[derive(Debug, Clone)]
pub struct PhptCase {
    pub path: PathBuf,
    pub label: String,
    pub text: String,
    pub source: String,
    pub expects_parse_error: bool,
}

pub fn phpt_cases(dir: &Path) -> Vec<PhptCase> {
    let mut paths: Vec<PathBuf> = WalkDir::new(dir)
        .into_iter()
        .filter_map(Result::ok)
        .map(|e| e.into_path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("phpt"))
        .collect();
    paths.sort();

    paths
        .into_iter()
        .filter_map(|path| {
            let text = std::fs::read_to_string(&path).ok()?;
            let source = phpt::extract_file_section(&text)?;
            let expects_parse_error = phpt::expects_parse_error(&text);
            let label = path.display().to_string();
            Some(PhptCase {
                path,
                label,
                text,
                source,
                expects_parse_error,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn cases_are_sorted_and_extract_metadata() {
        let dir = std::env::temp_dir().join(format!("php_ast_xtask_corpus_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        fs::write(
            dir.join("b.phpt"),
            "--FILE--\n<?php echo 'b';\n--EXPECT--\nb\n",
        )
        .unwrap();
        fs::write(
            dir.join("a.phpt"),
            "--FILE--\n<?php /*\n--EXPECTF--\nParse error: nope\n",
        )
        .unwrap();

        let cases = phpt_cases(&dir);
        assert_eq!(cases.len(), 2);
        assert!(cases[0].label.ends_with("a.phpt"));
        assert!(cases[0].expects_parse_error);
        assert_eq!(cases[1].source, "<?php echo 'b';");

        let _ = fs::remove_dir_all(&dir);
    }
}
