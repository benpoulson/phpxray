//! Pipeline stages shared by the batch engine and the incremental
//! [`Session`](crate::incremental::Session).
//!
//! The two engines differ in *orchestration*, and legitimately so: the batch
//! engine makes one pass over freshly parsed files, while the Session reuses
//! cached per-file artifacts and computes an invalidation set. But several
//! stages compute exactly the same thing from the same inputs, and those had
//! been written twice — which is how `laravelAliases` came to be registered in
//! one engine and not the other.
//!
//! What stays engine-specific is only how *project* files reach the indexes
//! (parsed programs vs cached artifacts). Everything downstream of that —
//! stub indexing, alias registration, index finalization, and the
//! signature-inference pre-pass — lives here.

use php_index::ProjectIndex;
use php_intern::Interner;
use php_reflect::ReflectionIndex;
use std::collections::HashMap;

/// Index the configured stub files.
///
/// Stubs go in **last** and are the one source allowed to override a project
/// declaration (see `php_reflect::reflect_stub_artifact`), so both engines must
/// call this after their project files are indexed.
pub(crate) fn index_stubs(
    project: &mut ProjectIndex,
    reflection: &mut ReflectionIndex,
    interner: &Interner,
    stub_programs: &[(String, php_ast::Program)],
) {
    for (path, program) in stub_programs {
        let file_index = php_resolve::index_file(program, interner);
        let artifact = php_reflect::reflect_stub_artifact(Some(path), program, interner);
        project.add_file_as(path, &file_index, php_index::SourceKind::Scan);
        reflection.add_artifact(&artifact);
    }
}

/// Index one parsed project file into both indexes.
///
/// A file's `analyze` flag picks Analyzed-vs-Scan provenance (scan-only sources
/// must not shadow curated builtins), and a configured stub file takes the
/// override path. The batch engine calls this per parsed file; the Session
/// replays cached artifacts instead, which is the one stage that genuinely
/// cannot be shared.
pub(crate) fn index_parsed_file(
    project: &mut ProjectIndex,
    reflection: &mut ReflectionIndex,
    interner: &Interner,
    path: &str,
    program: &php_ast::Program,
    analyze: bool,
    stub: bool,
) {
    let project_kind = if analyze {
        php_index::SourceKind::Analyzed
    } else {
        php_index::SourceKind::Scan
    };
    project.add_file_as(
        path,
        &php_resolve::index_file(program, interner),
        project_kind,
    );
    if stub {
        // The one source allowed to override an earlier project declaration.
        reflection.add_artifact(&php_reflect::reflect_stub_artifact(
            Some(path),
            program,
            interner,
        ));
        return;
    }
    let reflect_kind = if analyze {
        php_reflect::SourceKind::Analyzed
    } else {
        php_reflect::SourceKind::Scan
    };
    reflection.add_file_labeled_as(Some(path), program, interner, reflect_kind);
}

/// Register the Laravel facade aliases as known classes.
///
/// Must run **after** every real declaration: `ProjectIndex::add_alias` never
/// overwrites, so a genuine class of the same name always wins.
pub(crate) fn register_facade_aliases(project: &mut ProjectIndex, aliases: &[(String, String)]) {
    for (alias, target) in aliases {
        project.add_alias(alias, target);
    }
}

/// Finish index construction once every class is present.
///
/// Order matters: cross-class `@phpstan-import-type` resolution needs the whole
/// index, and global `typeAliases` expansion then rewrites the resolved types.
pub(crate) fn finalize_indexes(
    reflection: &mut ReflectionIndex,
    type_aliases: &std::collections::BTreeMap<String, String>,
) {
    reflection.resolve_type_imports();
    let owned: HashMap<String, String> = type_aliases.clone().into_iter().collect();
    reflection.apply_global_type_aliases(&owned);
}

/// The whole-project untyped-signature inference pre-pass.
///
/// Folds inferred signatures into `reflection` so all downstream
/// inference/rules see them, and returns them so the incremental engine can
/// diff against the previous pass (a call-site edit in one file can change
/// another file's *inferred* signature without touching it).
/// [`infer_signatures`] over evidence the caller harvested itself.
///
/// The streaming engine cannot hand over every `Program` at once, so it collects
/// call-site evidence batch by batch and finishes here. Both entry points build
/// the same [`php_infer::InferOpts`] for the same reason the rest of this module
/// exists: an option that reached one engine and not the other is the bug shape
/// §8i of CLAUDE.md documents.
pub(crate) fn infer_signatures_from_evidence(
    reflection: &mut ReflectionIndex,
    evidence: php_infer::CallSiteEvidence,
    interner: &Interner,
    terminators: std::sync::Arc<php_rules::Terminators>,
) -> php_reflect::InferredSignatures {
    php_infer::infer_and_apply_from_evidence(
        reflection,
        evidence,
        interner,
        php_infer::InferOpts {
            terminators,
            ..php_infer::InferOpts::default()
        },
    )
}

pub(crate) fn infer_signatures(
    reflection: &mut ReflectionIndex,
    programs: &[&php_ast::Program],
    interner: &Interner,
    terminators: std::sync::Arc<php_rules::Terminators>,
) -> php_reflect::InferredSignatures {
    php_infer::infer_and_apply(
        reflection,
        programs,
        interner,
        php_infer::InferOpts {
            // The same terminator set the rules run with: an analysis input that
            // reached one consumer and not the other is the shape
            // `AnalysisInputs` exists to prevent.
            terminators,
            ..php_infer::InferOpts::default()
        },
    )
}
