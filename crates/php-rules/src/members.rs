//! Shared call/member resolution for rules.

use crate::{symbols, FileAnalysis};
use php_reflect::{Found, FunctionReflection, MethodReflection, PropertyReflection};
use php_resolve::{Resolution, ResolvedRef};
use php_types::Type;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ResolveStatus<T> {
    Known(T),
    Unknown,
    Opaque,
    Skipped,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FunctionTarget {
    pub target_fqn: String,
    pub called_fqn: String,
    pub canonical_fqn: String,
    pub display_name: String,
}

pub(crate) struct CallResolver<'a> {
    fa: &'a FileAnalysis<'a>,
}

impl<'a> CallResolver<'a> {
    pub(crate) fn new(fa: &'a FileAnalysis<'a>) -> Self {
        Self { fa }
    }

    pub(crate) fn function(&self, r: &ResolvedRef) -> ResolveStatus<FunctionTarget> {
        let display_name = primary_name(r);
        match &r.resolution {
            Resolution::Fqn(fqn) => self
                .fa
                .project
                .function(fqn)
                .map(|entry| {
                    ResolveStatus::Known(FunctionTarget {
                        target_fqn: fqn.clone(),
                        called_fqn: fqn.clone(),
                        canonical_fqn: entry.fqn.clone(),
                        display_name: display_name.clone(),
                    })
                })
                .unwrap_or(ResolveStatus::Unknown),
            Resolution::Fallback { namespaced, global } => {
                if let Some(entry) = self.fa.project.function(namespaced) {
                    ResolveStatus::Known(FunctionTarget {
                        target_fqn: namespaced.clone(),
                        called_fqn: namespaced.clone(),
                        canonical_fqn: entry.fqn.clone(),
                        display_name,
                    })
                } else if let Some(entry) = self.fa.project.function(global) {
                    ResolveStatus::Known(FunctionTarget {
                        target_fqn: global.clone(),
                        called_fqn: global.clone(),
                        canonical_fqn: entry.fqn.clone(),
                        display_name,
                    })
                } else {
                    ResolveStatus::Unknown
                }
            }
            _ => ResolveStatus::Opaque,
        }
    }

    pub(crate) fn reflected_function(
        &self,
        r: &ResolvedRef,
    ) -> Option<(String, &FunctionReflection)> {
        match &r.resolution {
            Resolution::Fqn(fqn) => self.fa.reflection.function(fqn).map(|f| (fqn.clone(), f)),
            Resolution::Fallback { namespaced, global } => self
                .fa
                .reflection
                .function(namespaced)
                .map(|f| (namespaced.clone(), f))
                .or_else(|| {
                    self.fa
                        .reflection
                        .function(global)
                        .map(|f| (global.clone(), f))
                }),
            _ => None,
        }
    }

    pub(crate) fn known_function_fqn<'r>(&self, r: &'r ResolvedRef) -> Option<&'r str> {
        match self.function(r) {
            ResolveStatus::Known(target) => Some(match &r.resolution {
                Resolution::Fqn(fqn) => fqn.as_str(),
                Resolution::Fallback { namespaced, global } => {
                    if symbols::same_fqn(&target.target_fqn, namespaced) {
                        namespaced.as_str()
                    } else {
                        global.as_str()
                    }
                }
                _ => return None,
            }),
            ResolveStatus::Unknown | ResolveStatus::Opaque | ResolveStatus::Skipped => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MethodTarget<'a> {
    pub receiver_fqn: String,
    pub method_name: String,
    pub found: Found<'a, MethodReflection>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PropertyTarget<'a> {
    pub receiver_fqn: String,
    pub property_name: String,
    pub found: Found<'a, PropertyReflection>,
}

pub(crate) struct MemberAccessResolver<'a> {
    fa: &'a FileAnalysis<'a>,
}

impl<'a> MemberAccessResolver<'a> {
    pub(crate) fn new(fa: &'a FileAnalysis<'a>) -> Self {
        Self { fa }
    }

    pub(crate) fn instance_method(
        &self,
        receiver_ty: &Type,
        method_name: &str,
    ) -> ResolveStatus<MethodTarget<'a>> {
        let Some(receiver_fqn) = sole_class(receiver_ty) else {
            return ResolveStatus::Opaque;
        };
        if !self.fa.class_fully_known(&receiver_fqn) {
            return ResolveStatus::Opaque;
        }
        if let Some(found) = self.fa.reflection.find_method(&receiver_fqn, method_name) {
            return ResolveStatus::Known(MethodTarget {
                receiver_fqn,
                method_name: method_name.to_string(),
                found,
            });
        }
        if self
            .fa
            .reflection
            .find_method(&receiver_fqn, "__call")
            .is_some()
            || self
                .fa
                .reflection
                .final_concrete_descendants_have_method(&receiver_fqn, method_name)
        {
            return ResolveStatus::Skipped;
        }
        ResolveStatus::Unknown
    }

    pub(crate) fn static_method(
        &self,
        class_fqn: &str,
        method_name: &str,
    ) -> ResolveStatus<MethodTarget<'a>> {
        if !self.fa.class_fully_known(class_fqn) {
            return ResolveStatus::Opaque;
        }
        if let Some(found) = self.fa.reflection.find_method(class_fqn, method_name) {
            return ResolveStatus::Known(MethodTarget {
                receiver_fqn: class_fqn.trim_start_matches('\\').to_string(),
                method_name: method_name.to_string(),
                found,
            });
        }
        if self
            .fa
            .reflection
            .find_method(class_fqn, "__callStatic")
            .is_some()
        {
            return ResolveStatus::Skipped;
        }
        ResolveStatus::Unknown
    }

    pub(crate) fn instance_property(
        &self,
        receiver_ty: &Type,
        property_name: &str,
        write: bool,
    ) -> ResolveStatus<PropertyTarget<'a>> {
        let Some(receiver_fqn) = sole_class(receiver_ty) else {
            return ResolveStatus::Opaque;
        };
        if !symbols::class_tree_fully_known(self.fa, &receiver_fqn) {
            return ResolveStatus::Opaque;
        }
        if let Some(class) = self.fa.reflection.class(&receiver_fqn) {
            if class.kind == php_ast::ClassKind::Interface {
                return ResolveStatus::Skipped;
            }
        }
        if let Some(found) = self
            .fa
            .reflection
            .find_property(&receiver_fqn, property_name)
        {
            return ResolveStatus::Known(PropertyTarget {
                receiver_fqn,
                property_name: property_name.to_string(),
                found,
            });
        }
        let magic = if write { "__set" } else { "__get" };
        if self
            .fa
            .reflection
            .find_method(&receiver_fqn, magic)
            .is_some()
        {
            return ResolveStatus::Skipped;
        }
        // A class that legally carries *dynamic* properties can never have an
        // "undefined" one. `properties.rs` has always exempted these; this
        // resolver did not, so the two member-resolution stacks disagreed about
        // the §8p false-positive posture. Today `stdClass` happens to escape via
        // the fully-known guard (it is absent from the class manifest), which
        // makes the correct behaviour accidental rather than intended.
        if allows_dynamic_properties(&receiver_fqn) {
            return ResolveStatus::Skipped;
        }
        ResolveStatus::Unknown
    }

    pub(crate) fn static_property(
        &self,
        class_fqn: &str,
        property_name: &str,
    ) -> ResolveStatus<PropertyTarget<'a>> {
        if !symbols::class_tree_fully_known(self.fa, class_fqn) {
            return ResolveStatus::Opaque;
        }
        if let Some(found) = self.fa.reflection.find_property(class_fqn, property_name) {
            return ResolveStatus::Known(PropertyTarget {
                receiver_fqn: class_fqn.trim_start_matches('\\').to_string(),
                property_name: property_name.to_string(),
                found,
            });
        }
        ResolveStatus::Unknown
    }
}

/// Index the file's resolved *function* references by callee span.
///
/// Rules that walk calls need this to turn a callee `Name` into its resolution;
/// it existed verbatim in three category files.
pub(crate) fn function_refs(refs: &[ResolvedRef]) -> HashMap<(u32, u32), &ResolvedRef> {
    refs.iter()
        .filter(|r| r.kind == php_resolve::RefKind::Function)
        .map(|r| ((r.span.start, r.span.end), r))
        .collect()
}

/// The resolved reference for a call's callee, when it is a plain name.
pub(crate) fn resolved_callee<'a>(
    callee: &php_ast::Expr,
    fmap: &HashMap<(u32, u32), &'a ResolvedRef>,
) -> Option<&'a ResolvedRef> {
    if let php_ast::ExprKind::Name(n) = &callee.kind {
        return fmap.get(&(n.span.start, n.span.end)).copied();
    }
    None
}

/// Whether `lower` — an **already lowercased** method name — is one of PHP's
/// magic methods (`__construct`, `__get`, …).
///
/// Magic methods are invoked by the engine, so rules about unused or
/// unconventional methods must exempt them. Takes lowercased input to match the
/// two former copies exactly; callers already lowercase for their own lookups.
pub(crate) fn is_magic_method(lower: &str) -> bool {
    MAGIC_METHODS.contains(&lower)
}

const MAGIC_METHODS: &[&str] = &[
    "__construct",
    "__destruct",
    "__call",
    "__callstatic",
    "__get",
    "__set",
    "__isset",
    "__unset",
    "__sleep",
    "__wakeup",
    "__serialize",
    "__unserialize",
    "__tostring",
    "__invoke",
    "__set_state",
    "__clone",
    "__debuginfo",
];

/// Classes whose instances legally carry properties that are never declared, so
/// an "undefined property" report on them is always a false positive.
///
/// `stdClass` is the canonical case: `json_decode()`, `(object) [...]` casts and
/// database row fetches all produce one.
pub(crate) fn allows_dynamic_properties(fqn: &str) -> bool {
    fqn.trim_start_matches('\\')
        .eq_ignore_ascii_case("stdClass")
}

pub(crate) fn sole_class(ty: &Type) -> Option<String> {
    match ty {
        Type::Named { fqn, .. } | Type::EnumCase { fqn, .. } => {
            Some(fqn.trim_start_matches('\\').to_string())
        }
        Type::Nullable(inner) => sole_class(inner),
        _ => None,
    }
}

pub(crate) fn primary_name(r: &ResolvedRef) -> String {
    r.name.trim_start_matches('\\').to_string()
}

/// Every class name an object-ish type mentions, flattened through nullables
/// and unions/intersections. Non-object arms contribute nothing.
pub(crate) fn object_class_names(t: &php_types::Type) -> Vec<String> {
    fn walk(t: &php_types::Type, out: &mut Vec<String>) {
        match t {
            php_types::Type::Named { fqn, .. } => out.push(fqn.to_string()),
            php_types::Type::Nullable(inner) => walk(inner, out),
            php_types::Type::Union(parts) | php_types::Type::Intersection(parts) => {
                for p in parts.iter() {
                    walk(p, out);
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    walk(t, &mut out);
    out
}

#[cfg(test)]
mod resolver_tests {
    use super::{MemberAccessResolver, ResolveStatus};
    use crate::testutil::with_analysis;
    use php_types::Type;

    fn status(src: &str, class: &str, prop: &str) -> &'static str {
        with_analysis(
            src,
            Default::default(),
            |_| {},
            |fa| {
                let ty = Type::Named {
                    fqn: class.into(),
                    args: vec![],
                };
                match MemberAccessResolver::new(fa).instance_property(&ty, prop, false) {
                    ResolveStatus::Known(_) => "known",
                    ResolveStatus::Unknown => "unknown",
                    ResolveStatus::Skipped => "skipped",
                    ResolveStatus::Opaque => "opaque",
                }
            },
        )
    }

    /// The two member-resolution stacks must agree on the §8p false-positive
    /// posture. `properties.rs` always exempted dynamic-property classes; this
    /// shared resolver did not, so a consumer reporting on `Unknown` (e.g. the
    /// callback-context pass) could flag `$std->anything`.
    ///
    /// Today `stdClass` also escapes via the fully-known guard, because it is
    /// absent from the builtin class manifest — declaring it here removes that
    /// accident and tests the exemption itself.
    #[test]
    fn dynamic_property_classes_are_never_unknown() {
        let src = "<?php class Bare {} class stdClass {}";
        // A plain class with no such property stays reportable.
        assert_eq!(status(src, "Bare", "anything"), "unknown");
        // A dynamic-property class never is.
        assert_eq!(status(src, "stdClass", "anything"), "skipped");
        assert_eq!(status(src, "\\stdClass", "anything"), "skipped");
    }

    #[test]
    fn declared_properties_still_resolve() {
        let src = "<?php class C { public int $p = 1; }";
        assert_eq!(status(src, "C", "p"), "known");
        assert_eq!(status(src, "C", "nope"), "unknown");
    }
}
