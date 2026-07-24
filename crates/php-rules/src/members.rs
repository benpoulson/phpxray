//! Shared call/member resolution for rules.

use crate::{symbols, FileAnalysis};
use php_reflect::{Found, FunctionReflection, MethodReflection, PropertyReflection};
use php_resolve::{Resolution, ResolvedRef};
use php_types::Type;

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
