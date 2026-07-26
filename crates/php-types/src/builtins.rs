//! Shared built-in stub manifest loading.
//!
//! The generated manifests live in this crate so both the names-only project
//! index and the typed reflection index consume one version-selected source.

use crate::PhpVersion;

pub const BUILTIN_SOURCE: &str = "<builtin>";

/// A built-in class that carries `@template` parameters.
///
/// The stub manifests describe members but not genericity, so the template names
/// are curated here — in **one** place, because two consumers need overlapping
/// but *different* facts about these classes and had each grown their own list.
pub struct GenericBuiltinClass {
    /// Lowercased, `\`-free class name (the comparison key).
    pub lower_name: &'static str,
    /// `@template` names, in declaration order.
    pub templates: &'static [&'static str],
    /// Whether instances can be iterated (`foreach`) — which is **not** the same
    /// as being generic. `ArrayAccess` has `TKey`/`TValue` but provides only
    /// offset access; iterating requires `Traversable`. Conflating the two would
    /// make `foreach` over an `ArrayAccess` bind loop variables it cannot have.
    pub iterable: bool,
}

const KEY_VALUE: &[&str] = &["TKey", "TValue"];

/// Every generic built-in class, with its templates and whether it is iterable.
pub static GENERIC_BUILTIN_CLASSES: &[GenericBuiltinClass] = &[
    GenericBuiltinClass {
        lower_name: "traversable",
        templates: KEY_VALUE,
        iterable: true,
    },
    GenericBuiltinClass {
        lower_name: "iterator",
        templates: KEY_VALUE,
        iterable: true,
    },
    GenericBuiltinClass {
        lower_name: "seekableiterator",
        templates: KEY_VALUE,
        iterable: true,
    },
    GenericBuiltinClass {
        lower_name: "iteratoraggregate",
        templates: KEY_VALUE,
        iterable: true,
    },
    GenericBuiltinClass {
        lower_name: "arrayobject",
        templates: KEY_VALUE,
        iterable: true,
    },
    GenericBuiltinClass {
        lower_name: "splfixedarray",
        templates: KEY_VALUE,
        iterable: true,
    },
    GenericBuiltinClass {
        lower_name: "weakmap",
        templates: KEY_VALUE,
        iterable: true,
    },
    // Generic, but not iterable — see `GenericBuiltinClass::iterable`.
    GenericBuiltinClass {
        lower_name: "arrayaccess",
        templates: KEY_VALUE,
        iterable: false,
    },
    GenericBuiltinClass {
        lower_name: "generator",
        templates: &["TKey", "TYield", "TSend", "TReturn"],
        iterable: true,
    },
];

/// Look up a generic built-in class by any spelling of its name.
pub fn generic_builtin_class(fqn: &str) -> Option<&'static GenericBuiltinClass> {
    let key = fqn.trim_start_matches('\\').to_ascii_lowercase();
    GENERIC_BUILTIN_CLASSES.iter().find(|c| c.lower_name == key)
}

const BUILTIN_FUNCTIONS_80400: &str = include_str!("../stubs/builtin-functions-80400.txt");
const BUILTIN_FUNCTIONS_80500: &str = include_str!("../stubs/builtin-functions-80500.txt");
const BUILTIN_FUNCTIONS_80600: &str = include_str!("../stubs/builtin-functions-80600.txt");
const BUILTIN_CLASSES_80400: &str = include_str!("../stubs/builtin-classes-80400.txt");
const BUILTIN_CLASSES_80500: &str = include_str!("../stubs/builtin-classes-80500.txt");
const BUILTIN_CLASSES_80600: &str = include_str!("../stubs/builtin-classes-80600.txt");
const BUILTIN_CONSTANTS_80400: &str = include_str!("../stubs/builtin-constants-80400.txt");
const BUILTIN_CONSTANTS_80500: &str = include_str!("../stubs/builtin-constants-80500.txt");
const BUILTIN_CONSTANTS_80600: &str = include_str!("../stubs/builtin-constants-80600.txt");

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinClassKind {
    Class,
    Interface,
    Trait,
    Enum,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BuiltinParam<'a> {
    pub name: &'a str,
    pub ty: &'a str,
    pub flags: &'a str,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuiltinFunction<'a> {
    pub fqn: &'a str,
    pub return_type: &'a str,
    pub params: Vec<BuiltinParam<'a>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuiltinClassRecord<'a> {
    Class {
        kind: BuiltinClassKind,
        fqn: &'a str,
        parents: Vec<&'a str>,
        interfaces: Vec<&'a str>,
        traits: Vec<&'a str>,
        flags: &'a str,
    },
    Method {
        class: &'a str,
        name: &'a str,
        visibility: &'a str,
        flags: &'a str,
        return_type: &'a str,
        native_return: &'a str,
        params: Vec<BuiltinParam<'a>>,
    },
    Property {
        class: &'a str,
        name: &'a str,
        visibility: &'a str,
        flags: &'a str,
        ty: &'a str,
        native_ty: &'a str,
    },
    Constant {
        class: &'a str,
        name: &'a str,
        visibility: &'a str,
        flags: &'a str,
        ty: &'a str,
        int_value: Option<i64>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BuiltinConstant<'a> {
    pub fqn: &'a str,
}

pub fn selected_manifest_id(version: PhpVersion) -> u32 {
    match version.id() {
        id if id < 80500 => 80400,
        id if id < 80600 => 80500,
        _ => 80600,
    }
}

pub fn raw_function_manifest_for(version: PhpVersion) -> &'static str {
    match selected_manifest_id(version) {
        80400 => BUILTIN_FUNCTIONS_80400,
        80500 => BUILTIN_FUNCTIONS_80500,
        _ => BUILTIN_FUNCTIONS_80600,
    }
}

pub fn raw_class_manifest_for(version: PhpVersion) -> &'static str {
    match selected_manifest_id(version) {
        80400 => BUILTIN_CLASSES_80400,
        80500 => BUILTIN_CLASSES_80500,
        _ => BUILTIN_CLASSES_80600,
    }
}

pub fn raw_constant_manifest_for(version: PhpVersion) -> &'static str {
    match selected_manifest_id(version) {
        80400 => BUILTIN_CONSTANTS_80400,
        80500 => BUILTIN_CONSTANTS_80500,
        _ => BUILTIN_CONSTANTS_80600,
    }
}

pub fn functions_for(version: PhpVersion) -> Vec<BuiltinFunction<'static>> {
    raw_function_manifest_for(version)
        .lines()
        .filter_map(parse_function)
        .collect()
}

pub fn class_records_for(version: PhpVersion) -> Vec<BuiltinClassRecord<'static>> {
    raw_class_manifest_for(version)
        .lines()
        .filter_map(parse_class_record)
        .collect()
}

pub fn constants_for(version: PhpVersion) -> Vec<BuiltinConstant<'static>> {
    raw_constant_manifest_for(version)
        .lines()
        .filter_map(parse_constant)
        .collect()
}

fn parse_function(line: &'static str) -> Option<BuiltinFunction<'static>> {
    let line = line.trim();
    if line.is_empty() || line.starts_with('#') {
        return None;
    }
    let mut fields = line.split('\t');
    Some(BuiltinFunction {
        fqn: fields.next()?,
        return_type: fields.next().unwrap_or(""),
        params: parse_params(fields.next().unwrap_or("")),
    })
}

fn parse_class_record(line: &'static str) -> Option<BuiltinClassRecord<'static>> {
    let line = line.trim();
    if line.is_empty() || line.starts_with('#') {
        return None;
    }
    let mut fields = line.split('\t');
    match fields.next()? {
        "class" => Some(BuiltinClassRecord::Class {
            kind: parse_kind(fields.next().unwrap_or("class")),
            fqn: fields.next().unwrap_or(""),
            parents: parse_named_list(fields.next().unwrap_or("")),
            interfaces: parse_named_list(fields.next().unwrap_or("")),
            traits: parse_named_list(fields.next().unwrap_or("")),
            flags: fields.next().unwrap_or(""),
        }),
        "method" => Some(BuiltinClassRecord::Method {
            class: fields.next().unwrap_or(""),
            name: fields.next().unwrap_or(""),
            visibility: fields.next().unwrap_or("public"),
            flags: fields.next().unwrap_or(""),
            return_type: fields.next().unwrap_or(""),
            native_return: fields.next().unwrap_or(""),
            params: parse_params(fields.next().unwrap_or("")),
        }),
        "property" => Some(BuiltinClassRecord::Property {
            class: fields.next().unwrap_or(""),
            name: fields.next().unwrap_or(""),
            visibility: fields.next().unwrap_or("public"),
            flags: fields.next().unwrap_or(""),
            ty: fields.next().unwrap_or(""),
            native_ty: fields.next().unwrap_or(""),
        }),
        "constant" => Some(BuiltinClassRecord::Constant {
            class: fields.next().unwrap_or(""),
            name: fields.next().unwrap_or(""),
            visibility: fields.next().unwrap_or("public"),
            flags: fields.next().unwrap_or(""),
            ty: fields.next().unwrap_or(""),
            int_value: fields.next().and_then(|s| {
                if s.is_empty() {
                    None
                } else {
                    s.parse::<i64>().ok()
                }
            }),
        }),
        _ => None,
    }
}

fn parse_constant(line: &'static str) -> Option<BuiltinConstant<'static>> {
    let line = line.trim();
    if line.is_empty() || line.starts_with('#') {
        return None;
    }
    Some(BuiltinConstant { fqn: line })
}

fn parse_params(s: &'static str) -> Vec<BuiltinParam<'static>> {
    if s.is_empty() {
        return Vec::new();
    }
    s.split(';')
        .filter_map(|p| {
            let mut fields = p.split('#');
            Some(BuiltinParam {
                name: fields.next()?,
                ty: fields.next().unwrap_or(""),
                flags: fields.next().unwrap_or(""),
            })
        })
        .collect()
}

fn parse_kind(s: &str) -> BuiltinClassKind {
    match s {
        "interface" => BuiltinClassKind::Interface,
        "trait" => BuiltinClassKind::Trait,
        "enum" => BuiltinClassKind::Enum,
        _ => BuiltinClassKind::Class,
    }
}

fn parse_named_list(s: &'static str) -> Vec<&'static str> {
    s.split(',').filter(|p| !p.is_empty()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn manifest_selection_clamps_to_supported_versions() {
        assert_eq!(
            selected_manifest_id(PhpVersion::from_id(70400).unwrap()),
            80400
        );
        assert_eq!(
            selected_manifest_id(PhpVersion::from_id(80400).unwrap()),
            80400
        );
        assert_eq!(
            selected_manifest_id(PhpVersion::from_id(80500).unwrap()),
            80500
        );
        assert_eq!(
            selected_manifest_id(PhpVersion::from_id(80600).unwrap()),
            80600
        );
        assert_eq!(
            selected_manifest_id(PhpVersion::from_id(90000).unwrap()),
            80600
        );
    }

    #[test]
    fn parses_function_class_and_constant_manifests() {
        let version = PhpVersion::from_id(80400).unwrap();
        assert!(functions_for(version).iter().any(|f| f.fqn == "strlen"));
        assert!(class_records_for(version).iter().any(|r| matches!(
            r,
            BuiltinClassRecord::Class { fqn, .. } if *fqn == "Exception"
        )));
        assert!(constants_for(version).iter().any(|c| c.fqn == "PHP_EOL"));
    }
}

#[cfg(test)]
mod generic_class_tests {
    use super::*;

    /// The two former consumers disagreed on `ArrayAccess`, and that difference
    /// is correct rather than drift: it is generic but not iterable. Pin both
    /// facts so a future "cleanup" cannot collapse them.
    #[test]
    fn array_access_is_generic_but_not_iterable() {
        let c = generic_builtin_class("ArrayAccess").expect("ArrayAccess is generic");
        assert_eq!(c.templates, &["TKey", "TValue"]);
        assert!(!c.iterable, "ArrayAccess provides offsets, not iteration");

        let t = generic_builtin_class("Traversable").expect("Traversable is generic");
        assert!(t.iterable);
    }

    #[test]
    fn lookup_accepts_any_spelling() {
        for spelling in ["Generator", "generator", "\\Generator", "\\GENERATOR"] {
            let c = generic_builtin_class(spelling).expect(spelling);
            assert_eq!(c.templates, &["TKey", "TYield", "TSend", "TReturn"]);
        }
        assert!(generic_builtin_class("NotABuiltin").is_none());
    }

    /// Each class must be declared before any of its members, and only once.
    ///
    /// `php_reflect::builtins` synthesises a stub `ClassReflection` when a
    /// member record arrives first, then pushes a *second* entry when the real
    /// `class` line shows up — and the later insert wins, silently discarding
    /// every member attached to the stub. Nothing else pins the order, so a
    /// regenerated or hand-edited manifest could reintroduce it with no test
    /// failure anywhere.
    #[test]
    fn manifest_declares_each_class_once_and_before_its_members() {
        for id in [80400u32, 80500, 80600] {
            let v = PhpVersion::from_id(id).expect("version id");
            let mut declared: std::collections::HashSet<String> = std::collections::HashSet::new();
            for r in class_records_for(v) {
                match r {
                    BuiltinClassRecord::Class { fqn, .. } => {
                        let key = fqn.trim_start_matches('\\').to_ascii_lowercase();
                        assert!(
                            declared.insert(key.clone()),
                            "{id}: class {key:?} is declared twice — the second entry \
                             replaces the first and drops its members"
                        );
                    }
                    BuiltinClassRecord::Method { class, .. }
                    | BuiltinClassRecord::Property { class, .. }
                    | BuiltinClassRecord::Constant { class, .. } => {
                        let key = class.trim_start_matches('\\').to_ascii_lowercase();
                        assert!(
                            declared.contains(&key),
                            "{id}: a member of {key:?} appears before its `class` line"
                        );
                    }
                }
            }
        }
    }

    /// Every entry must name a class the stub manifests actually ship, or the
    /// curated genericity silently applies to nothing.
    #[test]
    fn every_generic_class_exists_in_the_manifests() {
        let records = class_records_for(PhpVersion::default());
        for c in GENERIC_BUILTIN_CLASSES {
            assert!(
                records.iter().any(|r| matches!(
                    r,
                    BuiltinClassRecord::Class { fqn, .. }
                        if fqn.trim_start_matches('\\').to_ascii_lowercase() == c.lower_name
                )),
                "GENERIC_BUILTIN_CLASSES names {:?}, which is not in the builtin class manifest",
                c.lower_name
            );
        }
    }
}
