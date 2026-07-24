//! M-T2: the **reflection model** — per-declaration descriptors whose member
//! types are fully resolved.
//!
//! A [`ClassReflection`] / [`FunctionReflection`] is the semantic view of a
//! class or function the type system queries: every member's type is a
//! [`Type`], with native declarations and PHPDoc annotations merged and class
//! names resolved to FQNs. PHPDoc refines native: when both a native type hint
//! and a `@param`/`@return`/`@var` are present, the doc type wins (it carries
//! generics, shapes, and literal types the native syntax can't express).
//!
//! Magic members declared only in the class docblock — `@method` and
//! `@property*` (heavily used by Laravel facades and barryvdh/ide-helper) — are
//! reflected alongside the real members, flagged [`MethodReflection::magic`] /
//! [`PropertyReflection::magic`]. Generic parent type arguments from
//! `@extends`/`@implements`/`@use` are attached to the corresponding resolved
//! parent/interface/trait.

use crate::{resolve_ast_type, resolve_doc_type};
use php_ast::{
    AttributeGroup, BinOp, ClassDecl, ClassKind, Expr, ExprKind, FunctionDecl, Member, MemberName,
    MethodDecl, Name, Param as AstParam, PropertyDecl, Type as AstType, Visibility,
};
use php_intern::Interner;
use php_phpdoc::{Doc, DocType, MethodParam, PropertyAccess};
use std::collections::HashMap;
use php_resolve::{Resolution, Scope};
use php_types::Type;

/// A reflected function or method parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamReflection {
    /// Variable name without the leading `$`.
    pub name: String,
    /// The resolved type (`mixed` when neither a hint nor a `@param` is given).
    pub ty: Type,
    pub by_ref: bool,
    pub variadic: bool,
    /// Has a default value or is variadic (so may be omitted at the call site).
    pub optional: bool,
    /// Declared via constructor property promotion (`public int $x`).
    pub promoted: bool,
    /// A type was *explicitly* written (native hint or `@param`), even if it is
    /// `mixed`. Distinguishes an explicit `@param mixed` (not a missing typehint)
    /// from a defaulted-to-`mixed` untyped parameter — used by the inherited-
    /// prototype check in the missing-typehint rules.
    pub explicit: bool,
    /// The type from the *native* hint alone (`mixed` if none), ignoring PHPDoc —
    /// used for `treatPhpDocTypesAsCertain: false` native-level checking.
    pub native_ty: Type,
    /// `@param-out` — the type a by-ref parameter holds *after* the call
    /// (`preg_match`-style out parameters). `None` = unannotated.
    pub out_ty: Option<Type>,
    /// `ty` was synthesized by whole-project signature inference (from call-site
    /// argument types), not declared. Treated as PHPDoc-grade: refines `ty` but
    /// leaves `native_ty`/`explicit` untouched, so the native-level checking and the
    /// missing-typehint rules are unaffected.
    pub inferred: bool,
}

impl ParamReflection {
    /// The type of the *local variable* bound to this parameter inside the body.
    /// For a variadic `...$xs` this is `list<ty>` (PHP collects the rest into a
    /// positional array), not the per-argument element type `ty`.
    pub fn local_type(&self) -> Type {
        if self.variadic {
            Type::List(Box::new(self.ty.clone()))
        } else {
            self.ty.clone()
        }
    }
}

/// A reflected free function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionReflection {
    pub fqn: String,
    pub params: Vec<ParamReflection>,
    pub return_type: Type,
    /// A return type was *explicitly* written (native hint or `@return`), even if
    /// `mixed`. See [`ParamReflection::explicit`]. Distinguishes a real declaration
    /// from a defaulted-to-`mixed` untyped function.
    pub explicit_return: bool,
    /// `return_type` was synthesized by whole-project signature inference (from the
    /// body's `return` statements), not declared. PHPDoc-grade; see
    /// [`ParamReflection::inferred`].
    pub inferred_return: bool,
    /// Native-hint-only return type (`mixed` if none).
    pub native_return: Type,
    pub by_ref: bool,
    /// `@template` names in scope for this function.
    pub templates: Vec<String>,
    pub deprecated: bool,
    /// Declared side-effect-free via `@pure`/`@phpstan-pure`/`@psalm-pure` (and not
    /// `@phpstan-impure`). Used by the `*.resultUnused` rules.
    pub pure: bool,
    /// Explicitly declared side-effect-having via `@phpstan-impure`/`@impure`.
    /// Distinct from `!pure` (unmarked): flow narrowing invalidates object-state
    /// facts only for callees *known* to have side effects.
    pub impure: bool,
    /// `@phpstan-assert*` declarations, with types resolved — call sites narrow
    /// the matching argument (webmozart/assert-style helpers).
    pub asserts: Vec<AssertReflection>,
    /// Declared with PHP 8.5's `#[NoDiscard]`; call-as-statement should report
    /// that the return value is discarded.
    pub must_use_return_value: bool,
    /// Loaded from the built-in stub manifest (Cap #4) rather than reflected from
    /// project source. The stub *arity* is unreliable (phpstorm-stubs omits
    /// defaults on some optional params and over-/under-counts variadics), so the
    /// arguments-count rule skips these; their *types* still drive inference.
    pub builtin: bool,
}

/// A reflected method (real or magic `@method`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MethodReflection {
    pub name: String,
    pub visibility: Visibility,
    pub is_static: bool,
    pub is_abstract: bool,
    pub is_final: bool,
    pub params: Vec<ParamReflection>,
    pub return_type: Type,
    /// A return type was *explicitly* written (native hint or `@return`), even if
    /// `mixed`. See [`ParamReflection::explicit`].
    pub explicit_return: bool,
    /// `return_type` was synthesized by whole-project signature inference, not
    /// declared. PHPDoc-grade; see [`ParamReflection::inferred`].
    pub inferred_return: bool,
    /// Native-hint-only return type (`mixed` if none). See [`ParamReflection::native_ty`].
    pub native_return: Type,
    /// `@template` names in scope (class templates plus the method's own).
    pub templates: Vec<String>,
    pub deprecated: bool,
    /// Declared side-effect-free via `@pure`/`@phpstan-pure`/`@psalm-pure` (and not
    /// `@phpstan-impure`). Used by the `*.resultUnused` rules.
    pub pure: bool,
    /// Explicitly declared side-effect-having via `@phpstan-impure`/`@impure`.
    /// Distinct from `!pure` (unmarked); see [`FunctionReflection::impure`].
    pub impure: bool,
    /// `@phpstan-assert*` declarations; see [`FunctionReflection::asserts`].
    pub asserts: Vec<AssertReflection>,
    /// `@phpstan-self-out Type` — the type `$this` (the receiver) holds after
    /// this method returns (`self`/`static` bound to the receiver at the call
    /// site). `None` = unannotated.
    pub self_out: Option<Type>,
    /// Declared with PHP 8.5's `#[NoDiscard]`; call-as-statement should report
    /// that the return value is discarded.
    pub must_use_return_value: bool,
    /// Declared only via a class-level `@method` tag (no real implementation).
    pub magic: bool,
}

/// A resolved `@phpstan-assert*` declaration on a function/method.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssertReflection {
    /// The asserted target without `$`: a parameter name, or a `this->prop`
    /// path (asserting on the receiver's own property).
    pub param: String,
    pub ty: Type,
    /// `!Type` — asserted *not* to be of the type.
    pub negated: bool,
    pub when: php_phpdoc::AssertWhen,
}

/// A reflected property (real or magic `@property*`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropertyReflection {
    /// Property name without the leading `$`.
    pub name: String,
    pub visibility: Visibility,
    pub is_static: bool,
    pub is_readonly: bool,
    pub ty: Type,
    /// Native-hint-only type (`mixed` if the property has only a `@var`).
    pub native_ty: Type,
    pub has_default: bool,
    /// Read/write access — always [`PropertyAccess::ReadWrite`] for real
    /// properties; reflects the `@property-read`/`-write` tag for magic ones.
    pub access: PropertyAccess,
    /// Declared only via a class-level `@property*` tag.
    pub magic: bool,
}

/// A reflected class constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstReflection {
    pub name: String,
    pub visibility: Visibility,
    /// Declared const type (`const int X = 1`), or the literal type of the
    /// initializer for an undeclared constant (`const X = 'draft'` is
    /// `'draft'`), else `mixed`.
    pub ty: Type,
    /// A native const type was *written* (`const int X = 1`). Distinguishes a
    /// declared type from a literal-folded one for the override rules.
    pub declared: bool,
    pub is_final: bool,
    /// The constant's integer value when the initializer is a plain int literal
    /// (`const TYPE_NORMAL = 1`). Lets inference treat `Foo::BAR` as a literal-int
    /// type, which drives constant-comparison dead-branch pruning. `None` for
    /// non-int / non-trivial initializers.
    pub int_value: Option<i64>,
    /// For an enum case: the literal type of its backing value
    /// (`case Draft = 'draft'` → `'draft'`). `None` for pure cases and
    /// ordinary constants. Drives per-case `->value` inference.
    pub case_backing: Option<Type>,
}

/// The semantic view of a class/interface/trait/enum declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassReflection {
    pub fqn: String,
    pub kind: ClassKind,
    pub is_abstract: bool,
    pub is_final: bool,
    pub is_readonly: bool,
    /// Parent class(es), resolved, with `@extends` generic args attached.
    pub parents: Vec<Type>,
    /// Implemented interfaces, with `@implements` generic args attached.
    pub interfaces: Vec<Type>,
    /// Used traits, with `@use` generic args attached.
    pub traits: Vec<Type>,
    /// `@template` names declared on the class.
    pub templates: Vec<String>,
    /// Resolved `@template T of Bound` upper bounds, aligned by index with
    /// [`templates`]. `None` = unbounded (`mixed`). Drives the
    /// `generics.notSubtype` check at instantiation sites.
    pub template_bounds: Vec<Option<Type>>,
    pub methods: Vec<MethodReflection>,
    pub properties: Vec<PropertyReflection>,
    pub constants: Vec<ConstReflection>,
    /// `@mixin` targets, resolved.
    pub mixins: Vec<Type>,
    pub deprecated: bool,
    /// If this class is itself an attribute (`#[Attribute]`), its target/repeatable
    /// flags — what the *AttributesRule family checks usages against.
    pub attribute: Option<AttributeSpec>,
    /// The class (or a parent) declares `@phpstan-consistent-constructor`, which
    /// makes `new static()` safe (subclasses can't change the constructor).
    pub consistent_constructor: bool,
    /// Local `@phpstan-type` aliases this class *exports* (for other classes to
    /// `@phpstan-import-type`), keyed by the alias's short name (lowercased).
    /// Already expanded among the class's own aliases.
    pub type_aliases: HashMap<String, Type>,
    /// `@phpstan-import-type Name from Other [as Alias]` declarations, resolved
    /// at the [`ReflectionIndex`] level (which has every class) — see
    /// `ReflectionIndex::resolve_type_imports`.
    pub imported_types: Vec<ImportedType>,
    /// Loaded from the built-in stub manifest rather than project source.
    pub builtin: bool,
}

/// A resolved `@phpstan-import-type Name from Other [as Alias]` declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportedType {
    /// The FQN the *local* alias name resolves to in this class's scope (the
    /// phantom class FQN a member reference to the bare name also resolves to —
    /// so we can substitute by FQN, not the shadow-prone short name).
    pub local_fqn: String,
    /// The FQN of the class the alias is imported from.
    pub source_class: String,
    /// The alias's short name in the source class (lowercased).
    pub source_name: String,
}

/// `#[Attribute(...)]` metadata on an attribute class: which targets it may be
/// applied to and whether it is repeatable. Mirrors PHP's `\Attribute` constants.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AttributeSpec {
    /// Bit-mask of the `attr_target::*` flags (`#[Attribute]` with no args ⇒ ALL).
    pub targets: u32,
    pub repeatable: bool,
}

/// PHP `\Attribute` flag constants.
pub mod attr_target {
    pub const CLASS: u32 = 1;
    pub const FUNCTION: u32 = 2;
    pub const METHOD: u32 = 4;
    pub const PROPERTY: u32 = 8;
    pub const CLASS_CONSTANT: u32 = 16;
    pub const PARAMETER: u32 = 32;
    pub const CONSTANT: u32 = 64;
    pub const ALL: u32 = 127;
    pub const IS_REPEATABLE: u32 = 128;
}

/// Parse the `#[Attribute]` / `#[Attribute(flags)]` group on a declaration, if
/// present, into an [`AttributeSpec`]. The attribute name must resolve to the
/// global `\Attribute`.
fn attribute_spec(
    scope: &Scope,
    interner: &Interner,
    attrs: &[AttributeGroup],
) -> Option<AttributeSpec> {
    for g in attrs {
        for a in &g.attrs {
            if !is_php_attribute(scope, &a.name) {
                continue;
            }
            return Some(match &a.args {
                None => AttributeSpec {
                    targets: attr_target::ALL,
                    repeatable: false,
                },
                Some(args) => {
                    let flags = args
                        .first()
                        .and_then(|arg| eval_attr_flags(interner, &arg.value))
                        .unwrap_or(attr_target::ALL);
                    let targets = flags & attr_target::ALL;
                    AttributeSpec {
                        targets: if targets != 0 {
                            targets
                        } else {
                            attr_target::ALL
                        },
                        repeatable: flags & attr_target::IS_REPEATABLE != 0,
                    }
                }
            });
        }
    }
    None
}

fn is_php_attribute(scope: &Scope, name: &Name) -> bool {
    matches!(scope.resolve_class(name), Resolution::Fqn(fqn) if fqn.eq_ignore_ascii_case("Attribute"))
}

/// Evaluate an `#[Attribute(...)]` flag expression (`Attribute::TARGET_X | …`).
fn eval_attr_flags(interner: &Interner, e: &Expr) -> Option<u32> {
    match &e.kind {
        ExprKind::Paren(inner) => eval_attr_flags(interner, inner),
        ExprKind::Binary {
            op: BinOp::BitOr,
            lhs,
            rhs,
        } => Some(eval_attr_flags(interner, lhs)? | eval_attr_flags(interner, rhs)?),
        ExprKind::ClassConst {
            name: MemberName::Ident(sym),
            ..
        } => attr_const(interner.resolve(*sym)),
        ExprKind::Int(n) => u32::try_from(*n).ok(),
        _ => None,
    }
}

fn attr_const(name: &str) -> Option<u32> {
    Some(match name {
        "TARGET_CLASS" => attr_target::CLASS,
        "TARGET_FUNCTION" => attr_target::FUNCTION,
        "TARGET_METHOD" => attr_target::METHOD,
        "TARGET_PROPERTY" => attr_target::PROPERTY,
        "TARGET_CLASS_CONSTANT" => attr_target::CLASS_CONSTANT,
        "TARGET_PARAMETER" => attr_target::PARAMETER,
        "TARGET_CONSTANT" => attr_target::CONSTANT,
        "TARGET_ALL" => attr_target::ALL,
        "IS_REPEATABLE" => attr_target::IS_REPEATABLE,
        _ => return None,
    })
}

/// Reflect a free function declaration.
pub fn reflect_function(
    scope: &Scope,
    interner: &Interner,
    f: &FunctionDecl,
) -> FunctionReflection {
    let doc = parse_doc(f.doc.as_deref());
    let templates: Vec<String> = doc.templates.iter().map(|t| t.name.clone()).collect();
    let asserts = reflect_asserts(scope, &templates, &doc);
    FunctionReflection {
        fqn: scope.qualify(interner.resolve(f.name)),
        params: reflect_params(scope, interner, &templates, &f.params, &doc),
        return_type: merge_type(
            scope,
            &templates,
            f.return_type.as_ref(),
            doc.returns.as_ref(),
        ),
        explicit_return: f.return_type.is_some() || doc.returns.is_some(),
        inferred_return: false,
        native_return: native_type(scope, f.return_type.as_ref()),
        by_ref: f.by_ref,
        templates,
        deprecated: doc.deprecated,
        pure: doc_is_pure(f.doc.as_deref()),
        impure: doc_is_impure(f.doc.as_deref()),
        asserts,
        must_use_return_value: has_nodiscard_attr(&f.attrs),
        builtin: false,
    }
}

/// Reflect a class/interface/trait/enum declaration. `fqn` is its already-resolved
/// fully-qualified name (the caller knows the declaring scope).
pub fn reflect_class(
    scope: &Scope,
    interner: &Interner,
    fqn: &str,
    c: &ClassDecl,
) -> ClassReflection {
    let doc = parse_doc(c.doc.as_deref());
    let class_templates: Vec<String> = doc.templates.iter().map(|t| t.name.clone()).collect();
    let template_bounds: Vec<Option<Type>> = doc
        .templates
        .iter()
        .map(|t| {
            t.bound
                .as_ref()
                .map(|b| resolve_doc_type(scope, &class_templates, b))
        })
        .collect();

    let mut methods = Vec::new();
    let mut properties = Vec::new();
    let mut constants = Vec::new();
    for m in &c.members {
        match m {
            Member::Method(md) => {
                methods.push(reflect_method(scope, interner, &class_templates, md));
                // Constructor property promotion: a `__construct` parameter with a
                // visibility modifier is *also* a property of the class.
                if interner
                    .resolve(md.name)
                    .eq_ignore_ascii_case("__construct")
                {
                    promoted_properties(
                        scope,
                        interner,
                        &class_templates,
                        md,
                        c.modifiers.is_readonly,
                        &mut properties,
                    );
                }
            }
            Member::Property(pd) => {
                reflect_properties(scope, interner, &class_templates, pd, &mut properties)
            }
            Member::ClassConst(cd) => reflect_consts(scope, cd, interner, &mut constants),
            // An enum case (`RoundingMode::Up`) is accessed like a class constant and
            // its value is an instance of the enum — reflect it as a constant so
            // cross-file `Enum::Case` access resolves through the index.
            Member::EnumCase(ec) => {
                let case = interner.resolve(ec.name).to_string();
                constants.push(ConstReflection {
                    ty: Type::EnumCase {
                        fqn: fqn.into(),
                        case: case.as_str().into(),
                    },
                    name: case,
                    visibility: Visibility::Public,
                    declared: false,
                    is_final: true,
                    int_value: None,
                    case_backing: ec.value.as_ref().and_then(const_literal_type),
                });
            }
            // Trait-use adaptations aren't members the type query layer needs yet;
            // traits are surfaced via `traits` below.
            Member::TraitUse(_) => {}
        }
    }

    // Magic members from the class docblock.
    methods.extend(
        doc.methods
            .iter()
            .map(|m| magic_method(scope, &class_templates, m)),
    );
    properties.extend(
        doc.properties
            .iter()
            .filter_map(|p| magic_property(scope, &class_templates, p)),
    );
    if c.kind == ClassKind::Enum {
        synthesize_enum_members(scope, c, &mut methods, &mut properties);
    }

    let traits: Vec<Name> = c
        .members
        .iter()
        .filter_map(|m| match m {
            Member::TraitUse(tu) => Some(tu.traits.iter().cloned()),
            _ => None,
        })
        .flatten()
        .collect();

    // Expand local `@phpstan-type` aliases in every reflected member type.
    let aliases = class_type_aliases(scope, &class_templates, c.doc.as_deref());
    if !aliases.is_empty() {
        expand_member_aliases(&mut methods, &mut properties, &mut constants, &aliases);
    }
    // Export aliases keyed by short name (for `@phpstan-import-type`); cross-
    // class imports are resolved later at the index level.
    let type_aliases: HashMap<String, Type> = aliases
        .into_iter()
        .map(|(fqn, ty)| (fqn.rsplit('\\').next().unwrap_or("").to_string(), ty))
        .filter(|(name, _)| !name.is_empty())
        .collect();
    let imported_types = class_imported_types(scope, c.doc.as_deref());

    ClassReflection {
        fqn: fqn.to_string(),
        kind: c.kind,
        is_abstract: c.modifiers.is_abstract,
        is_final: c.modifiers.is_final,
        is_readonly: c.modifiers.is_readonly,
        parents: parents_with_generics(scope, &class_templates, &c.extends, &doc.extends),
        interfaces: parents_with_generics(scope, &class_templates, &c.implements, &doc.implements),
        traits: parents_with_generics(scope, &class_templates, &traits, &doc.uses),
        mixins: doc
            .mixins
            .iter()
            .map(|m| resolve_doc_type(scope, &class_templates, m))
            .collect(),
        templates: class_templates,
        template_bounds,
        methods,
        properties,
        constants,
        deprecated: doc.deprecated,
        attribute: attribute_spec(scope, interner, &c.attrs),
        consistent_constructor: c
            .doc
            .as_deref()
            .is_some_and(|d| d.contains("consistent-constructor")),
        type_aliases,
        imported_types,
        builtin: false,
    }
}

fn synthesize_enum_members(
    scope: &Scope,
    c: &ClassDecl,
    methods: &mut Vec<MethodReflection>,
    properties: &mut Vec<PropertyReflection>,
) {
    properties.push(PropertyReflection {
        name: "name".to_string(),
        visibility: Visibility::Public,
        is_static: false,
        is_readonly: true,
        ty: Type::String,
        native_ty: Type::String,
        has_default: false,
        access: PropertyAccess::ReadOnly,
        magic: false,
    });

    let static_enum = Type::StaticType;
    methods.push(synthetic_method(
        "cases",
        Vec::new(),
        Type::List(Box::new(static_enum.clone())),
    ));

    let Some(backing) = &c.backing else { return };
    let backing_ty = resolve_ast_type(scope, backing);
    properties.push(PropertyReflection {
        name: "value".to_string(),
        visibility: Visibility::Public,
        is_static: false,
        is_readonly: true,
        ty: backing_ty.clone(),
        native_ty: backing_ty.clone(),
        has_default: false,
        access: PropertyAccess::ReadOnly,
        magic: false,
    });
    methods.push(synthetic_method(
        "from",
        vec![synthetic_param("value", backing_ty.clone())],
        static_enum.clone(),
    ));
    methods.push(synthetic_method(
        "tryFrom",
        vec![synthetic_param("value", backing_ty)],
        static_enum.nullable(),
    ));
}

fn synthetic_method(
    name: &str,
    params: Vec<ParamReflection>,
    return_type: Type,
) -> MethodReflection {
    MethodReflection {
        name: name.to_string(),
        visibility: Visibility::Public,
        is_static: true,
        is_abstract: false,
        is_final: true,
        params,
        return_type: return_type.clone(),
        explicit_return: true,
        inferred_return: false,
        native_return: return_type,
        templates: Vec::new(),
        deprecated: false,
        pure: true,
        impure: false,
        asserts: Vec::new(),
        self_out: None,
        must_use_return_value: false,
        magic: false,
    }
}

fn synthetic_param(name: &str, ty: Type) -> ParamReflection {
    ParamReflection {
        name: name.to_string(),
        ty: ty.clone(),
        by_ref: false,
        variadic: false,
        optional: false,
        promoted: false,
        explicit: true,
        native_ty: ty,
        out_ty: None,
        inferred: false,
    }
}

/// Append the constructor's promoted parameters as class properties. A parameter
/// is promoted iff it carries a visibility modifier (PHP requires one); its type
/// is the native hint refined by a matching `@param` on the constructor docblock.
fn promoted_properties(
    scope: &Scope,
    interner: &Interner,
    class_templates: &[String],
    ctor: &MethodDecl,
    class_readonly: bool,
    out: &mut Vec<PropertyReflection>,
) {
    let doc = parse_doc(ctor.doc.as_deref());
    let templates = combine_templates(class_templates, &doc);
    for p in &ctor.params {
        let Some(visibility) = p.modifiers.visibility else {
            continue;
        };
        let pname = interner.resolve(p.name);
        let doc_ty = doc
            .params
            .iter()
            .find(|dp| dp.name.as_deref() == Some(pname))
            .and_then(|dp| dp.ty.as_ref());
        out.push(PropertyReflection {
            name: pname.to_string(),
            visibility,
            is_static: false,
            is_readonly: p.modifiers.is_readonly || class_readonly,
            ty: merge_type(scope, &templates, p.ty.as_ref(), doc_ty),
            native_ty: native_type(scope, p.ty.as_ref()),
            has_default: p.default.is_some(),
            access: PropertyAccess::ReadWrite,
            magic: false,
        });
    }
}

fn reflect_method(
    scope: &Scope,
    interner: &Interner,
    class_templates: &[String],
    m: &MethodDecl,
) -> MethodReflection {
    let doc = parse_doc(m.doc.as_deref());
    let templates = combine_templates(class_templates, &doc);
    let asserts = reflect_asserts(scope, &templates, &doc);
    let self_out = doc
        .self_out
        .as_ref()
        .map(|t| resolve_doc_type(scope, &templates, t));
    MethodReflection {
        name: interner.resolve(m.name).to_string(),
        visibility: m.modifiers.visibility.unwrap_or(Visibility::Public),
        is_static: m.modifiers.is_static,
        is_abstract: m.modifiers.is_abstract || m.body.is_none(),
        is_final: m.modifiers.is_final,
        params: reflect_params(scope, interner, &templates, &m.params, &doc),
        return_type: merge_type(
            scope,
            &templates,
            m.return_type.as_ref(),
            doc.returns.as_ref(),
        ),
        explicit_return: m.return_type.is_some() || doc.returns.is_some(),
        inferred_return: false,
        native_return: native_type(scope, m.return_type.as_ref()),
        templates,
        deprecated: doc.deprecated,
        pure: doc_is_pure(m.doc.as_deref()),
        impure: doc_is_impure(m.doc.as_deref()),
        asserts,
        self_out,
        must_use_return_value: has_nodiscard_attr(&m.attrs),
        magic: false,
    }
}

fn reflect_properties(
    scope: &Scope,
    interner: &Interner,
    templates: &[String],
    pd: &PropertyDecl,
    out: &mut Vec<PropertyReflection>,
) {
    let doc = parse_doc(pd.doc.as_deref());
    // A property docblock's type is the single `@var` (the var name is usually
    // omitted on a property).
    let doc_ty = doc.vars.first().and_then(|v| v.ty.as_ref());
    let ty = merge_type(scope, templates, pd.ty.as_ref(), doc_ty);
    let native = native_type(scope, pd.ty.as_ref());
    for elem in &pd.props {
        out.push(PropertyReflection {
            name: interner.resolve(elem.name).to_string(),
            native_ty: native.clone(),
            visibility: pd.modifiers.visibility.unwrap_or(Visibility::Public),
            is_static: pd.modifiers.is_static,
            is_readonly: pd.modifiers.is_readonly,
            ty: ty.clone(),
            has_default: elem.default.is_some(),
            access: PropertyAccess::ReadWrite,
            magic: false,
        });
    }
}

fn reflect_consts(
    scope: &Scope,
    cd: &php_ast::ClassConstDecl,
    interner: &Interner,
    out: &mut Vec<ConstReflection>,
) {
    let declared = cd.ty.as_ref().map(|t| resolve_ast_type(scope, t));
    for c in &cd.consts {
        // An undeclared constant types as its literal initializer (phpstan's
        // constant scalar folding): `const STATUS = 'draft'` is `'draft'`.
        let ty = declared
            .clone()
            .or_else(|| const_literal_type(&c.value))
            .unwrap_or(Type::Mixed);
        out.push(ConstReflection {
            name: interner.resolve(c.name).to_string(),
            visibility: cd.modifiers.visibility.unwrap_or(Visibility::Public),
            ty,
            declared: declared.is_some(),
            is_final: cd.modifiers.is_final,
            int_value: const_int_value(&c.value),
            case_backing: None,
        });
    }
}

/// The literal type of a constant initializer, when it is a scalar literal
/// (through parentheses and a unary sign). Arrays type as bare `array`
/// (element folding is a later step); anything else → `None` (`mixed`).
fn const_literal_type(e: &php_ast::Expr) -> Option<Type> {
    use php_ast::ExprKind as E;
    const LITERAL_CAP: usize = 512;
    match &e.kind {
        E::Int(n) => Some(Type::LiteralInt(*n)),
        E::Float(_) => Some(Type::Float),
        E::Str(bytes) => Some(match std::str::from_utf8(bytes) {
            Ok(s) if s.len() <= LITERAL_CAP => Type::LiteralString(s.into()),
            _ => Type::String,
        }),
        E::Name(n) if n.text.eq_ignore_ascii_case("true") => Some(Type::True),
        E::Name(n) if n.text.eq_ignore_ascii_case("false") => Some(Type::False),
        E::Name(n) if n.text.eq_ignore_ascii_case("null") => Some(Type::Null),
        E::Array { .. } => Some(Type::Array(None)),
        E::Paren(inner) => const_literal_type(inner),
        E::Unary {
            op: php_ast::UnOp::Minus,
            expr,
        } => match const_literal_type(expr)? {
            Type::LiteralInt(n) => Some(Type::LiteralInt(n.wrapping_neg())),
            Type::Float => Some(Type::Float),
            _ => None,
        },
        E::Unary {
            op: php_ast::UnOp::Plus,
            expr,
        } => const_literal_type(expr),
        _ => None,
    }
}

/// The integer value of a constant initializer when it is a plain int literal
/// (through parentheses and a unary sign). Conservative: anything else → `None`.
fn const_int_value(e: &php_ast::Expr) -> Option<i64> {
    use php_ast::ExprKind as E;
    match &e.kind {
        E::Int(n) => Some(*n),
        E::Paren(inner) => const_int_value(inner),
        E::Unary {
            op: php_ast::UnOp::Minus,
            expr,
        } => const_int_value(expr).map(|n| n.wrapping_neg()),
        E::Unary {
            op: php_ast::UnOp::Plus,
            expr,
        } => const_int_value(expr),
        _ => None,
    }
}

/// Reflect a `@method` magic-method declaration.
fn magic_method(
    scope: &Scope,
    class_templates: &[String],
    m: &php_phpdoc::MethodTag,
) -> MethodReflection {
    let templates = class_templates.to_vec();
    MethodReflection {
        name: m.name.clone(),
        visibility: Visibility::Public,
        is_static: m.is_static,
        is_abstract: false,
        is_final: false,
        params: m
            .params
            .iter()
            .map(|p| magic_param(scope, &templates, p))
            .collect(),
        return_type: m
            .return_type
            .as_ref()
            .map(|t| resolve_doc_type(scope, &templates, t))
            .unwrap_or(Type::Mixed),
        explicit_return: m.return_type.is_some(),
        inferred_return: false,
        native_return: Type::Mixed,
        templates,
        deprecated: false,
        pure: false,
        impure: false,
        asserts: Vec::new(),
        self_out: None,
        must_use_return_value: false,
        magic: true,
    }
}

fn magic_param(scope: &Scope, templates: &[String], p: &MethodParam) -> ParamReflection {
    ParamReflection {
        name: p.name.clone().unwrap_or_default(),
        ty: p
            .ty
            .as_ref()
            .map(|t| resolve_doc_type(scope, templates, t))
            .unwrap_or(Type::Mixed),
        by_ref: p.by_ref,
        variadic: p.variadic,
        optional: p.default.is_some() || p.variadic,
        promoted: false,
        explicit: p.ty.is_some(),
        native_ty: Type::Mixed,
        out_ty: None,
        inferred: false,
    }
}

/// Reflect a `@property*` magic property. Skips tags without a name.
fn magic_property(
    scope: &Scope,
    templates: &[String],
    p: &php_phpdoc::PropertyTag,
) -> Option<PropertyReflection> {
    let name = p.name.clone()?;
    Some(PropertyReflection {
        name,
        visibility: Visibility::Public,
        is_static: false,
        is_readonly: p.access == PropertyAccess::ReadOnly,
        ty: p
            .ty
            .as_ref()
            .map(|t| resolve_doc_type(scope, templates, t))
            .unwrap_or(Type::Mixed),
        native_ty: Type::Mixed,
        has_default: false,
        access: p.access,
        magic: true,
    })
}

/// Reflect a parameter list, merging native hints with `@param` types by name.
fn reflect_params(
    scope: &Scope,
    interner: &Interner,
    templates: &[String],
    params: &[AstParam],
    doc: &Doc,
) -> Vec<ParamReflection> {
    params
        .iter()
        .map(|p| {
            let name = interner.resolve(p.name).to_string();
            let doc_ty = doc
                .params
                .iter()
                .find(|dp| dp.name.as_deref() == Some(name.as_str()))
                .and_then(|dp| dp.ty.as_ref());
            let out_ty = doc
                .param_outs
                .iter()
                .find(|dp| dp.name.as_deref() == Some(name.as_str()))
                .and_then(|dp| dp.ty.as_ref())
                .map(|t| resolve_doc_type(scope, templates, t));
            ParamReflection {
                ty: merge_type(scope, templates, p.ty.as_ref(), doc_ty),
                native_ty: native_type(scope, p.ty.as_ref()),
                name,
                by_ref: p.by_ref,
                variadic: p.variadic,
                optional: p.default.is_some() || p.variadic,
                promoted: !p.modifiers.is_empty(),
                explicit: p.ty.is_some() || doc_ty.is_some(),
                out_ty,
                inferred: false,
            }
        })
        .collect()
}

/// Resolve native parents to types, attaching generic args from matching
/// `@extends`/`@implements`/`@use` doc generics (matched by resolved FQN).
fn parents_with_generics(
    scope: &Scope,
    templates: &[String],
    native: &[Name],
    doc_generics: &[DocType],
) -> Vec<Type> {
    let doc_args: Vec<(std::sync::Arc<str>, Vec<Type>)> = doc_generics
        .iter()
        .filter_map(|d| match resolve_doc_type(scope, templates, d) {
            Type::Named { fqn, args } => Some((fqn, args)),
            _ => None,
        })
        .collect();
    native
        .iter()
        .filter_map(|n| {
            let fqn: std::sync::Arc<str> = scope.resolve_class(n).fqn()?.into();
            let args = doc_args
                .iter()
                .find(|(f, _)| *f == fqn)
                .map(|(_, a)| a.clone())
                .unwrap_or_default();
            Some(Type::Named { fqn, args })
        })
        .collect()
}

/// Merge a native type hint and a PHPDoc type: the doc type wins when present,
/// then the native hint, else `mixed`.
fn merge_type(
    scope: &Scope,
    templates: &[String],
    native: Option<&AstType>,
    doc: Option<&DocType>,
) -> Type {
    if let Some(d) = doc {
        return resolve_doc_type(scope, templates, d);
    }
    if let Some(n) = native {
        return resolve_ast_type(scope, n);
    }
    Type::Mixed
}

/// The *native*-hint-only type (ignoring PHPDoc): the resolved native hint, or
/// `mixed` when there is no native type. Used for `treatPhpDocTypesAsCertain:
/// false` native-level checking.
fn native_type(scope: &Scope, native: Option<&AstType>) -> Type {
    native
        .map(|n| resolve_ast_type(scope, n))
        .unwrap_or(Type::Mixed)
}

/// Class templates plus a method's own `@template` names.
fn combine_templates(class_templates: &[String], doc: &Doc) -> Vec<String> {
    let mut t = class_templates.to_vec();
    t.extend(doc.templates.iter().map(|d| d.name.clone()));
    t
}

/// Parse a declaration's docblock text, or an empty [`Doc`] when absent.
fn parse_doc(raw: Option<&str>) -> Doc {
    raw.map(php_phpdoc::parse).unwrap_or_default()
}

/// Whether a docblock declares the symbol side-effect-free: a `@pure`
/// (`@phpstan-pure`/`@psalm-pure`) tag and no `@phpstan-impure`/`@impure`.
fn doc_is_pure(raw: Option<&str>) -> bool {
    let Some(raw) = raw else { return false };
    let (mut pure, mut impure) = (false, false);
    for t in &php_phpdoc::parse_block(raw).tags {
        let base = t
            .name
            .strip_prefix("phpstan-")
            .or_else(|| t.name.strip_prefix("psalm-"))
            .unwrap_or(t.name.as_str());
        match base {
            "pure" => pure = true,
            "impure" => impure = true,
            _ => {}
        }
    }
    pure && !impure
}

/// Resolve a docblock's `@phpstan-assert*` tags against the declaring scope.
fn reflect_asserts(
    scope: &Scope,
    templates: &[String],
    doc: &Doc,
) -> Vec<AssertReflection> {
    doc.asserts
        .iter()
        .map(|a| AssertReflection {
            param: a.param.clone(),
            ty: resolve_doc_type(scope, templates, &a.ty),
            negated: a.negated,
            when: a.when,
        })
        .collect()
}

/// Collect a class's local `@phpstan-type`/`@psalm-type` aliases, keyed by the
/// FQN the alias *name* resolves to (so a member reference to the bare alias
/// name — which resolves to the same phantom FQN — matches, while a
/// fully-qualified real class of the same short name does not). Alias bodies
/// are expanded against one another to a bounded fixpoint (alias-references-
/// alias). Only local `@phpstan-type` is handled here; `@phpstan-import-type`
/// (cross-class) and global config aliases are follow-ups.
fn class_type_aliases(
    scope: &Scope,
    templates: &[String],
    raw: Option<&str>,
) -> HashMap<String, Type> {
    let Some(raw) = raw else {
        return HashMap::new();
    };
    let mut map: HashMap<String, Type> = HashMap::new();
    for tag in &php_phpdoc::parse_block(raw).tags {
        let base = tag
            .name
            .strip_prefix("phpstan-")
            .or_else(|| tag.name.strip_prefix("psalm-"))
            .unwrap_or(tag.name.as_str());
        if base != "type" {
            continue;
        }
        let rest = tag.value.trim_start();
        let name_len = rest
            .char_indices()
            .find_map(|(i, ch)| {
                (!(ch == '_' || ch.is_ascii_alphanumeric())).then_some(i)
            })
            .unwrap_or(rest.len());
        if name_len == 0 {
            continue;
        }
        let name = &rest[..name_len];
        let mut body = rest[name_len..].trim_start();
        if let Some(after_eq) = body.strip_prefix('=') {
            body = after_eq.trim_start();
        }
        // The alias's identity FQN is what the bare name resolves to as a class;
        // skip names that resolve to a reserved keyword type (invalid aliases).
        let Type::Named { fqn: key_fqn, .. } =
            resolve_doc_type(scope, &[], &DocType::Named(name.to_string()))
        else {
            continue;
        };
        let Some((dt, _)) = php_phpdoc::parse_type_prefix(body) else {
            continue;
        };
        let ty = resolve_doc_type(scope, templates, &dt);
        map.insert(key_fqn.trim_start_matches('\\').to_ascii_lowercase(), ty);
    }
    if map.len() > 1 {
        // Fixpoint: expand aliases that reference other aliases (bounded).
        for _ in 0..map.len().min(8) {
            let mut changed = false;
            for key in map.keys().cloned().collect::<Vec<_>>() {
                let cur = map[&key].clone();
                let next = expand_aliases_excluding(&cur, &map, &key);
                if next != cur {
                    map.insert(key, next);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }
    map
}

/// Parse a class's `@phpstan-import-type Name from Other [as Alias]` tags into
/// resolved [`ImportedType`]s (the cross-class lookup happens later, at the
/// index level). `local_fqn` is the FQN the *local* alias name resolves to in
/// this scope (matching how member references to it resolve).
fn class_imported_types(scope: &Scope, raw: Option<&str>) -> Vec<ImportedType> {
    let Some(raw) = raw else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for tag in &php_phpdoc::parse_block(raw).tags {
        let base = tag
            .name
            .strip_prefix("phpstan-")
            .or_else(|| tag.name.strip_prefix("psalm-"))
            .unwrap_or(tag.name.as_str());
        if base != "import-type" {
            continue;
        }
        // `Name from Other` or `Name from Other as Alias`.
        let toks: Vec<&str> = tag.value.split_whitespace().collect();
        let (Some(&name), Some(&kw), Some(&other)) =
            (toks.first(), toks.get(1), toks.get(2))
        else {
            continue;
        };
        if !kw.eq_ignore_ascii_case("from") {
            continue;
        }
        let local = match (toks.get(3), toks.get(4)) {
            (Some(a), Some(alias)) if a.eq_ignore_ascii_case("as") => *alias,
            _ => name,
        };
        let fqn_of = |n: &str| match resolve_doc_type(scope, &[], &DocType::Named(n.to_string())) {
            Type::Named { fqn, .. } => Some(fqn.trim_start_matches('\\').to_ascii_lowercase()),
            _ => None,
        };
        let (Some(source_class), Some(local_fqn)) = (fqn_of(other), fqn_of(local)) else {
            continue;
        };
        out.push(ImportedType {
            local_fqn,
            source_class,
            source_name: name.trim_start_matches('\\').to_ascii_lowercase(),
        });
    }
    out
}

/// Replace `Named` nodes whose resolved FQN keys `aliases` with the alias body.
fn expand_aliases(ty: &Type, aliases: &HashMap<String, Type>) -> Type {
    expand_aliases_excluding(ty, aliases, "")
}

fn expand_aliases_excluding(ty: &Type, aliases: &HashMap<String, Type>, exclude: &str) -> Type {
    ty.clone().map(&mut |part| match part {
        Type::Named { fqn, args } if args.is_empty() => {
            let key = fqn.trim_start_matches('\\').to_ascii_lowercase();
            if key != exclude {
                if let Some(t) = aliases.get(&key) {
                    return t.clone();
                }
            }
            Type::Named { fqn, args }
        }
        other => other,
    })
}

pub(crate) fn expand_member_aliases(
    methods: &mut [MethodReflection],
    properties: &mut [PropertyReflection],
    constants: &mut [ConstReflection],
    aliases: &HashMap<String, Type>,
) {
    let ex = |t: &mut Type| *t = expand_aliases(t, aliases);
    for m in methods.iter_mut() {
        ex(&mut m.return_type);
        ex(&mut m.native_return);
        for p in &mut m.params {
            ex(&mut p.ty);
            ex(&mut p.native_ty);
            if let Some(o) = &mut p.out_ty {
                ex(o);
            }
        }
        for a in &mut m.asserts {
            ex(&mut a.ty);
        }
    }
    for p in properties.iter_mut() {
        ex(&mut p.ty);
        ex(&mut p.native_ty);
    }
    for k in constants.iter_mut() {
        ex(&mut k.ty);
    }
}

/// Whether a docblock explicitly declares the symbol side-effect-having: a
/// `@phpstan-impure`/`@psalm-impure`/`@impure` tag is present.
fn doc_is_impure(raw: Option<&str>) -> bool {
    let Some(raw) = raw else { return false };
    php_phpdoc::parse_block(raw).tags.iter().any(|t| {
        let base = t
            .name
            .strip_prefix("phpstan-")
            .or_else(|| t.name.strip_prefix("psalm-"))
            .unwrap_or(t.name.as_str());
        base == "impure"
    })
}

fn has_nodiscard_attr(attrs: &[AttributeGroup]) -> bool {
    attrs.iter().any(|g| {
        g.attrs.iter().any(|a| {
            a.name
                .text
                .trim_start_matches('\\')
                .eq_ignore_ascii_case("nodiscard")
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_resolve::index_file;

    /// Parse `src`, build the global scope, and reflect the first class.
    fn reflect_first_class(src: &str) -> (ClassReflection, Interner) {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors");
        let idx = index_file(&r.program, &r.interner);
        let fqn = idx.classes[0].fqn.clone();
        // Rebuild the declaring scope (global namespace here).
        let scope = Scope::global();
        let class = first_class(&r.program).expect("a class decl");
        (reflect_class(&scope, &r.interner, &fqn, class), r.interner)
    }

    fn first_class(p: &php_ast::Program) -> Option<&ClassDecl> {
        p.stmts.iter().find_map(|s| match &s.kind {
            php_ast::StmtKind::Class(c) => Some(c),
            _ => None,
        })
    }

    fn first_function(src: &str) -> (FunctionReflection, Interner) {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors");
        let scope = Scope::global();
        let f = r.program.stmts.iter().find_map(|s| match &s.kind {
            php_ast::StmtKind::Function(f) => Some(f),
            _ => None,
        });
        let refl = reflect_function(&scope, &r.interner, f.expect("a function"));
        (refl, r.interner)
    }

    #[test]
    fn constructor_promoted_params_are_properties() {
        let (c, _) = reflect_first_class(
            r#"<?php class Cursor {
                public function __construct(private \Foo\Bar $output, public int $count = 0) {}
            }"#,
        );
        let out = c
            .properties
            .iter()
            .find(|p| p.name == "output")
            .expect("$output property");
        assert_eq!(out.visibility, Visibility::Private);
        assert_eq!(out.ty.to_string(), "Foo\\Bar");
        let count = c
            .properties
            .iter()
            .find(|p| p.name == "count")
            .expect("$count property");
        assert_eq!(count.visibility, Visibility::Public);
        assert_eq!(count.ty, Type::Int);
        assert!(count.has_default);
    }

    #[test]
    fn non_promoted_constructor_param_is_not_a_property() {
        let (c, _) =
            reflect_first_class(r#"<?php class C { public function __construct(int $x) {} }"#);
        assert!(c.properties.iter().all(|p| p.name != "x"));
    }

    #[test]
    fn function_params_and_return_native() {
        let (f, _) =
            first_function(r#"<?php function add(int $a, int $b = 0): int { return $a + $b; }"#);
        assert_eq!(f.fqn, "add");
        assert_eq!(f.params.len(), 2);
        assert_eq!(f.params[0].name, "a");
        assert_eq!(f.params[0].ty, Type::Int);
        assert!(!f.params[0].optional);
        assert!(f.params[1].optional);
        assert_eq!(f.return_type, Type::Int);
    }

    #[test]
    fn phpdoc_refines_native_param_and_return() {
        let (f, _) = first_function(
            r#"<?php
            /**
             * @param string[] $names
             * @return list<int>
             */
            function f(array $names): array { return []; }"#,
        );
        assert_eq!(f.params[0].ty.to_string(), "array<int|string, string>");
        assert_eq!(f.return_type.to_string(), "list<int>");
    }

    #[test]
    fn method_visibility_static_and_abstract() {
        let (c, _) = reflect_first_class(
            r#"<?php
            abstract class Repo {
                public function find(int $id): ?string { return null; }
                protected static function make(): static { }
                abstract public function all(): array;
            }"#,
        );
        assert!(c.is_abstract);
        let find = c.methods.iter().find(|m| m.name == "find").unwrap();
        assert_eq!(find.visibility, Visibility::Public);
        assert_eq!(find.return_type, Type::Nullable(Box::new(Type::String)));
        let make = c.methods.iter().find(|m| m.name == "make").unwrap();
        assert!(make.is_static && make.visibility == Visibility::Protected);
        assert_eq!(make.return_type, Type::StaticType);
        let all = c.methods.iter().find(|m| m.name == "all").unwrap();
        assert!(all.is_abstract);
    }

    #[test]
    fn properties_merge_var_and_promotion() {
        let (c, _) = reflect_first_class(
            r#"<?php
            class Box {
                /** @var array<string, int> */
                private array $items = [];
                public readonly string $name;
                public function __construct(public int $size) {}
            }"#,
        );
        let items = c.properties.iter().find(|p| p.name == "items").unwrap();
        assert_eq!(items.ty.to_string(), "array<string, int>");
        assert_eq!(items.visibility, Visibility::Private);
        assert!(items.has_default);
        let name = c.properties.iter().find(|p| p.name == "name").unwrap();
        assert!(name.is_readonly);
        // Constructor-promoted param shows up as a param on __construct.
        let ctor = c.methods.iter().find(|m| m.name == "__construct").unwrap();
        assert!(ctor.params[0].promoted && ctor.params[0].ty == Type::Int);
    }

    #[test]
    fn local_type_aliases_expand_in_members() {
        let (c, _) = reflect_first_class(
            r#"<?php
            /**
             * @phpstan-type UserId = int
             * @phpstan-type UserData = array{id: UserId, name: string}
             */
            class Service {
                /** @param UserData $data */
                public function save($data): void {}
                /** @return UserData */
                public function load() { return []; }
            }"#,
        );
        let want = "array{id: int, name: string}";
        let save = c.methods.iter().find(|m| m.name == "save").unwrap();
        // The alias (and its nested alias UserId → int) is fully expanded.
        assert_eq!(save.params[0].ty.to_string(), want);
        let load = c.methods.iter().find(|m| m.name == "load").unwrap();
        assert_eq!(load.return_type.to_string(), want);
    }

    #[test]
    fn alias_does_not_shadow_fully_qualified_class() {
        // A local alias `Data` must not replace a fully-qualified `\Other\Data`.
        let (c, _) = reflect_first_class(
            r#"<?php
            /** @phpstan-type Data = array{x: int} */
            class Service {
                /** @param \Other\Data $d */
                public function m($d): void {}
            }"#,
        );
        let m = c.methods.iter().find(|m| m.name == "m").unwrap();
        assert_eq!(m.params[0].ty.to_string(), "Other\\Data");
    }

    #[test]
    fn class_constants() {
        let (c, _) = reflect_first_class(
            r#"<?php
            class C {
                const A = 1;
                final protected const int B = 2;
                const S = 'draft';
                const NEG = -3;
                const F = false;
            }"#,
        );
        let a = c.constants.iter().find(|k| k.name == "A").unwrap();
        assert_eq!(a.visibility, Visibility::Public);
        // Undeclared constants type as their literal initializer.
        assert_eq!(a.ty, Type::LiteralInt(1));
        assert!(!a.declared);
        let b = c.constants.iter().find(|k| k.name == "B").unwrap();
        assert!(b.is_final && b.visibility == Visibility::Protected);
        assert_eq!(b.ty, Type::Int);
        assert!(b.declared);
        let s = c.constants.iter().find(|k| k.name == "S").unwrap();
        assert_eq!(s.ty, Type::LiteralString("draft".into()));
        let neg = c.constants.iter().find(|k| k.name == "NEG").unwrap();
        assert_eq!(neg.ty, Type::LiteralInt(-3));
        let f = c.constants.iter().find(|k| k.name == "F").unwrap();
        assert_eq!(f.ty, Type::False);
    }

    #[test]
    fn magic_methods_and_properties() {
        let (c, _) = reflect_first_class(
            r#"<?php
            /**
             * @method static \Builder where(string $column, mixed $value = null)
             * @property-read int $id
             * @property string $name
             */
            class Model {}"#,
        );
        let m = c.methods.iter().find(|m| m.name == "where").unwrap();
        assert!(m.magic && m.is_static);
        assert_eq!(m.return_type.to_string(), "Builder");
        assert_eq!(m.params.len(), 2);
        assert_eq!(m.params[0].ty, Type::String);
        assert!(m.params[1].optional);
        let id = c.properties.iter().find(|p| p.name == "id").unwrap();
        assert!(id.magic && id.is_readonly && id.ty == Type::Int);
        let name = c.properties.iter().find(|p| p.name == "name").unwrap();
        assert!(name.magic && name.access == PropertyAccess::ReadWrite);
    }

    #[test]
    fn generic_extends_and_implements_attach_args() {
        let (c, _) = reflect_first_class(
            r#"<?php
            /**
             * @extends \ArrayObject<int, string>
             * @implements \IteratorAggregate<int, string>
             */
            class Bag extends \ArrayObject implements \IteratorAggregate {}"#,
        );
        assert_eq!(c.parents[0].to_string(), "ArrayObject<int, string>");
        assert_eq!(
            c.interfaces[0].to_string(),
            "IteratorAggregate<int, string>"
        );
    }

    #[test]
    fn class_templates_resolve_in_members() {
        let (c, _) = reflect_first_class(
            r#"<?php
            /**
             * @template T
             */
            class Collection {
                /** @param T $item */
                public function add($item): void {}
                /** @return T */
                public function first() {}
            }"#,
        );
        assert_eq!(c.templates, ["T"]);
        let add = c.methods.iter().find(|m| m.name == "add").unwrap();
        assert_eq!(add.params[0].ty, Type::TemplateVar("T".into()));
        let first = c.methods.iter().find(|m| m.name == "first").unwrap();
        assert_eq!(first.return_type, Type::TemplateVar("T".into()));
    }
}
