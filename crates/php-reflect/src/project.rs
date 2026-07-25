//! M-T3: the **project reflection index** + inherited-member lookup.
//!
//! [`ReflectionIndex`] aggregates the [`ClassReflection`]s / [`FunctionReflection`]s
//! of many files into one queryable map (the reflection counterpart of
//! `php_index::ProjectIndex`, which only holds names). On top of it sit the
//! member-resolution queries the type system needs: looking up a method,
//! property, or constant *through* a class's hierarchy
//! (extends → implemented interfaces → used traits → `@mixin`), substituting
//! generic type arguments from each parent's `@extends`/`@implements`/`@use`
//! type args as the walk ascends.

use crate::{
    reflect_class, reflect_function, ClassReflection, ConstReflection, FunctionReflection,
    MethodReflection, PropertyReflection,
};
use php_ast::{ClassDecl, ClassKind, Member, Program, Stmt, StmtKind};
use php_intern::Interner;
use php_resolve::{depsrec, for_each_region, Scope, SymbolKey, SymbolOrigin};
use php_types::{PhpVersion, Type};
use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::Arc;

/// A map from `@template` names to the types bound for them along a hierarchy walk.
type Subst = HashMap<String, Type>;

/// How a parsed file participates in reflection.
pub type SourceKind = SymbolOrigin;

/// A member found via hierarchy lookup, plus the class that declared it. Member
/// types have generic template variables substituted for the query's bindings.
/// The member is **borrowed from the index** when no substitution applies (the
/// common case — lookups used to deep-clone every member) and owned only when
/// generic substitution had to rewrite types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Found<'a, T: Clone> {
    pub member: std::borrow::Cow<'a, T>,
    /// FQN of the class/interface/trait the member was declared on.
    pub declaring_class: &'a str,
}

/// Stored AST body metadata for a reflected function or method.
#[derive(Debug, Clone)]
struct BodyRecord {
    body: Vec<Stmt>,
    scope: Scope,
    path: Option<String>,
    source_kind: SourceKind,
}

/// A borrowed function/method body plus the source metadata needed by callers
/// that emit diagnostics against that body.
#[derive(Debug, Clone, Copy)]
pub struct BodyMetadata<'a> {
    pub body: &'a [Stmt],
    pub scope: &'a Scope,
    pub path: Option<&'a str>,
    pub source_kind: SourceKind,
}

impl BodyRecord {
    fn metadata(&self) -> BodyMetadata<'_> {
        BodyMetadata {
            body: self.body.as_slice(),
            scope: &self.scope,
            path: self.path.as_deref(),
            source_kind: self.source_kind,
        }
    }
}

/// A reflected function plus the AST declaration it came from.
#[derive(Debug)]
pub struct ReflectedFunction<'a> {
    pub decl: &'a php_ast::FunctionDecl,
    pub reflection: FunctionReflection,
}

/// A reflected class-like declaration plus the AST declaration it came from.
#[derive(Debug)]
pub struct ReflectedClass<'a> {
    pub decl: &'a ClassDecl,
    pub reflection: ClassReflection,
}

/// The reflected declarations discovered in one parsed source unit.
#[derive(Debug, Default)]
pub struct ReflectedFile<'a> {
    pub classes: Vec<ReflectedClass<'a>>,
    pub functions: Vec<ReflectedFunction<'a>>,
}

/// Reflect every named class-like and function declaration in a parsed file.
pub fn reflect_file<'a>(program: &'a Program, interner: &Interner) -> ReflectedFile<'a> {
    let mut out = ReflectedFile::default();
    for_each_region(&program.stmts, interner, |scope, region| {
        for st in region {
            visit_reflectable_decls(scope, st, &mut |scope, decl| match decl {
                ReflectableDecl::Function(f) => {
                    out.functions.push(ReflectedFunction {
                        decl: f,
                        reflection: reflect_function(scope, interner, f),
                    });
                }
                ReflectableDecl::Class(c) => {
                    let Some(name) = c.name else { return };
                    let fqn = scope.qualify(interner.resolve(name));
                    out.classes.push(ReflectedClass {
                        decl: c,
                        reflection: reflect_class(scope, interner, &fqn, c),
                    });
                }
            });
        }
    });
    out
}

enum ReflectableDecl<'a> {
    Function(&'a php_ast::FunctionDecl),
    Class(&'a ClassDecl),
}

fn visit_reflectable_decls<'a>(
    scope: &Scope,
    st: &'a php_ast::Stmt,
    f: &mut impl FnMut(&Scope, ReflectableDecl<'a>),
) {
    match &st.kind {
        StmtKind::Function(func) => {
            f(scope, ReflectableDecl::Function(func));
            for st in &func.body {
                visit_reflectable_decls(scope, st, f);
            }
        }
        StmtKind::Class(class) => {
            f(scope, ReflectableDecl::Class(class));
            for member in &class.members {
                if let Member::Method(method) = member {
                    if let Some(body) = &method.body {
                        for st in body {
                            visit_reflectable_decls(scope, st, f);
                        }
                    }
                }
            }
        }
        StmtKind::Block(body) => {
            for st in body {
                visit_reflectable_decls(scope, st, f);
            }
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            visit_reflectable_decls(scope, then, f);
            for elseif in elseifs {
                visit_reflectable_decls(scope, &elseif.body, f);
            }
            if let Some(els) = els {
                visit_reflectable_decls(scope, els, f);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => visit_reflectable_decls(scope, body, f),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for st in body {
                visit_reflectable_decls(scope, st, f);
            }
            for catch in catches {
                for st in &catch.body {
                    visit_reflectable_decls(scope, st, f);
                }
            }
            if let Some(finally) = finally {
                for st in finally {
                    visit_reflectable_decls(scope, st, f);
                }
            }
        }
        StmtKind::Switch { cases, .. } => {
            for case in cases {
                for st in &case.body {
                    visit_reflectable_decls(scope, st, f);
                }
            }
        }
        StmtKind::Declare {
            body: Some(body), ..
        } => {
            visit_reflectable_decls(scope, body, f);
        }
        StmtKind::Expr(_)
        | StmtKind::Echo(_)
        | StmtKind::Return(_)
        | StmtKind::Break(_)
        | StmtKind::Continue(_)
        | StmtKind::Goto(_)
        | StmtKind::Label(_)
        | StmtKind::Global(_)
        | StmtKind::StaticVars(_)
        | StmtKind::Unset(_)
        | StmtKind::Declare { body: None, .. }
        | StmtKind::Namespace { .. }
        | StmtKind::Use(_)
        | StmtKind::GroupUse { .. }
        | StmtKind::ConstDecl { .. }
        | StmtKind::HaltCompiler(_)
        | StmtKind::InlineHtml(_)
        | StmtKind::Nop
        | StmtKind::Error => {}
    }
}

/// All reflected classes/functions across a set of files, keyed for lookup.
///
/// Values are `Arc`-shared so per-file reflection artifacts (see
/// [`reflect_artifact`]) can be cached across incremental re-analysis passes and
/// merged back into a fresh index by reference-count bump instead of deep clone.
/// `Clone` on the index itself is correspondingly cheap (map-of-`Arc` copies).
#[derive(Debug, Default, Clone)]
pub struct ReflectionIndex {
    /// Lowercased FQN → class reflection (class names are case-insensitive).
    classes: HashMap<String, Arc<ClassReflection>>,
    /// Lowercased FQN → function reflection.
    functions: HashMap<String, Arc<FunctionReflection>>,
    /// Callable bodies + their declaring [`Scope`] for interprocedural per-call
    /// return inference and context diagnostics. Keyed by `key(fqn)` for free
    /// functions and `key(declaring_class)::name_lower` for methods. The scope is
    /// kept so the body's name references resolve in *their* namespace, not the
    /// caller's; this is sound only because all files share one interner (symbols
    /// are global).
    bodies: HashMap<String, Arc<BodyRecord>>,
}

/// One function/method's inferred signature, produced by whole-project signature
/// inference and applied to the stored reflections via
/// [`ReflectionIndex::apply_inferred`]. Every entry is advisory: `None` means
/// "leave the declared type", a `Some` only overwrites a slot that was *not*
/// explicitly declared.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InferredSig {
    /// Inferred type per parameter position. `None` = leave the parameter alone.
    pub params: Vec<Option<Type>>,
    /// Inferred return type, or `None` to leave the declared return.
    pub ret: Option<Type>,
}

impl InferredSig {
    /// A signature carrying only an inferred return type.
    pub fn ret_only(ret: Type) -> Self {
        InferredSig {
            params: Vec::new(),
            ret: Some(ret),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.ret.is_none() && self.params.iter().all(Option::is_none)
    }
}

/// The whole-project result of signature inference: synthesized signatures for
/// fully untyped free functions (keyed by FQN) and methods (keyed by
/// `(class_fqn, method_name)`). Built by `php_infer::signatures` and applied to a
/// [`ReflectionIndex`] in place.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InferredSignatures {
    pub fns: HashMap<String, InferredSig>,
    pub methods: HashMap<(String, String), InferredSig>,
}

impl InferredSignatures {
    pub fn is_empty(&self) -> bool {
        self.fns.is_empty() && self.methods.is_empty()
    }
}

impl ReflectionIndex {
    pub fn new() -> Self {
        Self::default()
    }

    /// A fresh index pre-loaded with the typed built-in **function** signatures
    /// (Cap #4). Project files added afterward (`add_file`) override a builtin of
    /// the same FQN. This is what makes `argument.type` / return inference work
    /// on `strlen`, `array_map`, … without any per-rule special-casing.
    pub fn with_builtins() -> Self {
        Self::with_builtins_for(PhpVersion::default())
    }

    /// A fresh index pre-loaded with typed built-in signatures for `version`.
    pub fn with_builtins_for(version: PhpVersion) -> Self {
        let mut idx = Self::new();
        for fr in crate::builtins::builtin_functions_for(version) {
            idx.functions.insert(function_key(&fr.fqn), Arc::new(fr));
        }
        for cr in crate::builtins::builtin_classes_for(version) {
            idx.classes.insert(class_key(&cr.fqn), Arc::new(cr));
        }
        idx
    }

    /// Reflect every class and function in a parsed file and add them to the
    /// index. Later definitions of the same FQN overwrite earlier ones.
    pub fn add_file(&mut self, program: &Program, interner: &Interner) {
        self.add_file_as(program, interner, SourceKind::Analyzed);
    }

    /// Reflect every class and function in a parsed file, with scan-only files
    /// prevented from replacing curated built-in reflections.
    pub fn add_file_as(&mut self, program: &Program, interner: &Interner, kind: SourceKind) {
        self.add_file_labeled_as(None, program, interner, kind);
    }

    /// Reflect every class and function in a parsed file and retain `path` for
    /// body metadata. The legacy [`add_file_as`](Self::add_file_as) remains for
    /// callers that only need signatures.
    pub fn add_file_labeled_as(
        &mut self,
        path: Option<&str>,
        program: &Program,
        interner: &Interner,
        kind: SourceKind,
    ) {
        // One code path with incremental analysis: build the per-file artifact,
        // then merge it — so cached artifacts replay the exact same inserts.
        let artifact = reflect_artifact(path, program, interner, kind);
        self.add_artifact(&artifact);
    }

    /// Merge a previously built per-file reflection artifact. Entries replay in
    /// declaration order with the same scan-vs-builtin guards as
    /// [`add_file_labeled_as`](Self::add_file_labeled_as); `Arc` values are
    /// shared, not deep-cloned, so re-merging a whole project of cached
    /// artifacts each incremental pass is cheap.
    pub fn add_artifact(&mut self, artifact: &FileReflectionArtifact) {
        let kind = artifact.kind;
        for entry in &artifact.entries {
            match entry {
                ArtifactEntry::Function {
                    key,
                    reflection,
                    body,
                } => {
                    let existing = self.functions.get(key).map(|f| f.builtin);
                    if !accepts_redeclaration(kind, artifact.stub, existing) {
                        continue;
                    }
                    self.bodies.insert(key.clone(), Arc::clone(body));
                    self.functions.insert(key.clone(), Arc::clone(reflection));
                }
                ArtifactEntry::Class {
                    key,
                    reflection,
                    bodies,
                } => {
                    let existing = self.classes.get(key).map(|c| c.builtin);
                    if !accepts_redeclaration(kind, artifact.stub, existing) {
                        continue;
                    }
                    for (body_key, body) in bodies {
                        self.bodies.insert(body_key.clone(), Arc::clone(body));
                    }
                    self.classes.insert(key.clone(), Arc::clone(reflection));
                }
            }
        }
    }

    /// Look up a class by FQN (case-insensitive, leading `\` ignored).
    pub fn class(&self, fqn: &str) -> Option<&ClassReflection> {
        self.class_by_key_ref(fqn)
    }

    /// Resolve every class's `@phpstan-import-type` declarations now that all
    /// classes are indexed: look up each imported alias in its source class's
    /// exported `type_aliases`, then re-expand the importing class's member
    /// types. Call once after all files/artifacts are added; idempotent and
    /// deterministic (safe to re-run per incremental pass). A missing source
    /// class or alias is silently skipped (graceful — the reference stays a
    /// lenient unresolved `Named`).
    pub fn resolve_type_imports(&mut self) {
        // Collect substitutions first (immutable borrow), then apply.
        let mut updates: Vec<(String, std::collections::HashMap<String, php_types::Type>)> =
            Vec::new();
        for (key, cls) in &self.classes {
            if cls.imported_types.is_empty() {
                continue;
            }
            let mut import_map = std::collections::HashMap::new();
            for imp in &cls.imported_types {
                if let Some(src) = self.classes.get(&class_key(&imp.source_class)) {
                    if let Some(ty) = src.type_aliases.get(&imp.source_name) {
                        import_map.insert(imp.local_fqn.clone(), ty.clone());
                    }
                }
            }
            if !import_map.is_empty() {
                updates.push((key.clone(), import_map));
            }
        }
        for (key, import_map) in updates {
            if let Some(cls_arc) = self.classes.get_mut(&key) {
                let cls = Arc::make_mut(cls_arc);
                crate::model::expand_member_aliases(
                    &mut cls.methods,
                    &mut cls.properties,
                    &mut cls.constants,
                    &import_map,
                );
            }
        }
    }

    /// Expand global `typeAliases` (from config) into every reflected member and
    /// function type. Each alias name is matched by its unqualified short name
    /// (so it works regardless of the using file's namespace), but a `Named` that
    /// resolves to a *real indexed class* is never rewritten — a real class of the
    /// same name wins, keeping the collision FP-safe. `defs` maps the alias name
    /// to its PHPDoc type string (resolved in the global namespace). Call once
    /// after all files are indexed; deterministic and idempotent.
    pub fn apply_global_type_aliases(&mut self, defs: &std::collections::HashMap<String, String>) {
        if defs.is_empty() {
            return;
        }
        let scope = Scope::global();
        let mut map: std::collections::HashMap<String, php_types::Type> =
            std::collections::HashMap::new();
        for (name, body) in defs {
            let Some((dt, _)) = php_phpdoc::parse_type_prefix(body.trim()) else {
                continue;
            };
            let ty = crate::resolve_doc_type(&scope, &[], &dt);
            map.insert(name.trim_start_matches('\\').to_ascii_lowercase(), ty);
        }
        if map.is_empty() {
            return;
        }
        // Fixpoint: aliases may reference each other (bounded).
        for _ in 0..map.len().min(8) {
            let mut changed = false;
            for key in map.keys().cloned().collect::<Vec<_>>() {
                let cur = map[&key].clone();
                let next = expand_global_alias(&cur, &map, &key);
                if next != cur {
                    map.insert(key, next);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        // Owned set of real class keys so the guard closure doesn't borrow `self`
        // while its maps are mutated.
        let real: std::collections::HashSet<String> = self.classes.keys().cloned().collect();
        let ex = |t: &mut php_types::Type| *t = expand_global_alias_guarded(t, &map, &real);
        for cls_arc in self.classes.values_mut() {
            let cls = Arc::make_mut(cls_arc);
            for m in &mut cls.methods {
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
                if let Some(s) = &mut m.self_out {
                    ex(s);
                }
            }
            for p in &mut cls.properties {
                ex(&mut p.ty);
                ex(&mut p.native_ty);
            }
            for k in &mut cls.constants {
                ex(&mut k.ty);
            }
        }
        for fn_arc in self.functions.values_mut() {
            let f = Arc::make_mut(fn_arc);
            ex(&mut f.return_type);
            ex(&mut f.native_return);
            for p in &mut f.params {
                ex(&mut p.ty);
                ex(&mut p.native_ty);
                if let Some(o) = &mut p.out_ty {
                    ex(o);
                }
            }
            for a in &mut f.asserts {
                ex(&mut a.ty);
            }
        }
    }

    /// Look up a function by FQN (case-insensitive, leading `\` ignored).
    pub fn function(&self, fqn: &str) -> Option<&FunctionReflection> {
        depsrec::note_surface(fqn);
        with_ci_key(fqn, |key| self.functions.get(key).map(Arc::as_ref))
    }

    /// The single choke point for class-map reads: records the consulted name for
    /// incremental dependency tracking (a no-op outside recording brackets). The
    /// canonical key is built in the reused scratch buffer (no per-lookup alloc).
    fn class_by_key_ref(&self, fqn: &str) -> Option<&ClassReflection> {
        with_ci_key(fqn, |key| {
            depsrec::note_surface(key);
            self.classes.get(key).map(Arc::as_ref)
        })
    }

    /// Number of indexed classes.
    pub fn class_count(&self) -> usize {
        self.classes.len()
    }

    /// Whether `sub` is `sup` or transitively extends/implements/uses it
    /// (reflexive, case-insensitive). Walks parents, interfaces, and traits;
    /// tolerant of unknown links and cycles. Returns `false` if the relationship
    /// can't be established from the indexed classes — callers that must avoid
    /// false positives should treat an *unknown* class leniently themselves.
    pub fn is_subclass_of(&self, sub: &str, sup: &str) -> bool {
        // `sup` is compared per level, so its canonical key is built once (owned);
        // the per-level `sub` keys go through the scratch buffer inside `is_sub_fqn`.
        let sup_key = class_key(sup);
        let mut visited = Vec::new();
        self.is_sub_fqn(sub, &sup_key, &mut visited)
    }

    /// Extract the key/value pair yielded by an iterable value, when reflection
    /// has enough information to do so without guessing.
    pub fn iterable_key_value_on_type(&self, ty: &Type) -> Option<(Type, Type)> {
        let ty = ty.peel_non_empty();
        let mut visited = Vec::new();
        self.iterable_key_value(ty, &mut visited)
    }

    fn iterable_key_value(&self, ty: &Type, visited: &mut Vec<String>) -> Option<(Type, Type)> {
        match ty {
            Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => Some((kv.0.clone(), kv.1.clone())),
            Type::List(value) => Some((Type::Int, (**value).clone())),
            Type::Shape { fields, sealed } => {
                let mut keys: Vec<Type> = fields.iter().map(shape_field_key_type).collect();
                let mut values: Vec<Type> = fields.iter().map(|f| f.ty.clone()).collect();
                if !sealed {
                    keys.push(Type::Mixed);
                    values.push(Type::Mixed);
                }
                Some((Type::union(keys), Type::union(values)))
            }
            Type::Nullable(inner) => self.iterable_key_value(inner, visited),
            Type::Union(parts) => {
                if parts.is_empty() {
                    return None;
                }
                let mut keys = Vec::new();
                let mut values = Vec::new();
                for part in parts.iter() {
                    let mut branch_seen = visited.clone();
                    let (k, v) = self.iterable_key_value(part, &mut branch_seen)?;
                    keys.push(k);
                    values.push(v);
                }
                Some((Type::union(keys), Type::union(values)))
            }
            Type::Intersection(parts) => parts.iter().find_map(|part| {
                let mut branch_seen = visited.clone();
                self.iterable_key_value(part, &mut branch_seen)
            }),
            Type::Named { fqn, args } => self.iterable_key_value_named(fqn, args, visited),
            _ => None,
        }
    }

    fn iterable_key_value_named(
        &self,
        fqn: &str,
        args: &[Type],
        visited: &mut Vec<String>,
    ) -> Option<(Type, Type)> {
        if let Some(kv) = direct_iterable_named_key_value(fqn, args) {
            return Some(kv);
        }

        let key = class_key(fqn);
        if visited.contains(&key) {
            return None;
        }
        visited.push(key);

        let class = self.class_by_key_ref(fqn)?;
        let subst = self.receiver_subst(fqn, args);
        let parents = class
            .traits
            .iter()
            .chain(&class.parents)
            .chain(&class.interfaces)
            .chain(&class.mixins);
        for parent in parents {
            let Type::Named {
                fqn: parent_fqn,
                args: parent_args,
            } = parent
            else {
                continue;
            };
            let parent_args: Vec<Type> = parent_args
                .iter()
                .map(|arg| subst_type(arg, &subst))
                .collect();
            let mut branch_seen = visited.clone();
            if let Some(kv) =
                self.iterable_key_value_named(parent_fqn, &parent_args, &mut branch_seen)
            {
                return Some(kv);
            }
        }
        None
    }

    fn is_sub_fqn(
        &self,
        sub: &str,
        sup_key: &str,
        visited: &mut Vec<*const ClassReflection>,
    ) -> bool {
        // Reflexive: compare canonical keys without allocating for `sub`.
        if with_ci_key(sub, |sk| sk == sup_key) {
            return true;
        }
        let Some(c) = self.class_by_key_ref(sub) else {
            return false;
        };
        let id = std::ptr::from_ref(c);
        if visited.contains(&id) {
            return false;
        }
        visited.push(id);
        c.parents
            .iter()
            .chain(&c.interfaces)
            .chain(&c.traits)
            .any(|p| match p {
                Type::Named { fqn, .. } => self.is_sub_fqn(fqn, sup_key, visited),
                _ => false,
            })
    }

    /// Resolve a method by name through `class_fqn`'s hierarchy (own members
    /// first, then traits, parent class, interfaces, mixins). Method names match
    /// case-insensitively. Returns the method with generic args substituted.
    pub fn find_method(&self, class_fqn: &str, name: &str) -> Option<Found<'_, MethodReflection>> {
        let mut visited = Vec::new();
        self.ascend(
            class_fqn,
            Subst::new(),
            &mut visited,
            &mut |class, subst| {
                class
                    .methods
                    .iter()
                    .find(|m| m.name.eq_ignore_ascii_case(name))
                    .map(|m| Found {
                        member: subst_method(m, subst),
                        declaring_class: &class.fqn,
                    })
            },
        )
    }

    /// Resolve a method through the hierarchy of a concrete receiver type,
    /// substituting the receiver's own generic arguments before walking parents.
    pub fn find_method_on_type(
        &self,
        receiver: &Type,
        name: &str,
    ) -> Option<Found<'_, MethodReflection>> {
        let (fqn, subst) = self.receiver_named_subst(receiver)?;
        let mut visited = Vec::new();
        self.ascend(fqn, subst, &mut visited, &mut |class, subst| {
            class
                .methods
                .iter()
                .find(|m| m.name.eq_ignore_ascii_case(name))
                .map(|m| Found {
                    member: subst_method(m, subst),
                    declaring_class: &class.fqn,
                })
        })
    }

    /// Whether every known concrete descendant of an abstract class/interface is
    /// final and exposes `method`. This is an intentionally narrow escape hatch
    /// for member-existence checks on abstract receiver types: if a library's
    /// hierarchy is closed by final leaf classes, a call may be valid even when
    /// the abstract parent does not declare the method.
    pub fn final_concrete_descendants_have_method(&self, class_fqn: &str, method: &str) -> bool {
        // A whole-index scan: the answer can change when *any* class changes,
        // so incremental invalidation must treat this as a global dependency.
        depsrec::note_global();
        let Some(base) = self.class(class_fqn) else {
            return false;
        };
        if !base.is_abstract && !matches!(base.kind, ClassKind::Interface) {
            return false;
        }

        let base_key = class_key(class_fqn);
        let mut saw_concrete = false;
        for class in self.classes.values() {
            if class_key(&class.fqn) == base_key || !self.is_subclass_of(&class.fqn, class_fqn) {
                continue;
            }
            if !matches!(class.kind, ClassKind::Class | ClassKind::Enum) || class.is_abstract {
                continue;
            }
            saw_concrete = true;
            if !class.is_final || self.find_method(&class.fqn, method).is_none() {
                return false;
            }
        }
        saw_concrete
    }

    /// Resolve a property by name (without `$`) through the hierarchy. Property
    /// names are case-sensitive.
    pub fn find_property(
        &self,
        class_fqn: &str,
        name: &str,
    ) -> Option<Found<'_, PropertyReflection>> {
        let mut visited = Vec::new();
        self.ascend(
            class_fqn,
            Subst::new(),
            &mut visited,
            &mut |class, subst| {
                class
                    .properties
                    .iter()
                    .find(|p| p.name == name)
                    .map(|p| Found {
                        member: subst_property(p, subst),
                        declaring_class: &class.fqn,
                    })
            },
        )
    }

    /// Resolve a property through the hierarchy of a concrete receiver type,
    /// substituting the receiver's own generic arguments before walking parents.
    pub fn find_property_on_type(
        &self,
        receiver: &Type,
        name: &str,
    ) -> Option<Found<'_, PropertyReflection>> {
        let (fqn, subst) = self.receiver_named_subst(receiver)?;
        let mut visited = Vec::new();
        self.ascend(fqn, subst, &mut visited, &mut |class, subst| {
            class
                .properties
                .iter()
                .find(|p| p.name == name)
                .map(|p| Found {
                    member: subst_property(p, subst),
                    declaring_class: &class.fqn,
                })
        })
    }

    /// Resolve a class constant by name through the hierarchy. Constant names are
    /// case-sensitive.
    pub fn find_constant(&self, class_fqn: &str, name: &str) -> Option<Found<'_, ConstReflection>> {
        let mut visited = Vec::new();
        self.ascend(
            class_fqn,
            Subst::new(),
            &mut visited,
            &mut |class, subst| {
                class
                    .constants
                    .iter()
                    .find(|c| c.name == name)
                    .map(|c| Found {
                        member: subst_constant(c, subst),
                        declaring_class: &class.fqn,
                    })
            },
        )
    }

    /// Walk `fqn` and its ancestors in PHP member-resolution order, calling `f`
    /// with each class and the active template substitution; returns the first
    /// `Some(f(...))`. `visited` (resolved class identities — `Arc` pointers, so
    /// no per-level key allocation) breaks diamonds/cycles.
    fn ascend<'s, T>(
        &'s self,
        fqn: &str,
        subst: Subst,
        visited: &mut Vec<*const ClassReflection>,
        f: &mut impl FnMut(&'s ClassReflection, &Subst) -> Option<T>,
    ) -> Option<T> {
        let class = self.class_by_key_ref(fqn)?;
        let id = std::ptr::from_ref(class);
        if visited.contains(&id) {
            return None;
        }
        visited.push(id);
        if let Some(found) = f(class, &subst) {
            return Some(found);
        }
        // Traits, then the parent class, then interfaces, then mixins.
        let parents = class
            .traits
            .iter()
            .chain(&class.parents)
            .chain(&class.interfaces)
            .chain(&class.mixins);
        for parent in parents {
            if let Type::Named { fqn: pf, args } = parent {
                let psubst = self.compose(pf, args, &subst);
                if let Some(found) = self.ascend(pf, psubst, visited, f) {
                    return Some(found);
                }
            }
        }
        None
    }

    /// Build the substitution for entering parent `pf` applied with `args`: map
    /// the parent's declared `@template` names to `args` (each first rewritten
    /// through the outer substitution so bindings compose down the chain).
    fn compose(&self, pf: &str, args: &[Type], outer: &Subst) -> Subst {
        let mut map = Subst::new();
        if let Some(parent) = self.class_by_key_ref(pf) {
            for (name, arg) in parent.templates.iter().zip(args) {
                map.insert(name.clone(), subst_type(arg, outer));
            }
        }
        map
    }

    fn receiver_named_subst<'a>(&self, receiver: &'a Type) -> Option<(&'a str, Subst)> {
        match receiver {
            Type::Named { fqn, args } => Some((&**fqn, self.receiver_subst(fqn, args))),
            Type::Nullable(inner) => self.receiver_named_subst(inner),
            _ => None,
        }
    }

    fn receiver_subst(&self, fqn: &str, args: &[Type]) -> Subst {
        let mut map = Subst::new();
        if let Some(class) = self.class_by_key_ref(fqn) {
            for (name, arg) in class.templates.iter().zip(args) {
                map.insert(name.clone(), arg.clone());
            }
        }
        map
    }

    /// The body + declaring scope of a free function, by FQN (for interprocedural
    /// return inference).
    pub fn function_body(&self, fqn: &str) -> Option<(&[Stmt], &Scope)> {
        depsrec::note_body(fqn);
        with_ci_key(fqn, |key| self.bodies.get(key)).map(|r| (r.body.as_slice(), &r.scope))
    }

    /// Full body metadata for a free function, including source path/kind when
    /// it was added through [`add_file_labeled_as`](Self::add_file_labeled_as).
    pub fn function_body_meta(&self, fqn: &str) -> Option<BodyMetadata<'_>> {
        depsrec::note_body(fqn);
        with_ci_key(fqn, |key| self.bodies.get(key)).map(|r| r.metadata())
    }

    /// The body + declaring scope of a method on `declaring_class` (use the
    /// `declaring_class` from [`find_method`](Self::find_method), not the receiver).
    pub fn method_body(&self, declaring_class: &str, name: &str) -> Option<(&[Stmt], &Scope)> {
        depsrec::note_body(declaring_class);
        with_method_key(declaring_class, name, |key| self.bodies.get(key))
            .map(|r| (r.body.as_slice(), &r.scope))
    }

    /// Full body metadata for a method on `declaring_class`.
    pub fn method_body_meta(&self, declaring_class: &str, name: &str) -> Option<BodyMetadata<'_>> {
        depsrec::note_body(declaring_class);
        self.bodies
            .get(&format!(
                "{}::{}",
                class_key(declaring_class),
                name.to_ascii_lowercase()
            ))
            .map(|r| r.metadata())
    }

    // --- Whole-project signature inference support ---------------------------
    //
    // These accessors and the apply step exist for `php_infer::signatures`, which
    // synthesizes signatures for fully untyped functions/methods from their bodies
    // and call sites, then folds them back into the stored reflections so all
    // downstream inference/rules benefit. They deliberately do **not** record
    // incremental dependencies (`depsrec`): the pre-pass runs before per-file
    // analysis, outside any recording session.

    /// Canonical FQNs of every free function in the index (built-ins included; the
    /// caller filters on [`FunctionReflection::builtin`]).
    pub fn function_fqns(&self) -> Vec<String> {
        self.functions.values().map(|f| f.fqn.clone()).collect()
    }

    /// Canonical FQNs of every class-like in the index (built-ins included).
    pub fn class_fqns(&self) -> Vec<String> {
        self.classes.values().map(|c| c.fqn.clone()).collect()
    }

    /// Whether a free-function body is stored under this FQN (i.e. it was reflected
    /// from project source, not a stub). Does not record a dependency.
    pub fn has_function_body(&self, fqn: &str) -> bool {
        with_ci_key(fqn, |key| self.bodies.contains_key(key))
    }

    /// Whether a method body is stored under `class_fqn::name` (the method is
    /// declared — with a body — on this class, not inherited or magic).
    pub fn has_method_body(&self, class_fqn: &str, name: &str) -> bool {
        with_method_key(class_fqn, name, |key| self.bodies.contains_key(key))
    }

    /// Fold synthesized signatures into the stored reflections in place. Only slots
    /// that were *not* explicitly declared are overwritten (and flagged
    /// `inferred`/`inferred_return`); `native_*` and `explicit*` are never touched,
    /// so inferred types behave exactly like PHPDoc types.
    pub fn apply_inferred(&mut self, inf: &InferredSignatures) {
        for (fqn, sig) in &inf.fns {
            if sig.is_empty() {
                continue;
            }
            if let Some(arc) = self.functions.get_mut(&function_key(fqn)) {
                let f = Arc::make_mut(arc);
                if f.builtin {
                    continue;
                }
                apply_params(&mut f.params, &sig.params);
                if let Some(ret) = &sig.ret {
                    if !f.explicit_return {
                        f.return_type = ret.clone();
                        f.inferred_return = true;
                    }
                }
            }
        }
        for ((class_fqn, method), sig) in &inf.methods {
            if sig.is_empty() {
                continue;
            }
            if let Some(arc) = self.classes.get_mut(&class_key(class_fqn)) {
                let c = Arc::make_mut(arc);
                if c.builtin {
                    continue;
                }
                if let Some(m) = c
                    .methods
                    .iter_mut()
                    .find(|m| m.name.eq_ignore_ascii_case(method))
                {
                    apply_params(&mut m.params, &sig.params);
                    if let Some(ret) = &sig.ret {
                        if !m.explicit_return {
                            m.return_type = ret.clone();
                            m.inferred_return = true;
                        }
                    }
                }
            }
        }
    }
}

/// Overwrite the inferred type of each non-explicit parameter position.
fn apply_params(params: &mut [crate::ParamReflection], inferred: &[Option<Type>]) {
    for (p, slot) in params.iter_mut().zip(inferred) {
        if let Some(ty) = slot {
            if !p.explicit {
                p.ty = ty.clone();
                p.inferred = true;
            }
        }
    }
}

/// The cached, re-mergeable reflection output of one parsed file: every
/// declared class/function reflection plus the callable bodies, in declaration
/// order, with the file's [`SourceKind`] baked in. Built by [`reflect_artifact`]
/// and merged via [`ReflectionIndex::add_artifact`]. Values are `Arc`-shared so
/// caching an artifact and re-merging it every incremental pass costs reference
/// bumps, not deep clones of statement bodies.
#[derive(Debug, Clone)]
pub struct FileReflectionArtifact {
    kind: SourceKind,
    /// A configured `stubFiles` entry. Stubs exist precisely to *override* a
    /// project declaration, so they are the one exception to the first-wins
    /// redeclaration rule in [`ReflectionIndex::add_artifact`].
    stub: bool,
    entries: Vec<ArtifactEntry>,
}

#[derive(Debug, Clone)]
enum ArtifactEntry {
    Class {
        key: String,
        reflection: Arc<ClassReflection>,
        /// Method bodies, keyed `class_key::method_lower`.
        bodies: Vec<(String, Arc<BodyRecord>)>,
    },
    Function {
        key: String,
        reflection: Arc<FunctionReflection>,
        body: Arc<BodyRecord>,
    },
}

impl FileReflectionArtifact {
    /// How the file participates in reflection (analyzed vs scan-only).
    pub fn kind(&self) -> SourceKind {
        self.kind
    }

    /// The normalized index keys of every symbol this file declares.
    pub fn declared_keys(&self) -> impl Iterator<Item = &str> {
        self.entries.iter().map(|e| match e {
            ArtifactEntry::Class { key, .. } | ArtifactEntry::Function { key, .. } => key.as_str(),
        })
    }

    /// `(key, reflection)` for each declared class, in declaration order.
    pub fn class_reflections(&self) -> impl Iterator<Item = (&str, &ClassReflection)> {
        self.entries.iter().filter_map(|e| match e {
            ArtifactEntry::Class {
                key, reflection, ..
            } => Some((key.as_str(), reflection.as_ref())),
            ArtifactEntry::Function { .. } => None,
        })
    }

    /// `(key, reflection)` for each declared function, in declaration order.
    pub fn function_reflections(&self) -> impl Iterator<Item = (&str, &FunctionReflection)> {
        self.entries.iter().filter_map(|e| match e {
            ArtifactEntry::Function {
                key, reflection, ..
            } => Some((key.as_str(), reflection.as_ref())),
            ArtifactEntry::Class { .. } => None,
        })
    }
}

/// Reflect one parsed file into a cacheable [`FileReflectionArtifact`]. This is
/// the reflection half of [`ReflectionIndex::add_file_labeled_as`], split out so
/// incremental analysis can cache the result per file and replay it with
/// [`ReflectionIndex::add_artifact`] on every pass.
pub fn reflect_artifact(
    path: Option<&str>,
    program: &Program,
    interner: &Interner,
    kind: SourceKind,
) -> FileReflectionArtifact {
    let mut entries = Vec::new();
    for_each_region(&program.stmts, interner, |scope, region| {
        for st in region {
            visit_reflectable_decls(scope, st, &mut |scope, decl| match decl {
                ReflectableDecl::Function(f) => {
                    let r = reflect_function(scope, interner, f);
                    let key = function_key(&r.fqn);
                    entries.push(ArtifactEntry::Function {
                        body: Arc::new(BodyRecord {
                            body: f.body.clone(),
                            scope: scope.clone(),
                            path: path.map(str::to_string),
                            source_kind: kind,
                        }),
                        key,
                        reflection: Arc::new(r),
                    });
                }
                ReflectableDecl::Class(c) => {
                    // Anonymous classes have no FQN.
                    let Some(name) = c.name else { return };
                    let fqn = scope.qualify(interner.resolve(name));
                    let key = class_key(&fqn);
                    let r = reflect_class(scope, interner, &fqn, c);
                    // Method bodies (+ the class's scope) for interprocedural inference.
                    let mut bodies = Vec::new();
                    for m in &c.members {
                        if let Member::Method(md) = m {
                            if let Some(body) = &md.body {
                                let mname = interner.resolve(md.name).to_ascii_lowercase();
                                bodies.push((
                                    format!("{key}::{mname}"),
                                    Arc::new(BodyRecord {
                                        body: body.clone(),
                                        scope: scope.clone(),
                                        path: path.map(str::to_string),
                                        source_kind: kind,
                                    }),
                                ));
                            }
                        }
                    }
                    entries.push(ArtifactEntry::Class {
                        key,
                        reflection: Arc::new(r),
                        bodies,
                    });
                }
            });
        }
    });
    FileReflectionArtifact {
        kind,
        stub: false,
        entries,
    }
}

/// [`reflect_artifact`] for a configured `stubFiles` entry: scan-only for
/// analysis purposes, but allowed to override an earlier project declaration.
pub fn reflect_stub_artifact(
    path: Option<&str>,
    program: &Program,
    interner: &Interner,
) -> FileReflectionArtifact {
    FileReflectionArtifact {
        stub: true,
        ..reflect_artifact(path, program, interner, SourceKind::Scan)
    }
}

/// Should an incoming declaration overwrite what is already indexed under its
/// key? `existing` is `Some(is_builtin)` when a declaration is already present.
///
/// * Scan-only sources never replace a curated builtin (a vendored polyfill must
///   not clobber the real signature).
/// * Otherwise the **first** declaration wins, matching
///   [`php_index::ProjectIndex`] and PHP itself (the first class to load wins;
///   the redeclaration is a fatal error). Keeping the two indexes on the same
///   winner is what stops name-level rules and member/type rules from
///   contradicting each other on a redeclared class.
/// * Configured stub files are the deliberate exception — overriding a project
///   declaration is their entire purpose.
/// * Analyzed source may still shadow a builtin (an unchanged long-standing
///   allowance for polyfills).
fn accepts_redeclaration(kind: SourceKind, stub: bool, existing: Option<bool>) -> bool {
    match existing {
        None => true,
        Some(true) => stub || kind != SourceKind::Scan,
        Some(false) => stub,
    }
}

fn class_key(fqn: &str) -> String {
    SymbolKey::class_like(fqn).into_string()
}

/// Replace `Named` nodes whose *short name* keys `map` with the alias body
/// (namespace-independent). Used for the alias-references-alias fixpoint, where
/// no real-class guard is needed (the map only holds alias names).
fn expand_global_alias(ty: &Type, map: &HashMap<String, Type>, exclude: &str) -> Type {
    ty.clone().map(&mut |part| match part {
        Type::Named { fqn, args } if args.is_empty() => {
            let full = fqn.trim_start_matches('\\').to_ascii_lowercase();
            let short = full.rsplit('\\').next().unwrap_or(&full);
            if short != exclude {
                if let Some(t) = map.get(short) {
                    return t.clone();
                }
            }
            Type::Named { fqn, args }
        }
        other => other,
    })
}

/// Like [`expand_global_alias`] but never rewrites a `Named` that resolves to a
/// real indexed class (`real` holds the class keys) — a real class of the same
/// short name wins, so a global alias colliding with a class is a silent no-op.
fn expand_global_alias_guarded(
    ty: &Type,
    map: &HashMap<String, Type>,
    real: &std::collections::HashSet<String>,
) -> Type {
    ty.clone().map(&mut |part| match part {
        Type::Named { fqn, args } if args.is_empty() => {
            let full = fqn.trim_start_matches('\\').to_ascii_lowercase();
            if !real.contains(&full) {
                let short = full.rsplit('\\').next().unwrap_or(&full);
                if let Some(t) = map.get(short) {
                    return t.clone();
                }
            }
            Type::Named { fqn, args }
        }
        other => other,
    })
}

fn function_key(fqn: &str) -> String {
    SymbolKey::function(fqn).into_string()
}

// Allocation-free lookup keys: read paths build the canonical (lowercased,
// `\`-stripped) key in a reused thread-local buffer instead of allocating a
// `String` per lookup — inference hammers these maps. Inserts keep the owned
// `class_key`/`function_key` builders above. The buffer is *taken* out of the
// cell for the closure's duration, so an (unexpected) re-entrant lookup falls
// back to a fresh allocation instead of panicking.
thread_local! {
    static KEY_BUF: std::cell::RefCell<String> = const { std::cell::RefCell::new(String::new()) };
}

/// Run `f` with the canonical class/function key for `fqn` (classes and
/// functions share the same case-insensitive canonicalization).
fn with_ci_key<R>(fqn: &str, f: impl FnOnce(&str) -> R) -> R {
    KEY_BUF.with(|cell| {
        let mut buf = cell.take();
        php_resolve::write_ci_key(fqn, &mut buf);
        let r = f(&buf);
        cell.replace(buf);
        r
    })
}

/// Run `f` with the canonical `class::method` body key.
fn with_method_key<R>(class: &str, name: &str, f: impl FnOnce(&str) -> R) -> R {
    KEY_BUF.with(|cell| {
        let mut buf = cell.take();
        php_resolve::write_ci_key(class, &mut buf);
        buf.push_str("::");
        buf.push_str(name);
        buf.make_ascii_lowercase();
        let r = f(&buf);
        cell.replace(buf);
        r
    })
}

/// Apply a template substitution to a method's parameter and return types.
fn subst_method<'a>(m: &'a MethodReflection, subst: &Subst) -> Cow<'a, MethodReflection> {
    if subst.is_empty() {
        return Cow::Borrowed(m);
    }
    let mut out = m.clone();
    for p in &mut out.params {
        p.ty = subst_type(&p.ty, subst);
        p.native_ty = subst_type(&p.native_ty, subst);
    }
    out.return_type = subst_type(&out.return_type, subst);
    out.native_return = subst_type(&out.native_return, subst);
    Cow::Owned(out)
}

/// Apply a template substitution to a property's type, borrowing when nothing
/// needs rewriting.
fn subst_property<'a>(p: &'a PropertyReflection, subst: &Subst) -> Cow<'a, PropertyReflection> {
    if subst.is_empty() {
        return Cow::Borrowed(p);
    }
    Cow::Owned(PropertyReflection {
        ty: subst_type(&p.ty, subst),
        ..p.clone()
    })
}

/// Apply a template substitution to a constant's type, borrowing when nothing
/// needs rewriting.
fn subst_constant<'a>(c: &'a ConstReflection, subst: &Subst) -> Cow<'a, ConstReflection> {
    if subst.is_empty() {
        return Cow::Borrowed(c);
    }
    Cow::Owned(ConstReflection {
        ty: subst_type(&c.ty, subst),
        ..c.clone()
    })
}

/// Recursively replace [`Type::TemplateVar`] occurrences using `subst`.
fn subst_type(ty: &Type, subst: &Subst) -> Type {
    if subst.is_empty() {
        return ty.clone();
    }
    ty.clone().map(&mut |part| match part {
        Type::TemplateVar(name) => subst
            .get(&*name)
            .cloned()
            .unwrap_or(Type::TemplateVar(name)),
        Type::Union(parts) => Type::union(parts.to_vec()),
        Type::Intersection(parts) => Type::intersection(parts.to_vec()),
        other => other,
    })
}

fn direct_iterable_named_key_value(fqn: &str, args: &[Type]) -> Option<(Type, Type)> {
    if !is_known_generic_iterable(fqn) {
        return None;
    }
    match args {
        [key, value, ..] => Some((key.clone(), value.clone())),
        [value] => Some((Type::Mixed, value.clone())),
        _ => None,
    }
}

fn is_known_generic_iterable(fqn: &str) -> bool {
    matches!(
        fqn.trim_start_matches('\\').to_ascii_lowercase().as_str(),
        "generator"
            | "iterator"
            | "seekableiterator"
            | "traversable"
            | "iteratoraggregate"
            | "arrayobject"
            | "splfixedarray"
            | "weakmap"
    )
}

fn shape_field_key_type(field: &php_types::ShapeField) -> Type {
    match &field.key {
        Some(key) if canonical_int_string(key.as_bytes()).is_some() => Type::Int,
        Some(_) => Type::String,
        None => Type::Int,
    }
}

fn canonical_int_string(bytes: &[u8]) -> Option<i64> {
    if bytes.is_empty() {
        return None;
    }
    let (neg, digits): (bool, &[u8]) = match bytes.first() {
        Some(b'-') => (true, &bytes[1..]),
        _ => (false, bytes),
    };
    if digits.is_empty() || !digits.iter().all(|b| b.is_ascii_digit()) {
        return None;
    }
    if digits.len() > 1 && digits[0] == b'0' {
        return None;
    }
    let s = std::str::from_utf8(bytes).ok()?;
    let n: i64 = s.parse().ok()?;
    if neg && n == 0 {
        return None;
    }
    Some(n)
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_resolve::SymbolKey;
    use std::collections::BTreeSet;

    fn index(src: &str) -> ReflectionIndex {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::new();
        idx.add_file(&r.program, &r.interner);
        idx
    }

    fn add(idx: &mut ReflectionIndex, src: &str, kind: SourceKind) {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors");
        idx.add_file_labeled_as(None, &r.program, &r.interner, kind);
    }

    fn add_stub(idx: &mut ReflectionIndex, src: &str) {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors");
        idx.add_artifact(&reflect_stub_artifact(None, &r.program, &r.interner));
    }

    /// Regression: `add_artifact` was unconditional last-wins while
    /// `ProjectIndex` is first-wins, so name-level rules and member/type rules
    /// could resolve a redeclared class through *different* parents in one run.
    #[test]
    fn redeclared_class_keeps_the_first_declaration() {
        let mut idx = ReflectionIndex::new();
        add(
            &mut idx,
            "<?php class B { public function fromB() {} }",
            SourceKind::Analyzed,
        );
        add(
            &mut idx,
            "<?php class C { public function fromC() {} }",
            SourceKind::Analyzed,
        );
        add(&mut idx, "<?php class A extends B {}", SourceKind::Analyzed);
        add(&mut idx, "<?php class A extends C {}", SourceKind::Analyzed);
        assert_eq!(idx.class("A").unwrap().parents, vec![named("B")]);
        assert!(idx.find_method("A", "fromB").is_some());
        assert!(idx.find_method("A", "fromC").is_none());
    }

    #[test]
    fn redeclared_function_keeps_the_first_declaration() {
        let mut idx = ReflectionIndex::new();
        add(
            &mut idx,
            "<?php function f(): int { return 1; }",
            SourceKind::Analyzed,
        );
        add(
            &mut idx,
            "<?php function f(): string { return 'x'; }",
            SourceKind::Analyzed,
        );
        assert_eq!(idx.function("f").unwrap().return_type, Type::Int);
    }

    /// Stub files exist to override project declarations — the one exception.
    #[test]
    fn stub_file_overrides_an_earlier_declaration() {
        let mut idx = ReflectionIndex::new();
        add(
            &mut idx,
            "<?php function f(): int { return 1; }",
            SourceKind::Analyzed,
        );
        add_stub(&mut idx, "<?php function f(): string {}");
        assert_eq!(idx.function("f").unwrap().return_type, Type::String);

        let mut idx = ReflectionIndex::new();
        add(
            &mut idx,
            "<?php class A { public function a(): int {} }",
            SourceKind::Analyzed,
        );
        add_stub(&mut idx, "<?php class A { public function a(): string {} }");
        assert_eq!(
            idx.find_method("A", "a").unwrap().member.return_type,
            Type::String
        );
    }

    #[test]
    fn scan_source_still_never_replaces_a_builtin() {
        let mut idx = ReflectionIndex::with_builtins();
        let before = idx.function("strlen").unwrap().return_type.clone();
        add(
            &mut idx,
            "<?php function strlen($s): array { return []; }",
            SourceKind::Scan,
        );
        assert_eq!(idx.function("strlen").unwrap().return_type, before);
    }

    fn named(fqn: &str) -> Type {
        Type::Named {
            fqn: fqn.into(),
            args: vec![],
        }
    }

    fn generic(fqn: &str, args: Vec<Type>) -> Type {
        Type::Named {
            fqn: fqn.into(),
            args,
        }
    }

    #[test]
    fn global_type_alias_expands_in_member_and_function_types() {
        let mut idx = index(
            r#"<?php
            namespace App;
            class Repo {
                /** @return UserId */
                public function id() {}
            }
            /** @param UserId $x */
            function take($x): void {}"#,
        );
        let mut defs = std::collections::HashMap::new();
        defs.insert("UserId".to_string(), "int".to_string());
        idx.apply_global_type_aliases(&defs);
        let m = idx.class("App\\Repo").unwrap().methods[0]
            .return_type
            .clone();
        assert_eq!(m, Type::Int);
        let p = idx.function("App\\take").unwrap().params[0].ty.clone();
        assert_eq!(p, Type::Int);
    }

    #[test]
    fn global_type_alias_does_not_shadow_a_real_class() {
        // A real class named `UserId` must win over a same-named global alias.
        let mut idx = index(
            r#"<?php
            namespace App;
            class UserId {}
            class Repo {
                /** @return UserId */
                public function id() {}
            }"#,
        );
        let mut defs = std::collections::HashMap::new();
        defs.insert("UserId".to_string(), "int".to_string());
        idx.apply_global_type_aliases(&defs);
        let m = idx.class("App\\Repo").unwrap().methods[0]
            .return_type
            .clone();
        assert_eq!(m, named("App\\UserId"));
    }

    #[test]
    fn indexes_classes_and_functions_case_insensitively() {
        let idx = index(
            r#"<?php
            namespace App;
            class User {}
            function helper(): void {}"#,
        );
        assert!(idx.class("App\\User").is_some());
        assert!(idx.class("app\\user").is_some()); // case-insensitive
        assert!(idx.class("\\App\\User").is_some()); // leading backslash ignored
        assert!(idx.function("App\\helper").is_some());
        assert_eq!(idx.class_count(), 1);
    }

    #[test]
    fn body_metadata_preserves_source_path_kind_and_scope() {
        let r = php_parser::parse(
            r#"<?php
            namespace App;
            function cb($x): void { helper($x); }
            class Handler { public function map($x): void { helper($x); } }
            "#,
        );
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::new();
        idx.add_file_labeled_as(
            Some("src/Callbacks.php"),
            &r.program,
            &r.interner,
            SourceKind::Analyzed,
        );

        let old_fn = idx.function_body("App\\cb").unwrap();
        assert_eq!(old_fn.1.namespace(), Some("App"));
        let fn_meta = idx.function_body_meta("App\\cb").unwrap();
        assert_eq!(fn_meta.path, Some("src/Callbacks.php"));
        assert_eq!(fn_meta.source_kind, SourceKind::Analyzed);
        assert_eq!(fn_meta.scope.namespace(), Some("App"));
        assert!(!fn_meta.body.is_empty());

        let old_method = idx.method_body("App\\Handler", "map").unwrap();
        assert_eq!(old_method.1.namespace(), Some("App"));
        let method_meta = idx.method_body_meta("App\\Handler", "map").unwrap();
        assert_eq!(method_meta.path, Some("src/Callbacks.php"));
        assert_eq!(method_meta.source_kind, SourceKind::Analyzed);
        assert_eq!(method_meta.scope.namespace(), Some("App"));
        assert!(!method_meta.body.is_empty());
    }

    #[test]
    fn unlabeled_body_metadata_keeps_old_body_api_but_has_no_path() {
        let r = php_parser::parse("<?php function cb(): void {}");
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::new();
        idx.add_file(&r.program, &r.interner);

        assert!(idx.function_body("cb").is_some());
        let meta = idx.function_body_meta("cb").unwrap();
        assert_eq!(meta.path, None);
        assert_eq!(meta.source_kind, SourceKind::Analyzed);
    }

    #[test]
    fn finds_inherited_method_from_parent() {
        let idx = index(
            r#"<?php
            class Base { public function id(): int { return 1; } }
            class User extends Base {}"#,
        );
        let f = idx.find_method("User", "id").unwrap();
        assert_eq!(f.declaring_class, "Base");
        assert_eq!(f.member.return_type, Type::Int);
        // Own method shadows the inherited one.
        let idx2 = index(
            r#"<?php
            class Base { public function id(): int {} }
            class User extends Base { public function id(): string {} }"#,
        );
        let f2 = idx2.find_method("User", "id").unwrap();
        assert_eq!(f2.declaring_class, "User");
        assert_eq!(f2.member.return_type, Type::String);
    }

    #[test]
    fn method_lookup_is_case_insensitive() {
        let idx = index(r#"<?php class C { public function doThing(): void {} }"#);
        assert!(idx.find_method("C", "DOTHING").is_some());
        assert!(idx.find_method("C", "dothing").is_some());
    }

    #[test]
    fn finds_method_through_trait_and_interface_const() {
        let idx = index(
            r#"<?php
            trait T { public function shared(): bool {} }
            interface I { const MAX = 10; }
            class C extends \stdClass implements I { use T; }"#,
        );
        assert_eq!(idx.find_method("C", "shared").unwrap().declaring_class, "T");
        assert_eq!(idx.find_constant("C", "MAX").unwrap().declaring_class, "I");
    }

    #[test]
    fn inherited_property_is_found() {
        let idx = index(
            r#"<?php
            class Base { protected string $name; }
            class User extends Base {}"#,
        );
        let p = idx.find_property("User", "name").unwrap();
        assert_eq!(p.declaring_class, "Base");
        assert_eq!(p.member.ty, Type::String);
        assert!(idx.find_property("User", "missing").is_none());
    }

    #[test]
    fn generic_args_substitute_into_inherited_members() {
        // Collection<T> with `add(T): void` and `first(): T`; a concrete
        // subclass binds T = User and inherited members specialise.
        let idx = index(
            r#"<?php
            /** @template T */
            class Collection {
                /** @param T $item */
                public function add($item): void {}
                /** @return T */
                public function first() {}
            }
            /** @extends Collection<User> */
            class Users extends Collection {}
            class User {}"#,
        );
        let add = idx.find_method("Users", "add").unwrap();
        assert_eq!(add.declaring_class, "Collection");
        assert_eq!(
            add.member.params[0].ty,
            Type::Named {
                fqn: "User".into(),
                args: vec![]
            }
        );
        let first = idx.find_method("Users", "first").unwrap();
        assert_eq!(
            first.member.return_type,
            Type::Named {
                fqn: "User".into(),
                args: vec![]
            }
        );
    }

    #[test]
    fn receiver_generic_args_substitute_own_method() {
        let idx = index(
            r#"<?php
            /** @template T */
            class Collection {
                /** @return T */
                public function first() {}
            }
            class User {}"#,
        );
        let receiver = generic("Collection", vec![named("User")]);
        let found = idx.find_method_on_type(&receiver, "first").unwrap();
        assert_eq!(found.declaring_class, "Collection");
        assert_eq!(found.member.return_type, named("User"));
    }

    #[test]
    fn receiver_generic_args_substitute_own_property() {
        let idx = index(
            r#"<?php
            /** @template T */
            class Box {
                /** @var T */
                public $value;
            }
            class User {}"#,
        );
        let receiver = generic("Box", vec![named("User")]);
        let found = idx.find_property_on_type(&receiver, "value").unwrap();
        assert_eq!(found.declaring_class, "Box");
        assert_eq!(found.member.ty, named("User"));
    }

    #[test]
    fn receiver_generic_builtin_arrayobject_offset_get() {
        let idx = ReflectionIndex::with_builtins();
        let receiver = generic("ArrayObject", vec![Type::Int, named("User")]);
        let found = idx.find_method_on_type(&receiver, "offsetGet").unwrap();
        assert_eq!(found.member.return_type.to_string(), "User|null");
    }

    #[test]
    fn iterable_key_value_extracts_generator_family_args() {
        let idx = ReflectionIndex::new();
        let ty = generic(
            "Generator",
            vec![Type::Int, named("User"), Type::Void, named("Result")],
        );
        let (k, v) = idx.iterable_key_value_on_type(&ty).unwrap();
        assert_eq!(k.to_string(), "int");
        assert_eq!(v.to_string(), "User");
    }

    #[test]
    fn iterable_key_value_extracts_builtin_iterable_classes() {
        let idx = ReflectionIndex::new();
        let array_object = generic("ArrayObject", vec![Type::Int, named("User")]);
        let weak_map = generic("WeakMap", vec![Type::Object, named("User")]);

        let (k, v) = idx.iterable_key_value_on_type(&array_object).unwrap();
        assert_eq!(
            (k.to_string(), v.to_string()),
            ("int".to_string(), "User".to_string())
        );

        let (k, v) = idx.iterable_key_value_on_type(&weak_map).unwrap();
        assert_eq!(
            (k.to_string(), v.to_string()),
            ("object".to_string(), "User".to_string())
        );
    }

    #[test]
    fn iterable_key_value_composes_through_userland_implements() {
        let idx = index(
            r#"<?php
            class User {}
            /** @implements \IteratorAggregate<string, User> */
            class Users implements \IteratorAggregate {}
            "#,
        );
        let (k, v) = idx
            .iterable_key_value_on_type(&named("Users"))
            .expect("iterable key/value");
        assert_eq!(
            (k.to_string(), v.to_string()),
            ("string".to_string(), "User".to_string())
        );
    }

    #[test]
    fn iterable_key_value_unions_only_when_all_arms_are_extractable() {
        let idx = ReflectionIndex::new();
        let ok = Type::union(vec![
            Type::List(Box::new(named("User"))),
            generic("Generator", vec![Type::String, named("Admin")]),
        ]);
        let (k, v) = idx.iterable_key_value_on_type(&ok).unwrap();
        assert_eq!(k.to_string(), "int|string");
        assert_eq!(v.to_string(), "User|Admin");

        let mixed = Type::union(vec![Type::List(Box::new(named("User"))), Type::Mixed]);
        assert!(idx.iterable_key_value_on_type(&mixed).is_none());
        assert!(idx.iterable_key_value_on_type(&Type::Mixed).is_none());
    }

    #[test]
    fn receiver_substitution_composes_through_inherited_parent() {
        let idx = index(
            r#"<?php
            /** @template T */
            class ParentBox {
                /** @return T */
                public function get() {}
            }
            /**
             * @template U
             * @extends ParentBox<U>
             */
            class ChildBox extends ParentBox {}
            class User {}"#,
        );
        let receiver = generic("ChildBox", vec![named("User")]);
        let found = idx.find_method_on_type(&receiver, "get").unwrap();
        assert_eq!(found.declaring_class, "ParentBox");
        assert_eq!(found.member.return_type, named("User"));
    }

    #[test]
    fn substitution_composes_through_two_levels() {
        // Map<K,V> -> StringMap<V> binds K=string -> IntStringMap binds V=int.
        let idx = index(
            r#"<?php
            /**
             * @template K
             * @template V
             */
            class Map {
                /** @return array<K, V> */
                public function all(): array {}
            }
            /**
             * @template V
             * @extends Map<string, V>
             */
            class StringMap extends Map {}
            /** @extends StringMap<int> */
            class IntStringMap extends StringMap {}"#,
        );
        let all = idx.find_method("IntStringMap", "all").unwrap();
        assert_eq!(all.member.return_type.to_string(), "array<string, int>");
    }

    #[test]
    fn cycle_in_hierarchy_does_not_loop() {
        // A pathological mutual-extends pair must terminate.
        let idx = index(
            r#"<?php
            class A extends B {}
            class B extends A {}"#,
        );
        assert!(idx.find_method("A", "whatever").is_none());
    }

    #[test]
    fn enum_magic_members_are_reflected() {
        let idx = index(
            r#"<?php
            enum Suit: string { case Hearts = 'H'; }"#,
        );
        assert_eq!(
            idx.find_property("Suit", "name").unwrap().member.ty,
            Type::String
        );
        assert_eq!(
            idx.find_property("Suit", "value").unwrap().member.ty,
            Type::String
        );
        assert_eq!(
            idx.find_method("Suit", "cases")
                .unwrap()
                .member
                .return_type
                .to_string(),
            "list<static>"
        );
        assert_eq!(
            idx.find_method("Suit", "tryFrom")
                .unwrap()
                .member
                .return_type
                .to_string(),
            "?static"
        );
    }

    #[test]
    fn builtin_class_members_are_loaded() {
        let idx = ReflectionIndex::with_builtins();
        assert_eq!(
            idx.find_method("DateTimeImmutable", "format")
                .unwrap()
                .member
                .return_type,
            Type::String
        );
        assert_eq!(
            idx.find_method("DateTimeZone", "getName")
                .unwrap()
                .member
                .return_type,
            Type::String
        );
    }

    #[test]
    fn phpstan_import_type_resolves_cross_class() {
        let r = php_parser::parse(
            r#"<?php
            /** @phpstan-type UserData = array{id: int, name: string} */
            class Shapes {}
            /** @phpstan-import-type UserData from Shapes */
            class Service {
                /** @param UserData $data */
                public function save($data): void {}
            }
            "#,
        );
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::new();
        idx.add_file(&r.program, &r.interner);
        // Before resolution, the imported alias is an unresolved Named phantom.
        let before = idx.find_method("Service", "save").unwrap();
        assert_ne!(
            before.member.params[0].ty.to_string(),
            "array{id: int, name: string}"
        );
        idx.resolve_type_imports();
        let after = idx.find_method("Service", "save").unwrap();
        assert_eq!(
            after.member.params[0].ty.to_string(),
            "array{id: int, name: string}"
        );
    }

    #[test]
    fn phpstan_import_type_with_alias_rename() {
        let r = php_parser::parse(
            r#"<?php
            /** @phpstan-type Row = array{n: int} */
            class Repo {}
            /** @phpstan-import-type Row from Repo as Record */
            class Uses {
                /** @return Record */
                public function one() { return []; }
            }
            "#,
        );
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::new();
        idx.add_file(&r.program, &r.interner);
        idx.resolve_type_imports();
        let one = idx.find_method("Uses", "one").unwrap();
        assert_eq!(one.member.return_type.to_string(), "array{n: int}");
    }

    #[test]
    fn builtin_generic_class_templates_substitute_through_extends() {
        let r = php_parser::parse(
            r#"<?php
            class User {}
            /** @extends \ArrayObject<int, User> */
            class Users extends \ArrayObject {}
            "#,
        );
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::with_builtins();
        idx.add_file(&r.program, &r.interner);

        assert_eq!(
            idx.class("ArrayObject").unwrap().templates,
            ["TKey", "TValue"]
        );
        assert_eq!(
            idx.class("Users").unwrap().parents[0].to_string(),
            "ArrayObject<int, User>"
        );
        let offset_get = idx.find_method("Users", "offsetGet").unwrap();
        assert_eq!(offset_get.member.return_type.to_string(), "User|null");
    }

    #[test]
    fn builtin_signatures_follow_selected_php_version() {
        let idx84 = ReflectionIndex::with_builtins_for(PhpVersion::from_id(80400).unwrap());
        assert_eq!(
            idx84.function("array_multisort").unwrap().return_type,
            Type::Bool
        );

        let idx85 = ReflectionIndex::with_builtins_for(PhpVersion::from_id(80500).unwrap());
        assert_eq!(
            idx85.function("array_multisort").unwrap().return_type,
            Type::True
        );

        let idx86 = ReflectionIndex::with_builtins_for(PhpVersion::from_id(80600).unwrap());
        assert_eq!(
            idx86.function("array_multisort").unwrap().return_type,
            Type::True
        );

        let below = ReflectionIndex::with_builtins_for(PhpVersion::from_id(70400).unwrap());
        assert_eq!(
            below.function("array_multisort").unwrap().return_type,
            Type::Bool
        );

        let above = ReflectionIndex::with_builtins_for(PhpVersion::from_id(90000).unwrap());
        assert_eq!(
            above.function("array_multisort").unwrap().return_type,
            Type::True
        );
    }

    #[test]
    fn builtin_names_match_typed_manifests_for_supported_versions() {
        for id in [80400, 80500, 80600] {
            let version = PhpVersion::from_id(id).unwrap();
            let project = php_index::ProjectIndex::with_builtins_for(version);
            let reflection = ReflectionIndex::with_builtins_for(version);

            let project_functions: BTreeSet<_> = project
                .functions()
                .map(|f| SymbolKey::function(&f.fqn).into_string())
                .collect();
            let reflection_functions: BTreeSet<_> = reflection.functions.keys().cloned().collect();
            assert_eq!(
                project_functions, reflection_functions,
                "builtin function manifest drift for PHP {id}"
            );

            let project_classes: BTreeSet<_> = project
                .classes()
                .map(|c| SymbolKey::class_like(&c.fqn).into_string())
                .collect();
            let reflection_classes: BTreeSet<_> = reflection.classes.keys().cloned().collect();
            assert_eq!(
                project_classes, reflection_classes,
                "builtin class manifest drift for PHP {id}"
            );

            let project_constants: BTreeSet<_> = project
                .constants()
                .map(|c| SymbolKey::constant(&c.fqn).into_string())
                .collect();
            let manifest_constants: BTreeSet<_> = php_types::builtins::constants_for(version)
                .into_iter()
                .map(|c| SymbolKey::constant(c.fqn).into_string())
                .collect();
            assert_eq!(
                project_constants, manifest_constants,
                "builtin constant manifest drift for PHP {id}"
            );
        }
    }

    #[test]
    fn reflected_file_discovers_same_nested_declarations_as_project_index() {
        let r = php_parser::parse(
            r#"<?php
            if (true) {
                function conditional_fn(): int {}
                class ConditionalClass {}
            }
            class Host {
                public function boot(): void {
                    function method_fn(): string {}
                    class MethodClass {}
                }
            }"#,
        );
        assert!(!r.has_errors(), "parse errors");

        let file_index = php_resolve::index_file(&r.program, &r.interner);
        let mut project = php_index::ProjectIndex::new();
        project.add_file("fixture.php", &file_index);

        let mut reflection = ReflectionIndex::new();
        reflection.add_file(&r.program, &r.interner);

        for name in ["conditional_fn", "method_fn"] {
            assert_eq!(
                project.has_function(name),
                reflection.function(name).is_some(),
                "function discovery diverged for {name}"
            );
        }
        for name in ["ConditionalClass", "Host", "MethodClass"] {
            assert_eq!(
                project.has_class(name),
                reflection.class(name).is_some(),
                "class discovery diverged for {name}"
            );
        }

        let reflected = reflect_file(&r.program, &r.interner);
        assert!(reflected
            .functions
            .iter()
            .any(|f| f.reflection.fqn == "method_fn"));
        assert!(reflected
            .classes
            .iter()
            .any(|c| c.reflection.fqn == "MethodClass"));
    }

    #[test]
    fn scan_file_does_not_override_builtin_function() {
        let r = php_parser::parse("<?php function strlen(): bool {}");
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::with_builtins();
        idx.add_file_as(&r.program, &r.interner, SourceKind::Scan);
        assert_eq!(
            idx.function("strlen").unwrap().return_type,
            Type::int_range(Some(0), None)
        );
    }
}
