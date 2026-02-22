//! M-R1: build a per-file **symbol table** by walking a parsed program.
//!
//! Splits the file into namespace regions (a braced `namespace X { … }` body, a
//! non-braced `namespace X;` run, or the global region), builds each region's
//! [`Scope`] from its `use`/group-`use` imports, then collects every declared
//! class/function/constant — descending into nested statements so conditionally
//! declared symbols are found too. Class hierarchies (`extends`/`implements`/
//! used traits) are resolved to fully-qualified names. This is the reflection
//! foundation the type system will build on.

use crate::Scope;
use php_ast::*;
use php_intern::{Interner, Symbol};

/// Every symbol a single file declares, with names resolved to FQNs.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct FileIndex {
    pub classes: Vec<ClassSymbol>,
    pub functions: Vec<FunctionSymbol>,
    pub constants: Vec<ConstSymbol>,
}

/// A declared class/interface/trait/enum.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassSymbol {
    pub fqn: String,
    pub kind: ClassKind,
    /// Resolved parent(s): one for a class, possibly many for an interface.
    pub extends: Vec<String>,
    /// Resolved implemented interfaces.
    pub implements: Vec<String>,
    /// Resolved traits pulled in via `use Trait;`.
    pub uses_traits: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionSymbol {
    pub fqn: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstSymbol {
    pub fqn: String,
}

/// Build the symbol table for one parsed file.
pub fn index_file(program: &Program, interner: &Interner) -> FileIndex {
    let mut indexer = Indexer { i: interner, out: FileIndex::default() };
    indexer.walk_top(&program.stmts);
    indexer.out
}

struct Indexer<'a> {
    i: &'a Interner,
    out: FileIndex,
}

impl Indexer<'_> {
    /// Partition top-level statements into namespace regions and index each.
    fn walk_top(&mut self, stmts: &[Stmt]) {
        let mut idx = 0;
        while idx < stmts.len() {
            let (name, region, next) = match &stmts[idx].kind {
                // Braced `namespace X { … }`: the body is a self-contained region.
                StmtKind::Namespace { name, body: Some(body) } => (name.clone(), &body[..], idx + 1),
                // Non-braced `namespace X;`: runs until the next namespace.
                StmtKind::Namespace { name, body: None } => {
                    let end = region_end(stmts, idx + 1);
                    (name.clone(), &stmts[idx + 1..end], end)
                }
                // Code before any namespace declaration: a global region.
                _ => {
                    let end = region_end(stmts, idx);
                    (None, &stmts[idx..end], end)
                }
            };
            let scope = self.build_scope(name.as_ref(), region);
            for st in region {
                self.collect_stmt(&scope, st);
            }
            idx = next;
        }
    }

    /// Build a region's scope: its namespace plus all `use`/group-`use` imports
    /// declared directly in the region (imports apply to the whole block).
    fn build_scope(&self, name: Option<&Name>, stmts: &[Stmt]) -> Scope {
        let mut scope = match name {
            Some(n) => Scope::in_namespace(n.text.trim_start_matches('\\')),
            None => Scope::global(),
        };
        for st in stmts {
            match &st.kind {
                StmtKind::Use(items) => {
                    for it in items {
                        self.add_import(&mut scope, it.kind, &it.name.text, it.alias);
                    }
                }
                StmtKind::GroupUse { prefix, items, .. } => {
                    let prefix = prefix.text.trim_start_matches('\\');
                    for it in items {
                        let fqn = format!("{prefix}\\{}", it.name.text);
                        self.add_import(&mut scope, it.kind, &fqn, it.alias);
                    }
                }
                _ => {}
            }
        }
        scope
    }

    fn add_import(&self, scope: &mut Scope, kind: UseKind, target: &str, alias: Option<Symbol>) {
        let target = target.trim_start_matches('\\');
        let alias = match alias {
            Some(s) => self.i.resolve(s),
            None => target.rsplit('\\').next().unwrap_or(target),
        };
        match kind {
            UseKind::Class => scope.add_class_use(alias, target),
            UseKind::Function => scope.add_function_use(alias, target),
            UseKind::Const => scope.add_const_use(alias, target),
        }
    }

    /// Collect declarations in a statement, descending into nested bodies so
    /// conditionally declared classes/functions are indexed too.
    fn collect_stmt(&mut self, scope: &Scope, st: &Stmt) {
        match &st.kind {
            StmtKind::Function(f) => {
                self.out.functions.push(FunctionSymbol { fqn: scope.qualify(self.i.resolve(f.name)) });
            }
            StmtKind::Class(c) => self.collect_class(scope, c),
            StmtKind::ConstDecl { consts, .. } => {
                for c in consts {
                    self.out.constants.push(ConstSymbol { fqn: scope.qualify(self.i.resolve(c.name)) });
                }
            }
            // Conditional / nested declarations.
            StmtKind::Block(b) => self.collect_all(scope, b),
            StmtKind::If { then, elseifs, els, .. } => {
                self.collect_stmt(scope, then);
                for e in elseifs {
                    self.collect_stmt(scope, &e.body);
                }
                if let Some(e) = els {
                    self.collect_stmt(scope, e);
                }
            }
            StmtKind::While { body, .. }
            | StmtKind::DoWhile { body, .. }
            | StmtKind::For { body, .. }
            | StmtKind::Foreach { body, .. } => self.collect_stmt(scope, body),
            StmtKind::Try { body, catches, finally } => {
                self.collect_all(scope, body);
                for c in catches {
                    self.collect_all(scope, &c.body);
                }
                if let Some(f) = finally {
                    self.collect_all(scope, f);
                }
            }
            StmtKind::Switch { cases, .. } => {
                for case in cases {
                    self.collect_all(scope, &case.body);
                }
            }
            StmtKind::Declare { body: Some(b), .. } => self.collect_stmt(scope, b),
            _ => {}
        }
    }

    fn collect_all(&mut self, scope: &Scope, stmts: &[Stmt]) {
        for st in stmts {
            self.collect_stmt(scope, st);
        }
    }

    fn collect_class(&mut self, scope: &Scope, c: &ClassDecl) {
        // Anonymous classes have no name and aren't file-level symbols.
        let Some(name) = c.name else { return };
        let extends = c.extends.iter().filter_map(|n| resolved_fqn(scope, n)).collect();
        let implements = c.implements.iter().filter_map(|n| resolved_fqn(scope, n)).collect();
        let mut uses_traits = Vec::new();
        for m in &c.members {
            if let Member::TraitUse(tu) = m {
                uses_traits.extend(tu.traits.iter().filter_map(|n| resolved_fqn(scope, n)));
            }
        }
        self.out.classes.push(ClassSymbol {
            fqn: scope.qualify(self.i.resolve(name)),
            kind: c.kind,
            extends,
            implements,
            uses_traits,
        });
    }
}

/// Resolve a class-like name to its FQN, dropping `self`/`parent`/`static` and
/// built-in types (which never appear as real parents/interfaces).
fn resolved_fqn(scope: &Scope, name: &Name) -> Option<String> {
    scope.resolve_class(name).fqn().map(str::to_string)
}

/// The index one past the last statement of a region starting at `start`: the
/// next `namespace` declaration, or the end of the list.
fn region_end(stmts: &[Stmt], start: usize) -> usize {
    stmts[start..]
        .iter()
        .position(|s| matches!(s.kind, StmtKind::Namespace { .. }))
        .map(|p| start + p)
        .unwrap_or(stmts.len())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn index(src: &str) -> FileIndex {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors in test source");
        index_file(&r.program, &r.interner)
    }

    #[test]
    fn classes_functions_consts_in_a_namespace() {
        let idx = index(
            r#"<?php
            namespace App\Models;
            const VERSION = 1;
            function helper() {}
            class User {}
            interface HasId {}
            "#,
        );
        assert_eq!(idx.classes.iter().map(|c| c.fqn.as_str()).collect::<Vec<_>>(), ["App\\Models\\User", "App\\Models\\HasId"]);
        assert_eq!(idx.functions[0].fqn, "App\\Models\\helper");
        assert_eq!(idx.constants[0].fqn, "App\\Models\\VERSION");
    }

    #[test]
    fn extends_and_implements_resolve_through_imports() {
        let idx = index(
            r#"<?php
            namespace App\Models;
            use App\Support\Base;
            use App\Contracts\Arrayable;
            class User extends Base implements Arrayable, \Countable {}
            "#,
        );
        let user = &idx.classes[0];
        assert_eq!(user.fqn, "App\\Models\\User");
        assert_eq!(user.extends, ["App\\Support\\Base"]);
        assert_eq!(user.implements, ["App\\Contracts\\Arrayable", "Countable"]);
    }

    #[test]
    fn unqualified_parent_uses_current_namespace() {
        let idx = index(
            r#"<?php
            namespace App;
            class Base {}
            class User extends Base {}
            "#,
        );
        assert_eq!(idx.classes[1].extends, ["App\\Base"]);
    }

    #[test]
    fn trait_uses_are_resolved() {
        let idx = index(
            r#"<?php
            namespace App;
            use App\Concerns\HasTimestamps;
            class Model { use HasTimestamps, \Other\Loggable; }
            "#,
        );
        assert_eq!(idx.classes[0].uses_traits, ["App\\Concerns\\HasTimestamps", "Other\\Loggable"]);
    }

    #[test]
    fn group_use_imports_resolve() {
        let idx = index(
            r#"<?php
            namespace App;
            use App\Support\{Str, Arr as Collection};
            class A extends Str {}
            class B extends Collection {}
            "#,
        );
        assert_eq!(idx.classes[0].extends, ["App\\Support\\Str"]);
        assert_eq!(idx.classes[1].extends, ["App\\Support\\Arr"]);
    }

    #[test]
    fn braced_namespaces_have_independent_scopes() {
        let idx = index(
            r#"<?php
            namespace A { class Foo {} }
            namespace B { class Bar extends \A\Foo {} }
            "#,
        );
        assert_eq!(idx.classes[0].fqn, "A\\Foo");
        assert_eq!(idx.classes[1].fqn, "B\\Bar");
        assert_eq!(idx.classes[1].extends, ["A\\Foo"]);
    }

    #[test]
    fn global_namespace_and_no_namespace() {
        let idx = index(r#"<?php class Widget {} function go() {} const K = 1;"#);
        assert_eq!(idx.classes[0].fqn, "Widget");
        assert_eq!(idx.functions[0].fqn, "go");
        assert_eq!(idx.constants[0].fqn, "K");
    }

    #[test]
    fn nested_conditional_declaration_is_found() {
        let idx = index(
            r#"<?php
            namespace App;
            if (true) { class Conditional {} }
            "#,
        );
        assert_eq!(idx.classes[0].fqn, "App\\Conditional");
    }

    #[test]
    fn anonymous_classes_are_not_indexed() {
        let idx = index(r#"<?php namespace App; $x = new class {};"#);
        assert!(idx.classes.is_empty());
    }
}
