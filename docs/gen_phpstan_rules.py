import os, re, collections
SRC = "/Users/ben/Projects/php-ast/phpstan-src"
RULES_DIR = os.path.join(SRC, "src")

attr_re = re.compile(r'#\[RegisteredRule\(level:\s*(\d+)\)\]')
class_re = re.compile(r'(?:final |abstract )?class (\w+)')
ident_re = re.compile(r"->identifier\(\s*'([^']+)'")

# level -> category -> list of (class, src_path, [identifiers])
data = collections.defaultdict(lambda: collections.defaultdict(list))
total = 0
for root, _, files in os.walk(RULES_DIR):
    for fn in files:
        if not fn.endswith(".php"):
            continue
        path = os.path.join(root, fn)
        with open(path, encoding="utf-8", errors="replace") as f:
            text = f.read()
        m = attr_re.search(text)
        if not m:
            continue
        level = int(m.group(1))
        after = text[m.end():]
        cm = class_re.search(after)
        cls = cm.group(1) if cm else fn[:-4]
        rel = os.path.relpath(path, RULES_DIR)
        parts = rel.split(os.sep)
        # category = dir under src/Rules, else the top dir
        if parts[0] == "Rules" and len(parts) >= 3:
            cat = parts[1]
        elif parts[0] == "Rules":
            cat = "(misc)"
        else:
            cat = parts[0]
        idents = sorted(set(ident_re.findall(text)))
        src_path = "phpstan-src/" + os.path.relpath(path, SRC).replace(os.sep, "/")
        data[level][cat].append((cls, src_path, idents))
        total += 1

# feature-toggle-gated rules from conf level files
toggle = collections.defaultdict(list)  # level -> [class]
confdir = os.path.join(SRC, "conf")
for n in range(0, 11):
    p = os.path.join(confdir, f"config.level{n}.neon")
    if not os.path.exists(p): continue
    txt = open(p).read()
    for c in re.findall(r'class:\s*PHPStan\\Rules\\([A-Za-z\\]+)', txt):
        short = c.split("\\")[-1]
        toggle[n].append(short)

level_theme = {
0:"Basic existence + obvious mistakes (unknown classes/functions/methods on $this, wrong #args, always-undefined vars)",
1:"Possibly-undefined variables; magic methods/properties via __call/__get",
2:"Unknown methods on all expressions; PHPDoc validation",
3:"Return types; property type assignments",
4:"Basic dead code (always-false instanceof, dead else, unreachable, too-wide throws)",
5:"Argument types passed to functions/methods; by-ref args",
6:"Missing typehints (params/returns/properties/@var)",
7:"Partial union types (members not supporting a call); reportMaybes",
8:"Calling methods / accessing properties on nullable types",
9:"Strict mixed (explicit mixed only assignable to mixed)",
10:"Implicit mixed reported too (PHPStan 2.0)",
}
# Implemented phpstan rule classes (tick the checklist box on regeneration).
DONE = {
    # Cast
    "UnsetCastRule", "VoidCastRule",
    # Keywords
    "ContinueBreakInLoopRule", "DeclareStrictTypesRule", "GotoUndefinedLabelRule", "UnusedLabelRule",
    # Arrays
    "DuplicateKeysInLiteralArraysRule", "OffsetAccessWithoutDimForReadingRule",
    # Operators
    "InvalidAssignVarRule", "InvalidIncDecOperationRule", "BacktickRule",
    # Functions
    "RedefinedParametersRule", "InvalidParameterNameRule", "VariadicParametersDeclarationRule",
    "InnerFunctionRule", "InvalidLexicalVariablesInClosureUseRule", "UnusedClosureUsesRule",
    "CallToNonExistentFunctionRule", "PrintfParametersRule", "DefineParametersRule", "FunctionCallableRule",
    # Classes
    "InstantiationRule", "InstantiationCallableRule", "NewStaticRule", "ExistingClassInClassExtendsRule",
    "ExistingClassesInClassImplementsRule", "ExistingClassesInInterfaceExtendsRule",
    "ExistingClassInTraitUseRule", "ExistingClassInInstanceOfRule", "EnumSanityRule",
    "DuplicateDeclarationRule", "DuplicateClassDeclarationRule", "NonClassAttributeClassRule",
    "InvalidPromotedPropertiesRule",
    # Properties
    "ReadOnlyPropertyRule", "PropertyInClassRule", "PropertiesInInterfaceRule", "PropertyHookAttributesRule",
    "OverridingPropertyRule", "AccessPropertiesRule", "ReadOnlyPropertyAssignRule",
    # Methods
    "AbstractMethodInNonAbstractClassRule", "AbstractPrivateMethodRule", "FinalPrivateMethodRule",
    "MethodVisibilityInInterfaceRule", "ConstructorReturnTypeRule", "MissingMethodImplementationRule",
    "MissingMagicSerializationMethodsRule", "MethodAttributesRule", "OverridingMethodRule",
    "CallMethodsRule", "CallStaticMethodsRule", "MissingMethodReturnTypehintRule",
    "MissingMethodParameterTypehintRule",
    # Comparison (constant-condition + strict-comparison; type-map driven, level 4)
    "IfConstantConditionRule", "ElseIfConstantConditionRule", "TernaryOperatorConstantConditionRule",
    "WhileLoopAlwaysFalseConditionRule", "WhileLoopAlwaysTrueConditionRule", "DoWhileLoopConstantConditionRule",
    "BooleanNotConstantConditionRule", "BooleanAndConstantConditionRule", "BooleanOrConstantConditionRule",
    "LogicalXorConstantConditionRule", "StrictComparisonOfDifferentTypesRule",
    # Comparison constant folding (Cap #2: php_infer::eval_const)
    "ConstantLooseComparisonRule", "NumberComparisonOperatorsConstantConditionRule",
    # Operators (invalid binary/unary/comparison; type-map driven, level 2)
    "InvalidBinaryOperationRule", "InvalidUnaryOperationRule", "InvalidComparisonOperationRule",
    # Cast (invalid cast + echo/print/encapsed non-string; type-map driven, level 2)
    "InvalidCastRule", "EchoRule", "PrintRule", "InvalidPartOfEncapsedStringRule",
    # PhpDoc (structural, via our own php_phpdoc parser, level 2)
    "WrongVariableNameInVarTagRule", "InvalidPHPStanDocTagRule",
    # PhpDoc type-subtyping (Cap #3: resolve_doc_type + resolve_ast_type + is_assignable)
    "IncompatiblePhpDocTypeRule",
    # Functions (structural + missing-typehint)
    "PrintfArrayParametersRule", "DuplicateFunctionDeclarationRule", "ReturnNullsafeByRefRule",
    "ArrowFunctionReturnNullsafeByRefRule", "CallToFunctionStatementWithoutSideEffectsRule",
    "UselessFunctionReturnValueRule", "MissingFunctionReturnTypehintRule", "MissingFunctionParameterTypehintRule",
    # Variables
    "ThisInGlobalStatementRule", "ThisInStaticStatementRule", "InvalidVariableAssignRule", "VariableCloningRule",
    # DeadCode
    "UnreachableStatementRule", "UnusedPrivateMethodRule", "UnusedPrivateConstantRule",
    "UnusedPrivatePropertyRule", "NoopRule",
    # Attribute-usage family (Cap #7: attribute-target reflection -> attribute.usage rule)
    "ClassAttributesRule", "ClassConstantAttributesRule", "EnumCaseAttributesRule",
    "FunctionAttributesRule", "MethodAttributesRule", "ParamAttributesRule",
    "PropertyAttributesRule", "TraitAttributesRule",
    # Cap #4: typed builtin stubs + castable-to-string predicate
    "ImplodeParameterCastableToStringRule",
    # Cap #5: definedness lattice
    "DefinedVariableRule",
    # Cap #8: callable-type resolution
    "PipeOperatorRule", "CallCallablesRule",
}
# Rules we can't implement yet, with the reason.
_TYPES = "needs the type system (operand/value types)"
DEFERRED = {
    "DeprecatedCastRule": "lexer normalizes cast spelling; AST lacks (integer)/(boolean)/(double)/(binary) distinction",
    "RequireFileExistsRule": "needs the type system (const-string operand) + filesystem access",
    "NonexistentOffsetInArrayDimFetchRule": _TYPES,
    "InvalidKeyInArrayDimFetchRule": _TYPES,
    "InvalidKeyInArrayItemRule": _TYPES,
    "OffsetAccessAssignmentRule": _TYPES,
    "OffsetAccessAssignOpRule": _TYPES,
    "OffsetAccessValueAssignmentRule": _TYPES,
    "IterableInForeachRule": _TYPES,
    "DeadForeachRule": _TYPES,
    "ArrayUnpackingRule": _TYPES,
    "UnpackIterableInArrayRule": _TYPES,
    "ArrayDestructuringRule": _TYPES,
}

level_params = {
0:[], 1:["checkMaybeUndefinedVariables","checkExtraArguments","reportMagicMethods","reportMagicProperties"],
2:["checkClassCaseSensitivity","checkPhpDocMissingReturn"],
3:["checkPhpDocMethodSignatures"],
4:["checkAdvancedIsset"],
5:["checkFunctionArgumentTypes","checkArgumentsPassedByReference"],
6:["checkMissingVarTagTypehint","checkMissingTypehints"],
7:["checkUnionTypes","reportMaybes"],
8:["checkNullables"],
9:["checkExplicitMixed"],
10:["checkImplicitMixed"],
}

# Levels 7-10 are not rule classes but modes of RuleLevelHelper. These are the
# concrete work items (checkbox title, description).
strictness_items = {
7:[
 ("Union-type member access (`checkUnionTypes`)",
  "A method call / property access / array offset on a union must be valid for **all** members; report "
  "when only some support it (partial union). Today `php_infer::is_assignable` accepts a union if any arm fits."),
 ("Report \"maybe\" mismatches (`reportMaybes`)",
  "Report argument/return/offset mismatches that only *might* be wrong — consumed by ~10 existing rules "
  "(e.g. `Functions/CallCallablesRule`, `Methods/MethodSignatureRule`, `Arrays/NonexistentOffsetInArrayDimFetchRule`)."),
],
8:[
 ("Nullable member access (`checkNullables`)",
  "Calling a method / accessing a property / offset on a `T|null` is an error — don't silently strip null "
  "first. (The classic \"Cannot call method X() on T|null\".)"),
],
9:[
 ("Strict explicit mixed (`checkExplicitMixed`)",
  "A value declared `mixed` is only assignable to `mixed`; using it where a concrete type is required "
  "(call/access/argument/return) is an error. Tightens `is_assignable(mixed, T)` from its lenient `true`."),
],
10:[
 ("Strict implicit mixed (`checkImplicitMixed`)",
  "Same as level 9 but also for **implicit** mixed — values whose type we couldn't infer, not just those "
  "declared `mixed`. (PHPStan 2.0; `max` = level 10.)"),
],
}

out = []
w = out.append
w("# PHPStan rule catalog — Phase 1 backlog\n")
w(f"> Generated from a checkout of **phpstan/phpstan-src @ 2.2.x** (`./phpstan-src`, gitignored).")
w(f"> Source of truth: the `#[RegisteredRule(level: N)]` attribute on each rule class, plus the")
w(f"> feature-toggle rules and parameters in `conf/config.level*.neon`. **{total} attribute-registered")
w(f"> rules** across levels 0–9, plus per-level strictness toggles.\n")
w("**How levels work:** cumulative — level N runs every rule at levels ≤ N. Levels 0–6 introduce")
w("discrete rules; **levels 7–10 add almost no new rule classes** — they flip parameters")
w("(`checkUnionTypes`, `checkNullables`, `checkExplicitMixed`, implicit-mixed) that make the existing")
w("argument/method/property/return rules stricter. Replicating 7–10 means honoring those modes in our")
w("assignability/inference layer, not writing new rules.\n")
w("Each entry is a checkbox so this doubles as the implementation tracker. `id:` lists the phpstan")
w("error identifier(s) the rule emits (literal ones; some are built dynamically).\n")
w("### Already implemented in `php-analyzer`")
w("- [x] **unknown-symbol** — `id:` `class.notFound`, `function.notFound`, `constant.notFound` (level 0; our single rule covers what phpstan spreads across many existence rules)")
w("- [x] **return-type** — `id:` `return.type` (level ~3; flow-tracked return vs declared type)")
w("- [x] **Cast/UnsetCastRule** — `id:` `cast.unset` (level 0)")
w("- [x] **Cast/VoidCastRule** — `id:` `cast.void` (level 0)")
w("- [x] **Keywords/ContinueBreakInLoopRule** — `id:` `continue.outOfLoop`, `break.outOfLoop` (level 0)")
w("- [x] **Keywords/DeclareStrictTypesRule** — `id:` `declareStrictTypes.value`, `declareStrictTypes.notFirst` (level 0)")
w("- [x] **Keywords/GotoUndefinedLabelRule** — `id:` `goto.labelUndefined` (level 0)")
w("- [x] **Keywords/UnusedLabelRule** — `id:` `label.unused` (level 0)")
w("- [x] **Arrays/DuplicateKeysInLiteralArraysRule** — `id:` `array.duplicateKey` (level 0)")
w("- [x] **Arrays/OffsetAccessWithoutDimForReadingRule** — `id:` `offsetAccess.noDim` (level 0)")
w("- [x] **Operators/InvalidAssignVarRule** — `id:` `assign.invalidExpr`, `nullsafe.assign`, `nullsafe.byRef` (level 0)")
w("- [x] **Operators/InvalidIncDecOperationRule** — `id:` `pre/postInc/Dec.expr` (level 0; syntactic half — type half deferred)")
w("- [x] **Operators/BacktickRule** — `id:` `backtick.deprecated` (level 0)")
w("- [x] **Functions** — 10 rules: parameter.duplicate/name/variadicNotLast, function.inner/nameCase, closure.invalidUse/unusedUse, argument.printf/define, arguments.count (existence via unknown-symbol)")
w("- [x] **Classes** — 13 rules: new.* (interface/trait/enum/abstract/static), class/interface extends + implements + traitUse kind checks, instanceof.trait, enum.* sanity, duplicate declaration/member, attribute.* target, property.invalidPromoted")
w("- [x] **Properties** — 7 rules: readonly misuse, property-in-class/interface modifiers, hook attributes, override compatibility, $this->prop existence, readonly-assign-outside-ctor")
w("- [x] **Methods** — 13 rules: abstract/final/visibility modifiers, constructor return/static, missing-impl, magic-serialization, attributes, override compatibility, method existence + arg-count, missing param/return typehints")
w("- [x] **argument.type** (M-T8) — type-aware argument checks at call sites (functions + instance methods) via the per-file type map (`fa.type_of` + `is_assignable`); level 5")
w("")
w("### Prioritization note")
w("Not every level-0 rule matters for a general analyzer. The **`Api`** category and a few")
w("phpstan-internal rules (`NodeConnectingVisitorAttributesRule`, `OldPhpParser4ClassRule`,")
w("`PhpStanNamespaceIn3rdPartyPackageRule`, `RuntimeReflection*`, `GetTemplateTypeRule`) police")
w("**phpstan extension/plugin development**, not user PHP code — skip these. The")
w("`InternalTag` restricted-usage extensions are niche. Focus first on the high-value categories:")
w("`Functions`, `Methods`, `Classes`, `Variables`, `Properties`, `Comparison`, `DeadCode`.")
w("")
w("---\n")

grand = 0
for level in range(0, 10):
    cats = data.get(level, {})
    n_rules = sum(len(v) for v in cats.values())
    grand += n_rules
    if n_rules == 0 and not toggle.get(level):
        continue
    w(f"## Level {level} — {level_theme[level]}")
    if level_params.get(level):
        w(f"*Enables parameters:* `{'`, `'.join(level_params[level])}`  ")
    w(f"*{n_rules} discrete rules.*\n")
    for cat in sorted(cats):
        w(f"### {cat}")
        for cls, src_path, idents in sorted(cats[cat]):
            idtxt = f" — `id:` {', '.join('`'+i+'`' for i in idents)}" if idents else ""
            box = "x" if cls in DONE else " "
            note = f" — _deferred: {DEFERRED[cls]}_" if cls in DEFERRED else ""
            w(f"- [{box}] **{cls}** — `{src_path}`{idtxt}{note}")
        w("")
    if toggle.get(level):
        w(f"*Feature-toggle-gated rules at this level (often bleeding-edge):* " +
          ", ".join(sorted(set(toggle[level]))) + "\n")

w("## Levels 7–10 — strictness modes (RuleLevelHelper)\n")
w("These add **no new rule classes**. They are flags on phpstan's central type-acceptance helper")
w("`phpstan-src/src/Rules/RuleLevelHelper.php` (`findTypeToCheck`/`accepts`), which nearly every")
w("type-aware rule calls. In our architecture they are **modes of `php_infer::is_assignable` plus the")
w("member-access / argument rules** — `is_assignable` is currently lenient on nullables / unions / mixed,")
w("and each level tightens one of those. Implement them as the corresponding lower-level rules land.\n")
for level in range(7, 11):
    w(f"### Level {level} — {level_theme[level]}")
    w(f"*Enables parameters:* `{'`, `'.join(level_params[level])}` · *location:* `phpstan-src/src/Rules/RuleLevelHelper.php`\n")
    for title, desc in strictness_items[level]:
        w(f"- [ ] **{title}** — {desc}")
    w("")
strict_count = sum(len(v) for v in strictness_items.values())
w("---\n")
w(f"**Totals:** {grand} discrete rules across levels 0–9, plus {strict_count} strictness-mode work "
  f"items for levels 7–10 = **{grand + strict_count} checklist items**. "
  f"Level breakdown: " + ", ".join(f"L{l}={sum(len(v) for v in data.get(l,{}).values())}" for l in range(0,10)) + ".")

open("/Users/ben/Projects/php-ast/docs/phpstan-rules.md","w").write("\n".join(out)+"\n")
print(f"wrote docs/phpstan-rules.md — {total} rules")
print("level counts:", {l: sum(len(v) for v in data.get(l,{}).values()) for l in range(0,10)})
