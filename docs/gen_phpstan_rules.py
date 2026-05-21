import collections
import os
import re
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.environ.get("PHPSTAN_SRC", os.path.join(ROOT, "phpstan-src"))
RULES_DIR = os.path.join(SRC, "src")

attr_re = re.compile(r"#\[RegisteredRule\(level:\s*(\d+)\)\]")
class_re = re.compile(r"(?:final |abstract )?class (\w+)")
ident_re = re.compile(r"->identifier\(\s*'([^']+)'")

EXTRA_IDENTS = {
    "DateTimeInstantiationRule": ["new.dateTime", "new.dateTimeImmutable"],
    # Emitted by the helper class NonexistentOffsetInArrayDimFetchCheck.
    "NonexistentOffsetInArrayDimFetchRule": ["offsetAccess.notFound"],
}

NON_USER_CODE = {
    # PHPStan extension-development API policy rules. `php-analyzer` targets
    # user PHP projects, and the runtime registry intentionally skips this
    # category.
    "ApiClassConstFetchRule",
    "ApiClassExtendsRule",
    "ApiClassImplementsRule",
    "ApiInstanceofRule",
    "ApiInstanceofTypeRule",
    "ApiInstantiationRule",
    "ApiInterfaceExtendsRule",
    "ApiMethodCallRule",
    "ApiStaticCallRule",
    "ApiTraitUseRule",
    "GetTemplateTypeRule",
    "NodeConnectingVisitorAttributesRule",
    "OldPhpParser4ClassRule",
    "PhpStanNamespaceIn3rdPartyPackageRule",
    "RuntimeReflectionFunctionRule",
    "RuntimeReflectionInstantiationRule",
}

LEVEL_THEME = {
    0: "Basic existence + obvious mistakes (unknown classes/functions/methods on $this, wrong #args, always-undefined vars)",
    1: "Possibly-undefined variables; magic methods/properties via __call/__get",
    2: "Unknown methods on all expressions; PHPDoc validation",
    3: "Return types; property type assignments",
    4: "Basic dead code (always-false instanceof, dead else, unreachable, too-wide throws)",
    5: "Argument types passed to functions/methods; by-ref args",
    6: "Missing typehints (params/returns/properties/@var)",
    7: "Partial union types (members not supporting a call); reportMaybes",
    8: "Calling methods / accessing properties on nullable types",
    9: "Strict mixed (explicit mixed only assignable to mixed)",
    10: "Implicit mixed reported too (PHPStan 2.0)",
}

LEVEL_PARAMS = {
    0: [],
    1: ["checkMaybeUndefinedVariables", "checkExtraArguments", "reportMagicMethods", "reportMagicProperties"],
    2: ["checkClassCaseSensitivity", "checkPhpDocMissingReturn"],
    3: ["checkPhpDocMethodSignatures"],
    4: ["checkAdvancedIsset"],
    5: ["checkFunctionArgumentTypes", "checkArgumentsPassedByReference"],
    6: ["checkMissingVarTagTypehint", "checkMissingTypehints"],
    7: ["checkUnionTypes", "reportMaybes"],
    8: ["checkNullables"],
    9: ["checkExplicitMixed"],
    10: ["checkImplicitMixed"],
}

STRICTNESS_ITEMS = {
    7: [
        (
            "checkUnionTypes",
            "Union-type member access",
            "A method call / property access / array offset on a union must be valid for all members.",
        ),
        (
            "reportMaybes",
            'Report "maybe" mismatches',
            "Report argument/return/offset mismatches that only might be wrong.",
        ),
    ],
    8: [
        (
            "checkNullables",
            "Nullable member access",
            "Calling a method / accessing a property / offset on a nullable value is an error.",
        ),
    ],
    9: [
        (
            "checkExplicitMixed",
            "Strict explicit mixed",
            "A value declared mixed is only assignable to mixed.",
        ),
    ],
    10: [
        (
            "checkImplicitMixed",
            "Strict implicit mixed",
            "Same as level 9, but for values whose type was inferred as implicit mixed.",
        ),
    ],
}


def load_analyzer_manifest():
    proc = subprocess.run(
        ["cargo", "run", "-q", "-p", "xtask", "--", "rule-manifest"],
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    rules = []
    options = set()
    for line in proc.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) != 3:
            continue
        kind, level, name = parts
        if kind == "rule":
            rules.append((int(level), name))
        elif kind == "option":
            options.add(name)
    return sorted(rules), options


def scan_phpstan_rules():
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
            after = text[m.end() :]
            cm = class_re.search(after)
            cls = cm.group(1) if cm else fn[:-4]
            rel = os.path.relpath(path, RULES_DIR)
            parts = rel.split(os.sep)
            if parts[0] == "Rules" and len(parts) >= 3:
                cat = parts[1]
            elif parts[0] == "Rules":
                cat = "(misc)"
            else:
                cat = parts[0]
            idents = sorted(set(ident_re.findall(text)).union(EXTRA_IDENTS.get(cls, [])))
            src_path = "phpstan-src/" + os.path.relpath(path, SRC).replace(os.sep, "/")
            data[level][cat].append((cls, src_path, idents))
            total += 1
    return data, total


def scan_toggle_rules():
    toggle = collections.defaultdict(list)
    confdir = os.path.join(SRC, "conf")
    for n in range(0, 11):
        p = os.path.join(confdir, f"config.level{n}.neon")
        if not os.path.exists(p):
            continue
        with open(p, encoding="utf-8", errors="replace") as f:
            txt = f.read()
        for c in re.findall(r"class:\s*PHPStan\\Rules\\([A-Za-z\\]+)", txt):
            toggle[n].append(c.split("\\")[-1])
    return toggle


manifest_rules, manifest_options = load_analyzer_manifest()
data, total = scan_phpstan_rules()
toggle = scan_toggle_rules()

out = []
w = out.append
w("# PHPStan Rule Catalog\n")
w(
    "> Generated from `./phpstan-src` plus `cargo run -q -p xtask -- rule-manifest`. "
    "The PHPStan catalog is scanned from source; analyzer coverage is owned by the Rust rule registry."
)
w("")
w("## Analyzer Manifest\n")
w("These are the runtime rules currently registered by `php-analyzer`, grouped by activation level.\n")
manifest_by_level = collections.defaultdict(list)
for level, name in manifest_rules:
    manifest_by_level[level].append(name)
for level in sorted(manifest_by_level):
    w(f"### Level {level}")
    for name in manifest_by_level[level]:
        w(f"- [x] `{name}`")
    w("")

w("## Analyzer Strictness Options\n")
for level in range(7, 11):
    w(f"### Level {level} — {LEVEL_THEME[level]}")
    w(f"*PHPStan parameters:* `{'`, `'.join(LEVEL_PARAMS[level])}`\n")
    for option, title, desc in STRICTNESS_ITEMS[level]:
        box = "x" if option in manifest_options else " "
        w(f"- [{box}] **{title}** (`{option}`) — {desc}")
    w("")

w("---\n")
w("## PHPStan Catalog\n")
w(
    "The rows below are PHPStan's registered rule classes. They are not marked as analyzer-complete here; "
    "that truth lives in the analyzer manifest above. PHPStan extension-development API rules are marked "
    "as not applicable to user-code analysis."
)
w("")

grand = 0
for level in range(0, 10):
    cats = data.get(level, {})
    n_rules = sum(len(v) for v in cats.values())
    grand += n_rules
    if n_rules == 0 and not toggle.get(level):
        continue
    w(f"## Level {level} — {LEVEL_THEME[level]}")
    if LEVEL_PARAMS.get(level):
        w(f"*Enables parameters:* `{'`, `'.join(LEVEL_PARAMS[level])}`  ")
    w(f"*{n_rules} discrete rules.*\n")
    for cat in sorted(cats):
        w(f"### {cat}")
        for cls, src_path, idents in sorted(cats[cat]):
            idtxt = f" — `id:` {', '.join('`' + i + '`' for i in idents)}" if idents else ""
            box = "x" if cls in NON_USER_CODE else " "
            note = (
                " — _covered: phpstan extension-development API rule; not applicable to user-code analysis_"
                if cls in NON_USER_CODE
                else ""
            )
            w(f"- [{box}] **{cls}** — `{src_path}`{idtxt}{note}")
        w("")
    if toggle.get(level):
        w(
            "*Feature-toggle-gated rules at this level:* "
            + ", ".join(sorted(set(toggle[level])))
            + "\n"
        )

strict_count = sum(len(v) for v in STRICTNESS_ITEMS.values())
w("---\n")
w(
    f"**Totals:** {grand} discrete PHPStan rules across levels 0-9, plus {strict_count} "
    f"strictness-mode work items for levels 7-10. Analyzer manifest entries: {len(manifest_rules)} "
    f"rules and {len(manifest_options)} enabled strictness options."
)

target = os.path.join(ROOT, "docs", "phpstan-rules.md")
with open(target, "w", encoding="utf-8") as f:
    f.write("\n".join(out) + "\n")
print(f"wrote docs/phpstan-rules.md — {total} phpstan rules, {len(manifest_rules)} analyzer rules")
