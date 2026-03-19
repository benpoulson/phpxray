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
10:["(implicit mixed)"],
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
            w(f"- [ ] **{cls}** — `{src_path}`{idtxt}")
        w("")
    if toggle.get(level):
        w(f"*Feature-toggle-gated rules at this level (often bleeding-edge):* " +
          ", ".join(sorted(set(toggle[level]))) + "\n")

w("## Levels 7–10 — strictness modes (no new rules)")
for level in range(7, 11):
    w(f"- **Level {level}** — {level_theme[level]} (params: `{'`, `'.join(level_params[level])}`)")
w("")
w("---\n")
w(f"**Totals:** {grand} discrete rules across levels 0–9 "
  f"(level breakdown: " + ", ".join(f"L{l}={sum(len(v) for v in data.get(l,{}).values())}" for l in range(0,10)) + ").")

open("/Users/ben/Projects/php-ast/docs/phpstan-rules.md","w").write("\n".join(out)+"\n")
print(f"wrote docs/phpstan-rules.md — {total} rules")
print("level counts:", {l: sum(len(v) for v in data.get(l,{}).values()) for l in range(0,10)})
