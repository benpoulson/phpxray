<?php
/**
 * Canonical Zend-AST dumper (the AST differential oracle).
 *
 * Usage: php dump_ast.php <source.php|->   (reads stdin for `-`)
 *
 * Emits a deterministic, indented s-expression of the AST produced by PHP's own
 * parser (via the `php-ast` extension). The Rust side reproduces the exact same
 * form from our AST; any diff is a real parser divergence.
 *
 * Structure per node:  (KIND[#flags] childKey=<child> ...)
 * Leaves: ints/floats/strings (decoded) / true / false / null.
 * Excluded as non-structural: lineno, docComment, __declId, endLineno.
 */

if ($argc < 2) {
    fwrite(STDERR, "usage: php dump_ast.php <source.php|->\n");
    exit(2);
}
$src = $argv[1] === '-' ? stream_get_contents(STDIN) : file_get_contents($argv[1]);

// Without the extension `ast\parse_code` is simply undefined, and calling it
// throws an `Error` — which the catch below would report as `<<PARSE_ERROR>>`,
// i.e. "PHP rejects this source". Every file would then look like a
// non-candidate, the differ would compare nothing and still exit 0. Fail here
// instead, where the reason is still known.
if (!function_exists('ast\parse_code')) {
    fwrite(STDERR, "the php-ast extension is not loaded (install with `pecl install ast`)\n");
    exit(3);
}

// Suppress compile-time warnings/notices (e.g. octal-overflow, declare-encoding)
// so they don't pollute the AST dump on stdout. We only care about structure.
error_reporting(0);
ini_set('display_errors', '0');

// Children keys that are metadata, not structural AST.
const SKIP = ['docComment' => 1, '__declId' => 1];

function leaf($v): string {
    if (is_int($v)) return (string)$v;
    if (is_float($v)) {
        if (is_nan($v)) return "NAN";
        if (is_infinite($v)) return $v > 0 ? "INF" : "-INF";
        // var_export uses shortest round-trip precision, matching Rust's {:?}.
        $s = var_export($v, true);
        return str_contains($s, '.') || str_contains($s, 'E') ? $s : $s . ".0";
    }
    if (is_string($v)) return '"' . strtr($v, ["\\" => "\\\\", "\"" => "\\\"", "\n" => "\\n", "\r" => "\\r", "\t" => "\\t"]) . '"';
    if ($v === null) return "null";
    if (is_bool($v)) return $v ? "true" : "false";
    return "?";
}

function dump($n, int $ind = 0): string {
    $p = str_repeat("  ", $ind);
    if (!($n instanceof ast\Node)) {
        return $p . leaf($n) . "\n";
    }
    $kind = substr(ast\get_kind_name($n->kind), 4); // strip "AST_"
    $head = $n->flags !== 0 ? "$kind#{$n->flags}" : $kind;
    $out = "$p($head\n";
    foreach ($n->children as $k => $c) {
        if (isset(SKIP[$k])) continue;
        $key = is_int($k) ? "" : "$k=";
        $out .= "$p  $key\n" . dump($c, $ind + 2);
    }
    $out .= "$p)\n";
    return $out;
}

try {
    $ast = ast\parse_code($src, 110);
} catch (\Throwable $e) {
    // Parse error — emit a sentinel so the differ can treat it as "PHP rejects".
    echo "<<PARSE_ERROR>>\n";
    exit(0);
}
echo dump($ast);
