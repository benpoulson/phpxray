<?php
/**
 * Golden token fixture generator (TDD Tier A oracle).
 *
 * Usage: php gen_golden.php <source.php>
 *
 * Reads a PHP source file and prints its token stream in the golden fixture
 * format consumed by `php-lexer::golden` — one token per line:
 *
 *     <name>\t<start>..<end>\t<escaped-text>
 *
 * where <name> is PhpToken::getTokenName() (a `T_*` name, or the literal
 * spelling for single-character tokens), the span is a half-open byte range, and
 * the text is escaped with the same scheme as `golden::escape_text`
 * (backslash, newline, CR and TAB).
 */

if ($argc < 2) {
    fwrite(STDERR, "usage: php gen_golden.php <source.php|->\n");
    exit(2);
}

// `-` reads source from stdin (used by the differential corpus checker).
$src = $argv[1] === '-' ? stream_get_contents(STDIN) : file_get_contents($argv[1]);
if ($src === false) {
    fwrite(STDERR, "cannot read {$argv[1]}\n");
    exit(2);
}

function golden_escape(string $s): string {
    return str_replace(
        ['\\', "\n", "\r", "\t"],
        ['\\\\', '\\n', '\\r', '\\t'],
        $s
    );
}

$out = '';
foreach (PhpToken::tokenize($src) as $t) {
    $name = $t->getTokenName();
    $start = $t->pos;
    $end = $t->pos + strlen($t->text);
    $out .= $name . "\t" . $start . '..' . $end . "\t" . golden_escape($t->text) . "\n";
}

echo $out;
