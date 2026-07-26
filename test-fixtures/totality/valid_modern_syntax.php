<?php
declare(strict_types=1);
namespace App\Deep\Space;

use App\{Alpha, Beta as Gamma};
use function App\helper;
use const App\LIMIT;

#[Attribute(Attribute::TARGET_ALL)]
final class Widget extends Gamma implements \Countable, \Stringable
{
    use SomeTrait, OtherTrait {
        SomeTrait::a as protected b;
        SomeTrait::c insteadof OtherTrait;
    }

    public const array SHAPES = ['a' => 1];
    private(set) protected string $guarded = 'x';
    public int $hooked { get => $this->guarded ? 1 : 2; set(int $v) { $this->guarded = (string) $v; } }

    public function __construct(
        #[Attr] public readonly ?int $id = null,
        string|int ...$rest,
    ) {}

    public function count(): int { return match(true) { default => 0 }; }
    public function __toString(): string { return <<<TXT
        interp {$this->guarded} and $this->guarded
        TXT; }
}

enum Suit: string implements \JsonSerializable {
    case Hearts = 'H';
    public function jsonSerialize(): mixed { return $this->value; }
}

interface Marker {}
trait SomeTrait { public function a() {} public function c() {} }
trait OtherTrait { public function c() {} }

function gen(): \Generator {
    $x = yield;
    $y = yield 1 => 2;
    yield from gen();
    return $x <=> $y;
}

$fn = static fn(int ...$n): int => array_sum($n);
$cl = function () use (&$fn): mixed { return $fn(...); };
$anon = new #[A] readonly class(1) extends Widget { public function __construct(int $i) { parent::__construct($i); } };
$nested = $anon?->hooked ?? LIMIT;
$arr = [...[1, 2], 'k' => 3];
[$a, [$b, $c]] = $arr;
['k' => $k] = $arr;
$s = "pre {$arr['k']} mid ${a} post $arr[0]";
$b1 = b"binary $a";
$h = <<<'NOW'
raw $notinterpolated
NOW;
$r = `echo $a`;
$t = $a ? yield : 2;
echo $a <=> $b, PHP_EOL;
