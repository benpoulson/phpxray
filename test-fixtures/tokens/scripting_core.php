<?php
$total = 1 + 2 * 3;
$name = 'Ada';
$greeting = "hello world";
$ok = $total >= 7 && $name !== '';
$x ??= 0;
function add($a, $b) { return $a + $b; }
class Point { public int $x = 0; }
if ($ok) {
    echo add(1, 2);
} elseif ($x) {
    $x--;
} else {
    foreach ([1, 2] as $k => $v) {}
}
