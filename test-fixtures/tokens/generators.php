<?php
function g() {
    yield 1;
    yield $k => $v;
    yield from $other;
    $x = yield;
}
