<?php
$a = "hello";
$b = "x $a y";
$c = "p $a->name q";
$d = "m $a[0] n";
$e = "k $a[key] j";
$f = "i $a[$idx] h";
$g = "pre {$a} post";
$h = "pre {$a->name} post";
$i = "pre {$obj->arr[1]} post";
$j = "v ${a} w";
$k = "v ${a[0]} w";
$l = "no interp here";
