<?php
$a = [1];
$o = new stdClass();
$s1 = "$a[0]";
$s2 = "$a[key]";
$s3 = "{$a[0]}";
$s4 = "${a}";
$s5 = "$o->p";
$s6 = "{$o->p}";
$s7 = "no interp";
$s8 = "trailing $";
$s9 = "escaped \$notvar";
