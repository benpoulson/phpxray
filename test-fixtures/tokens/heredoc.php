<?php
$a = <<<EOT
plain line
EOT;
$b = <<<TXT
hello $name and {$obj->p}
TXT;
$c = <<<"DQ"
double $x
DQ;
$d = <<<'NOW'
literal $x no interp
NOW;
$e = <<<END
    indented body $v
    END;
