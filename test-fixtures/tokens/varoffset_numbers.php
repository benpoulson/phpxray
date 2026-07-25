<?php
// T_NUM_STRING inside "$a[...]" follows Zend's {LNUM}|{HNUM}|{BNUM}|{ONUM}:
// radix digits only after their prefix, `_` only between two digits, and no
// float/exponent form. Everything else ends the token and lexes as T_STRING.
//
// NOTE: several cases below are deliberately NOT valid PHP *grammar* (e.g.
// "$a[12ef]" is a parse error). This fixture is consumed only by the
// tokenizer-level golden harness, whose oracle is token_get_all() — which
// tokenizes without parsing. Do not run php -l over it.
echo "$a[12ef]";
echo "$a[0x1f]";
echo "$a[0xAB_CD]";
echo "$a[0X1F]";
echo "$a[1_2]";
echo "$a[0b12]";
echo "$a[012]";
echo "$a[0o7]";
echo "$a[-5]";
echo "$a[0]";
echo "$a[1e3]";
echo "$a[1_]";
echo "$a[12_ef]";
echo "$a[0x_1]";
echo "$a[0x]";
echo "$a[1__2]";
echo "$a[00]";
