(benchmark fuzzsmt
:logic QF_AUFBV
:status sat
:extrafuns ((v0 BitVec[12]))
:extrafuns ((v1 BitVec[14]))
:extrafuns ((v2 BitVec[9]))
:extrafuns ((a3 Array[5:3]))
:formula
(let (?e4 bv0[2])
(let (?e5 bv3960[12])
(let (?e6 (ite (bvsge v0 (sign_extend[3] v2)) bv1[1] bv0[1]))
(let (?e7 (concat ?e4 v1))
(let (?e8 (ite (bvule (zero_extend[2] ?e5) v1) bv1[1] bv0[1]))
(let (?e9 (select a3 (zero_extend[4] ?e6)))
(let (?e10 (select a3 (extract[7:3] v2)))
(let (?e11 (select a3 (sign_extend[2] ?e9)))
(let (?e12 (select a3 (extract[11:7] v0)))
(let (?e13 (bvneg ?e8))
(let (?e14 (bvnot ?e9))
(let (?e15 (rotate_left[2] ?e12))
(let (?e16 (bvnand (sign_extend[2] ?e6) ?e15))
(let (?e17 (zero_extend[0] ?e7))
(let (?e18 (zero_extend[13] ?e9))
(let (?e19 (bvsrem (zero_extend[6] ?e10) v2))
(let (?e20 (bvsdiv (sign_extend[4] ?e5) ?e7))
(let (?e21 (bvxnor v0 (sign_extend[9] ?e14)))
(let (?e22 (bvnot ?e11))
(let (?e23 (ite (distinct ?e4 ?e4) bv1[1] bv0[1]))
(let (?e24 (ite (= bv1[1] (extract[9:9] v1)) ?e15 ?e9))
(flet ($e25 (bvsle (zero_extend[13] ?e10) ?e17))
(flet ($e26 (bvsle ?e5 ?e21))
(flet ($e27 (bvsgt (zero_extend[1] ?e4) ?e11))
(flet ($e28 (bvult v1 (sign_extend[11] ?e15)))
(flet ($e29 (= v0 (zero_extend[11] ?e23)))
(flet ($e30 (bvuge ?e7 (sign_extend[15] ?e8)))
(flet ($e31 (bvslt (sign_extend[6] ?e22) ?e19))
(flet ($e32 (bvuge ?e10 ?e15))
(flet ($e33 (bvsgt (zero_extend[13] ?e12) ?e7))
(flet ($e34 (= ?e11 ?e16))
(flet ($e35 (bvslt (zero_extend[1] ?e4) ?e10))
(flet ($e36 (= ?e17 (sign_extend[4] ?e21)))
(flet ($e37 (bvsgt (sign_extend[14] ?e4) ?e18))
(flet ($e38 (bvsgt (zero_extend[15] ?e8) ?e20))
(flet ($e39 (bvult (zero_extend[13] ?e16) ?e20))
(flet ($e40 (bvslt v1 (zero_extend[11] ?e12)))
(flet ($e41 (bvsge (sign_extend[11] ?e8) v0))
(flet ($e42 (bvsge ?e21 ?e5))
(flet ($e43 (distinct (sign_extend[1] ?e4) ?e12))
(flet ($e44 (bvsgt ?e17 (sign_extend[13] ?e12)))
(flet ($e45 (bvult v2 (sign_extend[6] ?e9)))
(flet ($e46 (bvuge ?e9 ?e12))
(flet ($e47 (bvugt ?e24 ?e10))
(flet ($e48 (bvule (zero_extend[2] ?e13) ?e12))
(flet ($e49 (bvugt ?e16 ?e10))
(flet ($e50 (bvuge (sign_extend[2] ?e23) ?e10))
(flet ($e51 (bvult ?e5 (zero_extend[11] ?e13)))
(flet ($e52 (bvsge ?e17 (zero_extend[13] ?e10)))
(flet ($e53 (bvsle (zero_extend[11] ?e9) v1))
(flet ($e54 (bvsgt ?e19 (zero_extend[6] ?e10)))
(flet ($e55 (bvslt ?e10 ?e10))
(flet ($e56 (bvsgt (sign_extend[2] ?e13) ?e10))
(flet ($e57 (= ?e18 ?e20))
(flet ($e58 (bvsgt v0 (zero_extend[3] v2)))
(flet ($e59 (distinct (zero_extend[1] ?e6) ?e4))
(flet ($e60 (bvsge ?e16 ?e15))
(flet ($e61 (distinct (sign_extend[1] ?e4) ?e10))
(flet ($e62 (bvule ?e13 ?e6))
(flet ($e63 (bvsle (sign_extend[2] ?e23) ?e15))
(flet ($e64 (bvuge (zero_extend[11] ?e6) ?e5))
(flet ($e65 (bvslt ?e13 ?e6))
(flet ($e66 (bvule v0 (zero_extend[11] ?e23)))
(flet ($e67 (= (zero_extend[2] ?e8) ?e16))
(flet ($e68 (bvule ?e24 (sign_extend[2] ?e23)))
(flet ($e69 (bvslt ?e22 ?e16))
(flet ($e70 (bvslt (zero_extend[5] v2) v1))
(flet ($e71 (bvult ?e18 (zero_extend[13] ?e10)))
(flet ($e72 (= ?e20 (sign_extend[13] ?e10)))
(flet ($e73 (bvuge ?e11 ?e9))
(flet ($e74 (bvule ?e13 ?e8))
(flet ($e75 (= (zero_extend[11] ?e13) ?e5))
(flet ($e76 (= v2 (sign_extend[8] ?e8)))
(flet ($e77 (distinct (zero_extend[9] ?e24) ?e21))
(flet ($e78 (bvsgt ?e11 (zero_extend[2] ?e23)))
(flet ($e79 (bvsgt ?e24 (zero_extend[1] ?e4)))
(flet ($e80 (bvslt ?e5 (zero_extend[11] ?e8)))
(flet ($e81 (bvult v0 (sign_extend[9] ?e11)))
(flet ($e82 (bvult ?e20 (zero_extend[13] ?e11)))
(flet ($e83 (bvule ?e18 (zero_extend[13] ?e15)))
(flet ($e84 (bvsgt v0 (sign_extend[9] ?e10)))
(flet ($e85 (= ?e17 (sign_extend[15] ?e8)))
(flet ($e86 (distinct v2 (zero_extend[8] ?e8)))
(flet ($e87 (bvsge ?e18 (zero_extend[13] ?e22)))
(flet ($e88 (bvsle ?e14 (zero_extend[1] ?e4)))
(flet ($e89 (and $e52 $e30))
(flet ($e90 (xor $e61 $e77))
(flet ($e91 (or $e32 $e29))
(flet ($e92 (or $e84 $e66))
(flet ($e93 (xor $e49 $e39))
(flet ($e94 (implies $e48 $e73))
(flet ($e95 (and $e79 $e50))
(flet ($e96 (or $e88 $e92))
(flet ($e97 (xor $e28 $e67))
(flet ($e98 (implies $e75 $e76))
(flet ($e99 (not $e68))
(flet ($e100 (iff $e34 $e83))
(flet ($e101 (iff $e90 $e56))
(flet ($e102 (xor $e60 $e74))
(flet ($e103 (if_then_else $e37 $e36 $e100))
(flet ($e104 (implies $e53 $e26))
(flet ($e105 (or $e87 $e27))
(flet ($e106 (if_then_else $e55 $e105 $e59))
(flet ($e107 (and $e63 $e31))
(flet ($e108 (if_then_else $e99 $e91 $e106))
(flet ($e109 (iff $e69 $e103))
(flet ($e110 (iff $e57 $e44))
(flet ($e111 (not $e40))
(flet ($e112 (or $e70 $e108))
(flet ($e113 (xor $e81 $e71))
(flet ($e114 (iff $e51 $e41))
(flet ($e115 (not $e86))
(flet ($e116 (implies $e82 $e42))
(flet ($e117 (if_then_else $e107 $e97 $e47))
(flet ($e118 (and $e80 $e45))
(flet ($e119 (and $e78 $e115))
(flet ($e120 (xor $e102 $e85))
(flet ($e121 (not $e25))
(flet ($e122 (if_then_else $e110 $e117 $e116))
(flet ($e123 (and $e109 $e96))
(flet ($e124 (if_then_else $e101 $e35 $e122))
(flet ($e125 (iff $e121 $e104))
(flet ($e126 (if_then_else $e119 $e94 $e125))
(flet ($e127 (and $e120 $e120))
(flet ($e128 (not $e58))
(flet ($e129 (iff $e98 $e38))
(flet ($e130 (implies $e43 $e111))
(flet ($e131 (implies $e93 $e54))
(flet ($e132 (if_then_else $e72 $e129 $e124))
(flet ($e133 (xor $e33 $e113))
(flet ($e134 (and $e127 $e133))
(flet ($e135 (not $e131))
(flet ($e136 (or $e123 $e64))
(flet ($e137 (xor $e118 $e134))
(flet ($e138 (not $e95))
(flet ($e139 (iff $e62 $e62))
(flet ($e140 (or $e139 $e89))
(flet ($e141 (implies $e130 $e135))
(flet ($e142 (if_then_else $e132 $e128 $e132))
(flet ($e143 (iff $e46 $e136))
(flet ($e144 (if_then_else $e137 $e138 $e138))
(flet ($e145 (and $e126 $e141))
(flet ($e146 (if_then_else $e114 $e140 $e145))
(flet ($e147 (implies $e144 $e143))
(flet ($e148 (iff $e147 $e146))
(flet ($e149 (if_then_else $e142 $e148 $e65))
(flet ($e150 (or $e149 $e112))
(flet ($e151 (and $e150 (not (= ?e7 bv0[16]))))
(flet ($e152 (and $e151 (not (= ?e7 (bvnot bv0[16])))))
(flet ($e153 (and $e152 (not (= v2 bv0[9]))))
(flet ($e154 (and $e153 (not (= v2 (bvnot bv0[9])))))
$e154
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

