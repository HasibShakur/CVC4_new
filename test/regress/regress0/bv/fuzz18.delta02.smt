(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v5 BitVec[4]))
:extrafuns ((v0 BitVec[4]))
:extrafuns ((v8 BitVec[4]))
:extrafuns ((v3 BitVec[4]))
:extrafuns ((v2 BitVec[4]))
:extrafuns ((v6 BitVec[4]))
:extrafuns ((v1 BitVec[4]))
:status sat
:formula
(flet ($n1 true)
(let (?n2 bv1[1])
(let (?n3 (extract[1:1] v2))
(flet ($n4 (= ?n2 ?n3))
(let (?n5 bv4[4])
(let (?n6 (bvadd v1 v6))
(let (?n7 (bvsub ?n6 v6))
(let (?n8 (ite $n4 ?n5 ?n7))
(flet ($n9 (bvule ?n8 v2))
(let (?n10 bv0[1])
(let (?n11 (ite $n9 ?n2 ?n10))
(let (?n12 (zero_extend[3] ?n11))
(let (?n13 bv1[4])
(flet ($n14 (bvsge ?n12 ?n13))
(flet ($n15 false)
(let (?n16 bv0[4])
(let (?n17 (bvand ?n5 v3))
(let (?n18 (bvlshr v1 ?n17))
(flet ($n19 (bvslt ?n5 v2))
(let (?n20 (ite $n19 ?n2 ?n10))
(let (?n21 (zero_extend[3] ?n20))
(flet ($n22 (bvugt ?n18 ?n21))
(let (?n23 (ite $n22 ?n2 ?n10))
(let (?n24 (zero_extend[3] ?n23))
(flet ($n25 (bvsge ?n16 ?n24))
(let (?n26 (ite $n25 ?n2 ?n10))
(let (?n27 (sign_extend[3] ?n26))
(flet ($n28 (bvugt ?n13 ?n27))
(flet ($n29 (bvsle ?n16 v1))
(let (?n30 (ite $n29 ?n2 ?n10))
(let (?n31 (zero_extend[3] ?n30))
(flet ($n32 (bvslt ?n16 ?n31))
(let (?n33 (ite $n32 ?n2 ?n10))
(let (?n34 (zero_extend[3] ?n33))
(flet ($n35 (bvslt ?n34 ?n13))
(flet ($n36 (or $n15 $n28 $n35))
(flet ($n37 (bvuge v0 v6))
(let (?n38 (ite $n37 ?n2 ?n10))
(let (?n39 (sign_extend[3] ?n38))
(flet ($n40 (bvule ?n39 ?n16))
(let (?n41 (ite $n40 ?n2 ?n10))
(let (?n42 (zero_extend[3] ?n41))
(flet ($n43 (bvule ?n42 ?n16))
(flet ($n44 (bvuge v1 v6))
(let (?n45 (ite $n44 ?n2 ?n10))
(flet ($n46 (= ?n2 ?n45))
(let (?n47 (ite $n46 ?n13 ?n16))
(flet ($n48 (bvsge ?n47 ?n16))
(flet ($n49 (not $n48))
(flet ($n50 (or $n15 $n43 $n49))
(let (?n51 (bvshl ?n5 v1))
(flet ($n52 (bvule ?n51 ?n16))
(let (?n53 (sign_extend[3] ?n45))
(flet ($n54 (bvult v0 ?n53))
(let (?n55 (ite $n54 ?n2 ?n10))
(let (?n56 (bvlshr ?n2 ?n55))
(flet ($n57 (= ?n2 ?n56))
(flet ($n58 (bvuge ?n16 ?n51))
(let (?n59 (ite $n58 ?n2 ?n10))
(let (?n60 (zero_extend[3] ?n59))
(flet ($n61 (bvugt ?n60 ?n16))
(flet ($n62 (bvslt v6 ?n16))
(let (?n63 (ite $n62 ?n2 ?n10))
(flet ($n64 (distinct ?n2 ?n63))
(flet ($n65 (or $n15 $n61 $n64))
(flet ($n66 (bvsgt v3 ?n31))
(let (?n67 (ite $n66 ?n2 ?n10))
(let (?n68 (zero_extend[3] ?n67))
(flet ($n69 (= v1 ?n68))
(let (?n70 (bvnot v5))
(flet ($n71 (bvule v6 ?n70))
(flet ($n72 (or $n15 $n69 $n71))
(flet ($n73 (bvule v0 v6))
(let (?n74 (ite $n73 ?n2 ?n10))
(let (?n75 (extract[2:2] ?n47))
(flet ($n76 (bvule ?n74 ?n75))
(flet ($n77 (bvsle ?n16 ?n17))
(flet ($n78 (or $n15 $n76 $n77))
(let (?n79 (bvadd ?n13 ?n13))
(let (?n80 (bvshl ?n18 ?n79))
(flet ($n81 (bvsge ?n16 ?n80))
(flet ($n82 (not $n81))
(let (?n83 (bvand ?n5 ?n70))
(flet ($n84 (bvuge ?n16 ?n83))
(flet ($n85 (not $n84))
(flet ($n86 (or $n15 $n82 $n85))
(let (?n87 (sign_extend[3] ?n2))
(flet ($n88 (bvuge v6 ?n87))
(let (?n89 (ite $n88 ?n2 ?n10))
(flet ($n90 (bvslt ?n23 ?n89))
(let (?n91 (bvand v1 v6))
(let (?n92 (bvxnor ?n16 ?n91))
(let (?n93 (bvxnor ?n16 ?n92))
(flet ($n94 (bvsle ?n79 ?n93))
(flet ($n95 (not $n94))
(let (?n96 (bvcomp v2 v3))
(flet ($n97 (= ?n2 ?n96))
(let (?n98 (bvcomp v0 v5))
(let (?n99 (zero_extend[3] ?n98))
(let (?n100 (ite $n97 v8 ?n99))
(flet ($n101 (distinct ?n16 ?n100))
(flet ($n102 (and $n14 $n36 $n50 $n52 $n57 $n65 $n72 $n78 $n86 $n90 $n95 $n101))
$n102
)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
