thf(sortdecl_nat, type, s_nat: $tType).
    thf(sortdecl_int, type, s_int: $tType).
    thf(sortdecl_string, type, s_string: $tType).
    thf(sortdecl_empty, type, s_empty: $tType).
    thf(sortdecl_0, type, s_a0: $tType).
    thf(sortdecl_1, type, s_a1: $tType).
    thf(sortdecl_3, type, s_a3: $tType).
    thf(sortdecl_4, type, s_a4: $tType).
    thf(sortdecl_5, type, s_a5: $tType).
    thf(sortdecl_6, type, s_a6: $tType).
    
    thf(typedecl_icst_t_ilt, type, t_ilt: (s_int > (s_int > $o))).
    thf(typedecl_t_a3, type, t_a3: (s_a0 > $o)).
    thf(typedecl_t_a4, type, t_a4: s_a0).
    thf(typedecl_t_a7, type, t_a7: (s_a1 > (s_a1 > s_a1))).
    thf(typedecl_t_a11, type, t_a11: (s_a5 > (s_a4 > $o))).
    thf(typedecl_t_a12, type, t_a12: (s_a1 > (s_a4 > s_a5))).
    thf(typedecl_t_a13, type, t_a13: (s_a3 > (s_a1 > (s_a1 > s_a1)))).
    thf(typedecl_t_a14, type, t_a14: (s_a3 > (s_a1 > s_a1))).
    thf(typedecl_t_a15, type, t_a15: s_a1).
    thf(typedecl_t_a16, type, t_a16: (s_a3 > (s_a4 > $o))).
    thf(typedecl_t_a17, type, t_a17: (s_a6 > (s_a6 > s_a3))).
    thf(typedecl_t_a18, type, t_a18: (s_a6 > (s_a4 > s_int))).
    thf(typedecl_t_a19, type, t_a19: (s_a3 > (s_a3 > s_a3))).
    thf(typedecl_t_a20, type, t_a20: (s_a3 > s_a3)).
    thf(typedecl_t_a21, type, t_a21: ($o > s_a3)).
    thf(typedecl_t_a24, type, t_a24: s_a3).
    thf(typedecl_t_a25, type, t_a25: s_a1).
    thf(typedecl_t_a26, type, t_a26: s_a4).
    thf(typedecl_t_a27, type, t_a27: s_a4).
    thf(typedecl_t_a28, type, t_a28: s_a1).
    thf(typedecl_t_a29, type, t_a29: s_a0).
    
    thf(fact0, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((&) @ X0) @ X1)) @ (((&) @ X1) @ X0))))).
    thf(fact1, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((&) @ (((&) @ X0) @ X1)) @ X1)) @ (((&) @ X0) @ X1))))).
    thf(fact2, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=>) @ (((=>) @ X0) @ X1)) @ (((=>) @ (((=>) @ X1) @ X0)) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ X1)))))).
    thf(fact3, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=>) @ (((=) @ X0) @ X1)) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ X1))))).
    thf(fact4, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=>) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ X1)) @ (((=) @ X0) @ X1))))).
    thf(fact5, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((=) @ X0) @ (((&) @ X0) @ X1))) @ (((=>) @ X0) @ X1))))).
    thf(fact6, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((=) @ X0) @ X1)) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ X1))))).
    thf(fact7, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=>) @ X0) @ (((=) @ (((&) @ X0) @ X1)) @ X1))))).
    thf(fact8, axiom, (! [X0 : s_a1] : (! [X1 : s_a1] : (! [X2 : s_a1] : (! [X3 : s_a1] : (((^ [L : $o, R : $o] : L = R) @ (((^ [L : s_a1, R : s_a1] : L = R) @ ((t_a7 @ X0) @ X1)) @ ((t_a7 @ X2) @ X3))) @ (((&) @ (((^ [L : s_a1, R : s_a1] : L = R) @ X0) @ X2)) @ (((^ [L : s_a1, R : s_a1] : L = R) @ X1) @ X3)))))))).
    thf(fact9, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ X1)) @ (((=) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true)) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ $true)))))).
    thf(fact10, axiom, (! [X0 : $o] : (! [X1 : $o] : (! [X2 : $o] : (((=>) @ (((=>) @ X0) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ X2))) @ (((^ [L : $o, R : $o] : L = R) @ (((&) @ X0) @ X1)) @ (((&) @ X0) @ X2))))))).
    thf(fact11, axiom, (! [X0 : $o] : (((^ [L : $o, R : $o] : L = R) @ (((&) @ X0) @ X0)) @ X0))).
    thf(fact12, axiom, (! [X0 : $o] : (! [X1 : $o] : (! [X2 : $o] : (((=>) @ (((=>) @ X0) @ X1)) @ (((=>) @ (((&) @ X0) @ X2)) @ (((&) @ X1) @ X2))))))).
    thf(fact13, axiom, (! [X0 : s_a1] : (! [X1 : s_a1] : (! [X2 : s_a1] : (! [X3 : s_a1] : (((=>) @ (((^ [L : s_a1, R : s_a1] : L = R) @ ((t_a7 @ X0) @ X1)) @ ((t_a7 @ X2) @ X3))) @ (((&) @ (((^ [L : s_a1, R : s_a1] : L = R) @ X0) @ X2)) @ (((^ [L : s_a1, R : s_a1] : L = R) @ X1) @ X3)))))))).
    thf(fact14, axiom, (! [X0 : $o] : (((=) @ (((&) @ X0) @ X0)) @ X0))).
    thf(fact15, axiom, (! [X0 : $o] : (! [X1 : $o] : (! [X2 : $o] : (((=) @ (((&) @ (((&) @ X0) @ X1)) @ X2)) @ (((&) @ (((&) @ X0) @ X2)) @ (((&) @ X1) @ X2))))))).
    thf(fact16, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((&) @ X0) @ X1)) @ (((&) @ X1) @ X0))))).
    thf(fact17, axiom, (! [X0 : $o] : (! [X1 : $o] : (! [X2 : $o] : (((=) @ (((&) @ X0) @ (((&) @ X1) @ X2))) @ (((&) @ X1) @ (((&) @ X0) @ X2))))))).
    thf(fact18, axiom, (! [X0 : s_a1] : (! [X1 : s_a3] : (! [X2 : s_a4] : (! [X3 : s_a4] : (((=) @ ((t_a11 @ ((t_a12 @ (((t_a13 @ X1) @ X0) @ X0)) @ X2)) @ X3)) @ ((t_a11 @ ((t_a12 @ X0) @ X2)) @ X3))))))).
    thf(fact19, axiom, (! [X0 : s_a3] : (! [X1 : s_a3] : (! [X2 : s_a1] : (! [X3 : s_a1] : (! [X4 : s_a1] : (! [X5 : s_a4] : (! [X6 : s_a4] : (((=) @ ((t_a11 @ ((t_a12 @ (((t_a13 @ X0) @ (((t_a13 @ X1) @ X2) @ X3)) @ X4)) @ X5)) @ X6)) @ ((t_a11 @ ((t_a12 @ (((t_a13 @ X1) @ (((t_a13 @ X0) @ X2) @ X4)) @ (((t_a13 @ X0) @ X3) @ X4))) @ X5)) @ X6)))))))))).
    thf(fact20, axiom, (! [X0 : s_a1] : (! [X1 : s_a1] : (! [X2 : s_a1] : (! [X3 : s_a4] : (! [X4 : s_a4] : (((=) @ ((t_a11 @ ((t_a12 @ ((t_a7 @ ((t_a7 @ X0) @ X1)) @ X2)) @ X3)) @ X4)) @ ((t_a11 @ ((t_a12 @ ((t_a7 @ X0) @ ((t_a7 @ X1) @ X2))) @ X3)) @ X4)))))))).
    thf(fact21, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((^ [L : $o, R : $o] : L = R) @ (((&) @ X0) @ X1)) @ $true)) @ (((&) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true)) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ $true)))))).
    thf(fact22, axiom, (! [X0 : ($o > $o)] : (((=) @ (! [X1 : $o] : (X0 @ X1))) @ (((&) @ (X0 @ $false)) @ (X0 @ $true))))).
    thf(fact23, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ (((|) @ X0) @ X1))) @ (((=>) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true)) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ $true)))))).
    thf(fact24, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ (((&) @ X0) @ X1))) @ (((=>) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true)) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ $true)))))).
    thf(fact25, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ (((&) @ X0) @ X1))) @ (((=>) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ $true)) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true)))))).
    thf(fact26, axiom, (! [X0 : $o] : (((=) @ (((=>) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $false)) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true))) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true)))).
    thf(fact27, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ (((|) @ X0) @ X1))) @ (((=>) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ $true)) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true)))))).
    thf(fact28, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((^ [L : $o, R : $o] : L = R) @ (((|) @ X0) @ X1)) @ X1)) @ (((=>) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true)) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ $true)))))).
    thf(fact29, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((^ [L : $o, R : $o] : L = R) @ (((&) @ X0) @ X1)) @ X0)) @ (((=>) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true)) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ $true)))))).
    thf(fact30, axiom, (! [X0 : $o] : (((=) @ (((=>) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true)) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $false))) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $false)))).
    thf(fact31, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((^ [L : $o, R : $o] : L = R) @ (((|) @ X0) @ X1)) @ X0)) @ (((=>) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ $true)) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true)))))).
    thf(fact32, axiom, (! [X0 : $o] : (! [X1 : $o] : (((^ [L : $o, R : $o] : L = R) @ (((^ [L : $o, R : $o] : L = R) @ (((&) @ X0) @ X1)) @ $true)) @ (((&) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true)) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ $true)))))).
    thf(fact33, axiom, (! [X0 : $o] : (! [X1 : $o] : (((=) @ (((^ [L : $o, R : $o] : L = R) @ (((&) @ X0) @ X1)) @ X1)) @ (((=>) @ (((^ [L : $o, R : $o] : L = R) @ X1) @ $true)) @ (((^ [L : $o, R : $o] : L = R) @ X0) @ $true)))))).
    thf(fact34, axiom, (! [X0 : s_a1] : (! [X1 : s_a3] : (! [X2 : s_a4] : (! [X3 : s_a4] : (((=) @ ((t_a11 @ ((t_a12 @ ((t_a14 @ X1) @ X0)) @ X2)) @ X3)) @ ((t_a11 @ ((t_a12 @ (((t_a13 @ X1) @ ((t_a7 @ X0) @ ((t_a14 @ X1) @ X0))) @ t_a15)) @ X2)) @ X3))))))).
    thf(fact35, axiom, (! [X0 : s_a4] : (! [X1 : s_a6] : (! [X2 : s_a6] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ ((t_a17 @ X1) @ X2)) @ X0)) @ ((^ [X : $o] : X) @ ((t_ilt @ ((t_a18 @ X1) @ X0)) @ ((t_a18 @ X2) @ X0)))))))).
    thf(fact36, axiom, (! [X0 : s_a4] : (! [X1 : s_a3] : (! [X2 : s_a3] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ ((t_a19 @ X1) @ X2)) @ X0)) @ (((&) @ ((t_a16 @ X1) @ X0)) @ ((t_a16 @ X2) @ X0))))))).
    thf(fact37, axiom, (! [X0 : s_a4] : (! [X1 : s_a3] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a20 @ X1)) @ X0)) @ ((~) @ ((t_a16 @ X1) @ X0)))))).
    thf(fact38, axiom, (! [X0 : s_a4] : (! [X1 : $o] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ X1)) @ X0)) @ X1)))).
    thf(fact39, axiom, (! [X0 : s_a4] : (! [X1 : s_a4] : (! [X2 : s_a3] : (((=>) @ ((t_a11 @ ((t_a12 @ (((t_a13 @ X2) @ t_a15) @ t_a15)) @ X0)) @ X1)) @ (((^ [L : s_a4, R : s_a4] : L = R) @ X1) @ X0)))))).
    thf(fact40, axiom, (! [X0 : s_a3] : (! [X1 : s_a1] : (! [X2 : s_a3] : (! [X3 : s_a1] : (((^ [L : $o, R : $o] : L = R) @ (((^ [L : s_a1, R : s_a1] : L = R) @ ((t_a14 @ X0) @ X1)) @ ((t_a14 @ X2) @ X3))) @ (((&) @ (((^ [L : s_a3, R : s_a3] : L = R) @ X0) @ X2)) @ (((^ [L : s_a1, R : s_a1] : L = R) @ X1) @ X3)))))))).
    thf(fact41, axiom, (! [X0 : s_a3] : (! [X1 : s_a1] : (! [X2 : s_a3] : (! [X3 : s_a1] : (((=>) @ (((^ [L : s_a1, R : s_a1] : L = R) @ ((t_a14 @ X0) @ X1)) @ ((t_a14 @ X2) @ X3))) @ (((&) @ (((^ [L : s_a3, R : s_a3] : L = R) @ X0) @ X2)) @ (((^ [L : s_a1, R : s_a1] : L = R) @ X1) @ X3)))))))).
    thf(fact42, axiom, (! [X0 : s_a3] : (! [X1 : s_a1] : (! [X2 : s_a4] : (! [X3 : s_a4] : (! [X4 : s_a1] : (((=>) @ ((t_a11 @ ((t_a12 @ ((t_a14 @ X0) @ X1)) @ X2)) @ X3)) @ (((=>) @ (! [X5 : s_a4] : (! [X6 : s_a4] : (((=) @ ((t_a11 @ ((t_a12 @ X1) @ X5)) @ X6)) @ ((t_a11 @ ((t_a12 @ X4) @ X5)) @ X6))))) @ ((t_a11 @ ((t_a12 @ ((t_a14 @ X0) @ X4)) @ X2)) @ X3))))))))).
    thf(fact43, axiom, ((~) @ (((=) @ ((t_a11 @ ((t_a12 @ ((t_a14 @ t_a24) @ t_a25)) @ t_a26)) @ t_a27)) @ ((t_a11 @ ((t_a12 @ ((t_a14 @ t_a24) @ t_a28)) @ t_a26)) @ t_a27)))).
    thf(fact44, axiom, (! [X0 : s_a4] : (! [X1 : s_a4] : (((=) @ ((t_a11 @ ((t_a12 @ t_a25) @ X0)) @ X1)) @ ((t_a11 @ ((t_a12 @ t_a28) @ X0)) @ X1))))).
    thf(fact45, axiom, (((^ [L : $o, R : $o] : L = R) @ (t_a3 @ t_a4)) @ (t_a3 @ t_a4))).
    thf(fact46, axiom, (((^ [L : $o, R : $o] : L = R) @ (t_a3 @ t_a29)) @ (t_a3 @ t_a4))).
    thf(fact47, axiom, (((^ [L : $o, R : $o] : L = R) @ (t_a3 @ t_a29)) @ (t_a3 @ t_a4))).
    thf(fact48, axiom, (((^ [L : $o, R : $o] : L = R) @ (t_a3 @ t_a29)) @ (t_a3 @ t_a4))).
    thf(fact49, axiom, (((^ [L : $o, R : $o] : L = R) @ (t_a3 @ t_a29)) @ (t_a3 @ t_a4))).
    thf(fact50, axiom, (((^ [L : $o, R : $o] : L = R) @ (t_a3 @ t_a29)) @ (t_a3 @ t_a4))).
    thf(fact51, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ (t_a3 @ t_a29))) @ X0)) @ (t_a3 @ t_a4)))).
    thf(fact52, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ (t_a3 @ t_a4))) @ X0)) @ (t_a3 @ t_a4)))).
    thf(fact53, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact54, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact55, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact56, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact57, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact58, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact59, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact60, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact61, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact62, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact63, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact64, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact65, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact66, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact67, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact68, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact69, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact70, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact71, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact72, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact73, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact74, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact75, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact76, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact77, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact78, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact79, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact80, axiom, (((^ [L : $o, R : $o] : L = R) @ $true) @ $true)).
    thf(fact81, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact82, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact83, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact84, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact85, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact86, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact87, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact88, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact89, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact90, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact91, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact92, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact93, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact94, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact95, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $false)) @ X0)) @ $false))).
    thf(fact96, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact97, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact98, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact99, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact100, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact101, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact102, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact103, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $false)) @ X0)) @ $false))).
    thf(fact104, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact105, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $false)) @ X0)) @ $false))).
    thf(fact106, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact107, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact108, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact109, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact110, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact111, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))).
    thf(fact112, axiom, (! [X0 : s_a4] : (((^ [L : $o, R : $o] : L = R) @ ((t_a16 @ (t_a21 @ $true)) @ X0)) @ $true))). 