//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function IsConsistentH1RandomPrime(H1,DAB,n)
    K := QuarticCMField(DAB);
    O := MaximalOrder(K);
    D := DAB[1];
    while true do
        p := RandomPrime(n);
        while KroneckerSymbol(D,p) ne 1 do
            p := RandomPrime(n);
        end while;
        prms := Decomposition(O,p);
        if #prms eq 4 then
            if &and[ IsPrincipal(pp[1]) : pp in prms ] then
                break;
            end if;
        end if;
    end while;
    _, degs := QuarticCMFieldOrdinaryWeilNumbers(K,p);
    degs_set := SequenceToSet(degs);
    for r in degs_set do
        FF := FiniteField(p,r);
        PF := PolynomialRing(FF);
        rts := Roots(PolynomialRing(FF)!H1);
        if #degs eq 2 and #degs_set eq 1 then
            if #rts ne Degree(H1) then
                return false, p;
            elif #rts lt Degree(H1) div 2 then
                return false, p;
            end if;
        end if;
    end for;
    return true, p;
end function;

function IsValidLIXClassPolyH1(H1,DAB,prec :
    SmoothnessCheck := true, SmoothnessBound := 10^7, LatticeDimension := 0)
    RR := RealField(8);
    if Degree(H1) eq 0 then return false, Floor(1.414*prec); end if;
    if LatticeDimension eq 0 then
        deg := Degree(H1);
    else
        deg := LatticeDimension-1;
    end if;
    short := RR!prec/deg;
    long := 1.33 * short;
    m1 := RR!Log(10,Max([ Abs(c) : c in Eltseq(H1) ])) + 8;
    bool := m1 le short;
    if m1 le long and not bool then
        bool, p := IsConsistentH1RandomPrime(H1,DAB,32);
    end if;
    if not bool then
        if GetVerbose("IgusaInvariant") gt 0 then
            printf "H1 coefficient size fails: %o > %o\n",  m1, short;
            print "H1:";
            print H1;
        end if;
        return false, Min(Ceiling((deg+2)*m1),2*prec);
    end if;
    if not SmoothnessCheck then return true, _; end if;
    lc_facts, lc_unfacts := TrialDivision(LeadingCoefficient(H1),SmoothnessBound);
    lc_primes := [ p[1] : p in lc_facts ] cat lc_unfacts;
    if Max([1] cat lc_primes) gt SmoothnessBound then
        if GetVerbose("IgusaInvariant") gt 0 then
            print "Leading coefficient factorization fails:";
            print [ Sprintf("%o^%o",p[1],p[2]) : p in lc_facts] cat [ Sprint(p) : p in lc_unfacts ];
            print "H1:";
            print H1;
        end if;
        return false, Floor(1.414*prec);
    end if;
    return true, prec;
end function;

function IsValidLIXClassPolyNi(Ni,prec)
    RR := RealField(16);
    if Ni eq 0 then return false, Floor(1.414*prec); end if;
    Ni_facts, Ni_unfacts := TrialDivision(Ni,10^6);
    Ni_facts := [ p[1] : p in Ni_facts ] cat Ni_unfacts;
    if Max([1] cat Ni_facts) gt 10^8 then
        return false, Floor(1.32*prec);
    end if;
    return true, prec;
end function;

function IsValidLIXClassPolyGi(IgLIX,prec : PrecisionBase := 10, LatticeDimension := 0)
    deg := LatticeDimension eq 0 select Degree(IgLIX[1][1]) else LatticeDimension-1;
    RR := RealField(16);
    short := RR!prec/deg;
    for j in [2..#IgLIX] do
        Gj := IgLIX[j][1]; Nj := IgLIX[j][2];
        mj := RR!Log(PrecisionBase,Max([ Abs(RR!c) : c in Eltseq(Gj) ] cat [Nj])) + 8;
        if mj ge short then
            vprintf IgusaInvariant : "G%o coefficient size fails: %o > %o\n", j, mj, short;
            return false, Min(Ceiling((deg+1)*mj),Floor(1.414*prec));
        end if;
        vprintf IgusaInvariant : "G%o coefficient size passes: %o < %o\n", j, mj, short;
    end for;
    return true, prec;
end function;

//////////////////////////////////////////////////////////////////////////////

function TraceMatrix(H)
    n := Degree(H);
    R := BaseRing(Parent(H));
    P := PolynomialRing(R);
    K<a> := quo< P | P!H >;
    c := R!1;
    trace_seq := [ R!n ];
    for i in [1..2*n-2] do
        c *:= a;
        Append(~trace_seq,Trace(c));
    end for;
    return Matrix([ trace_seq[[i..i+n-1]] : i in [1..n] ]);
    // == return Matrix([ [ Trace(a^(i+j)) : i in [0..n-1] ] : j in [0..n-1] ]);
end function;

//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaClassPolynomial(
    DAB::[RngIntElt],p::RngIntElt,prec::RngIntElt : 
    Conductor := [],
    InvariantNumber := 1,
    RelationsDegree := 0,
    RepresentativeCurve := 0,
    UseDatabase := true) -> RngUPolElt
    {Returns the class polynomial for the absolute Igusa invariant i1 = I4*I6'/I10 (of Streng's thesis).}
    if p eq 0 then
        require false: "Analytic method not implemented for characteristic 0.";
        return IgusaClassPolynomial(DAB,prec : Conductor := Conductor, RelationsDegree := RelationsDegree);
    end if;
    K := QuarticCMField(DAB);
    h := ClassNumber(K);
    C := RepresentativeCurve;
    PZ := PolynomialRing(IntegerRing()); x := PZ.1;
    if Type(C) eq SeqEnum then
        if #C eq 5 and Type(Universe(C)) eq FldFin then
            C := HyperellipticCurveFromIgusaInvariants(C);
            return IgusaLIXInvariants(DAB,p,prec :
                Conductor := Conductor,
                RelationsDegree := RelationsDegree,
                RepresentativeCurve := C);
        end if;
        // C should be a sequence of curves or IgusaInvariants
        Curves := [];
        for X in C do
            error_msg := "Given \"RepresentativeCurve\" must be a sequence of curves or Igusa invariants defined over a finite field of given characteristic.";
            case ExtendedType(X):
            when SeqEnum[FldFinElt]:
                FF := Universe(X);
                require #X eq 5 : error_msg;
                Y := HyperellipticCurveFromIgusaInvariants(X);
            when Crv[FldFin]:
                FF := BaseField(X); Y := X;
            else
                require false : error_msg;
            end case;
            require Characteristic(FF) eq p : error_msg;
            psi := FrobeniusCharacteristicPolynomial(Y);
            deg := Degree(FF);
            require IsIrreducible(psi) :
                "Given RepresentativeCurve must have irreducible Frobenius charpoly.";
            L := NumberField(psi);
            require IsIsomorphic(K,L) :
                "Given RepresentativeCurve is not consistent with quartic invariants.";
            Append(~Curves,Y);
        end for;
    elif Type(C) eq CrvHyp then
        FF := BaseField(C);
        deg := Degree(FF);
        require Type(FF) eq FldFin and Characteristic(FF) eq p : 
            "Given RepresentativeCurve must be defined over a finite field of given characteristic.";
        psi := FrobeniusCharacteristicPolynomial(C);
        deg := Degree(BaseField(C));
        require IsIrreducible(psi) :
            "Given RepresentativeCurve must have irreducible Frobenius charpoly.";
        L := NumberField(psi);
        require IsIsomorphic(K,L) :
            "Given RepresentativeCurve is not consistent with quartic invariants.";
        Curves := [ C ];
    else
        weil, degs := QuarticCMFieldOrdinaryWeilNumbers(K,p);
        require #weil gt 0:
            "Argument 2 must admit ordinary reduction at argument 2.";
        char_polys := [ PZ | MinimalPolynomial(pi) : pi in weil ];
        chi := char_polys[1];
        deg := degs[1];
        DBG2 := Genus2CurvesDatabase();
        if chi in DBG2 then
            JJ_invs_seq := IgusaInvariantsSequences(DBG2,chi,[]);
            if #JJ_invs_seq gt 0 then
                JJ_invs := JJ_invs_seq[1];
            else
                JJ_invs := [];
            end if;
        else
            JJ_invs := [];
        end if;
        if #JJ_invs ne 0 then
            Curves := [ HyperellipticCurveFromIgusaInvariants(JJ) : JJ in JJ_invs ];
        else
            FF := FiniteField(p^deg);
            vprint IgusaInvariant : "Found minimal polynomials of Frobenius:";
            vprint IgusaInvariant : char_polys;
            vprint IgusaInvariant : "Conductor abelian invariants:";
            vprint IgusaInvariant : [ FrobeniusVerschiebungConductorAbelianInvariants(chi) : chi in char_polys ];
            repeat
                C := RandomHyperellipticCurveWithFrobeniusCharpoly(chi);
                vprint IgusaInvariant : "Found curve:";
                vprint IgusaInvariant : C;
                J := Jacobian(C);
                R, cond := EndomorphismRing(J);
                vprint IgusaInvariant : "Endomorphism ring conductor:", cond;
            until Conductor eq cond;
            Curves := [ C ];
        end if;
    end if;
    tyme := Cputime();
    Zp := pAdicQuotientRing(p,prec);
    Rp := UnramifiedExtension(Zp,deg);
    II_seq := [ ];
    for C in Curves do
        JJ := CanonicalLiftAbsoluteIgusaInvariants(C,prec : pAdicLiftingRing := Rp);
        vprint IgusaInvariant : "Canonical lifting time:", Cputime(tyme);
        j1, j2, j4 := Explode(JJ); j3 := 4*j4 + j2^2/j1;
        // j1 = J2^5/J10
        // j2 = J2^3*J4/J10
        // j3 = J2^2*J6/J10
        // 4*j4 = j3 - J2*J4^2/J10
        // j2*j3/j1 = J4*J6/J10
        case InvariantNumber:
        when 1:
            // Absolute Igusa-Clebsch invariants:
            // i1 = (J2^5 - 60*J2^3*J4 + 216*J2^2*J6 + 864*J2*J4^2 - 5184*J4*J6)/J10:
            //    =  j1   -   60*j2    +   216*j3    + 864*j2*(j2 -  6*j3)/j1;
            ii := j1 - 60*j2 + 216*j3 + 864*j2*(j2 - 6*j3)/j1;
        when 2:
            // Absolute Igusa-Clebsch invariants:
            // i2 = (J2^5 - 48*J2^3*J4 + 576*J2*J4^2)/J10,
            ii := j1 - 48*j2 + 576*(j3 - 4*j4);
        when 3:
            // Absolute Igusa-Clebsch invariants:
            // i3 = (J2^10 - 120*J2^8*J4 + 5760*J2^6*J4^2 - 138240*J2^4*J4^3 + 1658880*J2^2*J4^4 - 7962624*J4^5)/J10^2
            ii := j1^2 - 120*j1*j2 + 5760*j2^2 - 138240*j2*(j3 - 4*j4) + (1658880 - 7962624*j2/j1)*(j3 - 4*j4)^2;
        else
            require false: "Parameter \"InvariantNumber\" must be in {0,1,2}.";
        end case;
        Append(~II_seq,[ii]);
    end for;
    // Absolute Igusa invariants:
    e := QuarticCMFieldType(K) eq [4] select 1 else 2;
    deg := RelationsDegree gt 0 select RelationsDegree else e*h;
    vprint IgusaInvariant : "Searching for relations of degree:", deg;
    tyme := Cputime();
    RR := RealField(8);
    /* Use CommonAlgebraicRelations if more than one element of II_seq exists. */
    if #II_seq eq 1 then
        rels1 := AlgebraicRelations([ii],deg);
    else
        rels1 := CommonAlgebraicRelations([ II[1] : II in II_seq ],deg);
    end if;
    lens1 := [ &+[ (RR!c)^2 : c in Coefficients(H) ] : H in rels1[[1,2]] ];
    rgap1 := Sqrt(lens1[2]/lens1[1]);
    if #II_seq eq 1 then
        H1 := UnivariatePolynomial(rels1[1]);
    else
        H1 := rels1[1];
    end if;
    while Degree(H1) gt 1 and Coefficient(H1,0) eq 0 do
        H1 div:= Parent(H1).1;
    end while;
    if LeadingCoefficient(H1) lt 0 then H1 *:= -1; end if;
    vprint IgusaInvariant : "H1 relations time:", Cputime(tyme);
    vprint IgusaInvariant : "H1 relation gap:", rgap1;
    vprint IgusaInvariant : "H1:\n", H1;
    if rgap1 lt 128 then
        bool, new_prec := IsValidLIXClassPolyH1(H1,DAB,prec);
        if not bool then
            printf "***\n    Given precision %o was not sufficient!!!", prec;
            printf "...increasing to %o...\n***\n", new_prec;
            return IgusaClassPolynomial(DAB, p, new_prec :
                Conductor := Conductor,
                RepresentativeCurve := Curves,
                RelationsDegree := RelationsDegree);
        end if;
    end if;
    return H1;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////

function ContentReduction(H)
    PO := Parent(H); O := BaseRing(PO); F := NumberField(O);
    cffs := Coefficients(H);
    if Type(O) eq RngInt then
        s := GCD(cffs);
        return H div s, s;
    end if;
    prec := Max(GetKantPrecision(),Max([ Floor(Log(10,1+Abs(Norm(c)))) : c in cffs ]))+32;
    _, s := MinkowskiReduction(ideal< O | cffs > : Precision := prec);
    return PO!(s*PolynomialRing(Parent(s))!H), s;
end function;

function AbsoluteClassPolynomialFromRoots(roots,deg)
    RR := RealField(16);
    rels := CommonAlgebraicRelations(roots,deg);
    lens := [ &+[ (RR!c)^2 : c in Coefficients(H) ] : H in rels[[1,2]] ];
    return rels[1], Sqrt(lens[2]/lens[1]);
end function;

function AbsoluteLagrangeInterpolationFromRoots(H1,II_seq)
    prec := Precision(Universe(II_seq[1]));
    deg := Degree(H1);
    Gj_seq := [ ];
    pows_seq := [ [ II[1]^i : i in [0..deg-1] ] : II in II_seq ];
    RR := RealField(16);
    for j in [2..#II_seq[1]] do
        tyme := Cputime();
        if #II_seq eq 1 then
            N1 := Evaluate(Derivative(H1),II_seq[1][1]);
            rels := Basis(LinearRelations(pows_seq[1] cat [ N1*II_seq[1][j] ]));
        else
            Mj := &meet[ LinearRelations(pows_seq[i] cat
                [ Evaluate(Derivative(H1),II_seq[i][1]) * II_seq[i][j] ]) : i in [1..#II_seq] ];
            Bj := LLL(BasisMatrix(Mj));
            rels := [ Bj[i] : i in [1..Nrows(Bj)] ];
        end if;
        lens := [ &+[ (RR!c)^2 : c in Eltseq(v) ] : v in rels[[1,2]] ];
        rgap := Floor(Log(2,1+Sqrt(lens[2]/lens[1])));
        vj := rels[1];
        vprintf IgusaInvariant : "G%o relations time: %o\n", j, Cputime(tyme);
        vprintf IgusaInvariant : "G%o relation gap: %o bits\n", j, rgap;
        Gj := Polynomial(Eltseq(vj)[1..deg]);
        Nj := -vj[deg+1];
        if Nj lt 0 then
            Gj *:= -1; Nj *:= -1;
        end if;
        vprintf IgusaInvariant :  "G%o:\n%o\n", j, Gj;
        vprintf IgusaInvariant :  "N%o: %o\n", j, Nj;
        if rgap lt 16 then
            bool := false;
            new_prec := Floor(1.32*prec);
        elif rgap lt 256 then
            // this shouldn't be expensive but we can skip it if the relation gap is big
            bool, new_prec := IsValidLIXClassPolyNi(Nj,prec);
        else
            bool := true;
	    new_prec := prec;
        end if;
        if not bool then
            vprintf IgusaInvariant : "   N%o check failed.\n", j;
            return false, new_prec, 0;
        end if;
        Append(~Gj_seq,<Gj,Nj>);
    end for;
    return true, Gj_seq, rgap;
end function;

function GlobalFactors(H1,II_seq)
    prec := Precision(Universe(II_seq[1]));
    H1_fac := [ fac[1] : fac in Factorization(H1) ];
    if #H1_fac eq 1 then return [<H1,II_seq>]; end if;
    ret_fac_seq := [ ];
    for Hi in H1_fac do
        Ii_seq := [ II : II in II_seq | Valuation(Evaluate(Hi,II[1])) ge prec-16 ];
        assert #Ii_seq gt 0;
        Append(~ret_fac_seq,<Hi,Ii_seq>);
    end for;
    return ret_fac_seq;
end function;

function RelativeFactors(H1_1,II_seq,phi)
    Sp := Universe(II_seq[1]);
    Zp := BaseRing(Sp);
    prec := Precision(Sp);
    PO := Parent(H1_1);
    Or := BaseRing(PO);
    Fr := FieldOfFractions(Or);
    PF := PolynomialRing(Fr);
    H1_1_fac := [ fac[1] : fac in Factorization(PF!H1_1) ];
    if #H1_1_fac eq 1 then
        return [<H1_1,II_seq>];
    end if;
    ret_fac_seq := [ ];
    for Hi in H1_1_fac do
        mi := LCM([ Denominator(c) : c in Eltseq(Hi) ]);
        Hi_O := ContentReduction(PO!(mi*Hi));
        Hi_p := Polynomial([ Zp!phi(c) : c in Eltseq(Hi_O) ]);
        Ii_seq := [ II : II in II_seq | Valuation(Evaluate(Hi_p,II[1])) ge prec-16 ]; assert #Ii_seq gt 0;
        Append(~ret_fac_seq,<Hi_O,Ii_seq>);
    end for;
    return ret_fac_seq;
end function;

function RelativeClassPolynomialFromRoots(roots,phi)
    H1_1 := GaloisDescentAlgebraicRelation(roots,phi);
    H1_1 := ContentReduction(H1_1);
    return H1_1;
end function;

function RelativeLagrangeInterpolationFromRoots(H1_1,II_seq,phi : Al := "LagrangeTrace")
    // Al == 'TraceMatrix' or 'LagrangeTrace'
    // Solve for simultaneous solution for all invariants.
    /*
    This descriptions computation on the output of this function:
        Solve for:
            G_j^{(1)(i_1) = N_j^(1) H_1^{(1)}'(i_1) i_j
        then set
            N_j = N_j^{(1)} N_j^{(2)}, and
            G_j = G_j^{(1)} N_j^{(2)} H_1^{(2)} + G_j^{(2)} N_j^{(1)} H_1^{(1)}
        from which
            G_j(i_1) = G_j^{(1)}(i_1) N_j^{(2)} H_1^{(2)}(i_1)
                     = N_j^(1) N_j^{(2)} H_1^{(1)}'(i_1) H_1^{(2)}(i_1) i_j
                     = N_j H_1'(i_1).
        Then we may clear any common denominators from N_j and G_j.

        However, since N_j^{(1)} = N_j^{(2)}, we take N_j = N_j^{(i)}.
    */
    deg := Degree(H1_1);
    Sp := Universe(II_seq[1]);
    prec := Precision(Sp);
    p := ResidueCharacteristic(Sp);
    Rp := Codomain(phi); // assert degree Rp == 1
    RR := RealField(16);
    if Al eq "TraceMatrix" then
        Qp := pAdicField(p,prec);
        tyme := Cputime();
        H1_1_Qp := Polynomial([ Qp!phi(c) : c in Eltseq(H1_1) ]);
        A1 := TraceMatrix(H1_1_Qp);
        vprint IgusaInvariant : "Trace matrix time:", Cputime(tyme);
        tyme := Cputime();
        U1 := A1^-1; // coefficients in Q_p
        vprint IgusaInvariant : "Trace matrix inversion time:", Cputime(tyme);
        m1 := p^Max([ -Valuation(c) : c in Eltseq(U1) ]);
        U1 := MatrixAlgebra(Rp,Nrows(U1))!(m1 * U1);
        //
        V := RSpace(Sp,deg);
        num_aux := #II_seq[1]-1;
        vj_traces := [ V!0 : j in [1..num_aux] ];
        for II in II_seq do
            // Construct N1 = H1'(i1):
            i1 := II[1];
            N1 := phi(Coefficient(H1_1,1));
            i1_exp_i := 1;
            for i in [1..deg-1] do
                i1_exp_i *:= i1;
                N1 +:= phi(Coefficient(H1_1,i+1))*(i+1)*i1_exp_i;
            end for;
            //
            for j in [1..num_aux] do
                vj := [ N1*II[j+1] ];
                for i in [1..deg-1] do
                    Append(~vj,vj[i]*i1);
                end for;
                vj_traces[j] +:= V!vj;
            end for;
        end for;
        B0 := Basis(Domain(phi));
        B1 := [ phi(xi) : xi in B0 ];
        Gj_seq := [ ];
        for j in [1..num_aux] do
            // Gj:
            dj_int := [ ]; cj_1_int := [ ]; cj_2_int := [ ];
            rgap := Infinity();
            tyme := Cputime();
            vj_trace := vj_traces[j];
            for k in [1..deg] do
                ijk := 1;
                cjk := Trace(&+[ vj_traces[j][i] * U1[i,k]  : i in [1..deg] ]);
                Ljk := LinearRelations([-cjk] cat B1); vjk := Ljk.ijk;
                if vjk[1] eq 0 then
                    rgap := 0; break k;
                end if;
                lens := [ &+[ (RR!c)^2 : c in Eltseq(Ljk.i) ] : i in [1,2] ];
                rgap := Min(rgap,Floor(Log(2,1+Sqrt(lens[2]/lens[1]))));
                denjk, numjk_1, numjk_2 := Explode(Eltseq(vjk));
                numjk := GCD([m1,numjk_1,numjk_2]);
                numjk_1 div:= numjk;
                numjk_2 div:= numjk;
                denjk *:= (m1 div numjk);
                Append(~cj_1_int,numjk_1);
                Append(~cj_2_int,numjk_2);
                Append(~dj_int,denjk);
            end for;
            vprintf IgusaInvariant : "G%o relations time: %o\n", j+1, Cputime(tyme);
            vprintf IgusaInvariant : "G%o relation gap: %o bits\n", j+1, rgap;
            if rgap lt 16 then
                bool := false;
                new_prec := Floor(1.32*prec);
	    elif rgap lt 256 then
                Nj := LCM(dj_int);
                cj_1_int := [ cj_1_int[k] * (Nj div dj_int[k]) : k in [1..deg] ];
                cj_2_int := [ cj_2_int[k] * (Nj div dj_int[k]) : k in [1..deg] ];
                cj_1 := [ cj_1_int[k]*B0[1] + cj_2_int[k]*B0[2] : k in [1..deg] ];
                // cj_2 := [ Trace(c) - c : c in cj_1 ];
                Gj_1 := Polynomial(cj_1);
                vprintf IgusaInvariant :  "N%o: %o\n", j+1, Nj;
                bool, new_prec := IsValidLIXClassPolyNi(Nj,prec);
	    else
		bool := true;
		new_prec := prec;
            end if;
            if not bool then
                vprintf IgusaInvariant : "   N%o check failed.\n", j+1;
                return false, new_prec, 0;
            end if;
            Append(~Gj_seq,<Gj_1,Nj>);
        end for;
    else // Al eq "LagrangeTrace" then
        H1_1_seq := [ Rp | phi(c) : c in Eltseq(H1_1) ][[2..deg+1]];
        B0 := Basis(Domain(phi));
        B1 := [ phi(xi) : xi in B0 ];
        Gj_seq := [ ];
        m1 := 1;
	assert #II_seq[1] eq 3;
	// First analytically reconstruct the polynomial:
	tyme := Cputime();
	v2_exp_traces := [ 0 : i in [0..deg-1] ];
	v3_exp_traces := [ 0 : i in [0..deg-1] ];
	for II in II_seq do
	    i1, i2, i3 := Explode(II);
	    i1_k := Sp!1;
	    v2_exp_traces[1] +:= Trace(i2);
	    v3_exp_traces[1] +:= Trace(i3);
	    for k in [1..deg-1] do
		i1_k *:= i1;
		v2_exp_traces[k+1] +:= Trace(i2*i1_k);
		v3_exp_traces[k+1] +:= Trace(i3*i1_k);
	    end for;
	end for;
	ChangeUniverse(~v2_exp_traces,Rp);
	ChangeUniverse(~v3_exp_traces,Rp);
	G2_coeffs := [ &+[ H1_1_seq[deg-k+i]*v2_exp_traces[i+1] : i in [0..k] ] : k in [deg-1..0 by -1] ];
	G3_coeffs := [ &+[ H1_1_seq[deg-k+i]*v3_exp_traces[i+1] : i in [0..k] ] : k in [deg-1..0 by -1] ];
	vprint IgusaInvariant : "Analytic coefficients time:", Cputime(tyme);
	// Now algebraically reconstruct the polynomial:
	tyme := Cputime();
	rgap := Infinity();
	for j in [2,3] do
	    dj_int := [ ]; cj_1_int := [ ]; cj_2_int := [ ];
	    Gj_coeffs := j eq 2 select G2_coeffs else G3_coeffs;
	    for k in [1..deg] do
		cjk := Gj_coeffs[k];
		Ljk := LinearRelations([-cjk] cat B1); vjk := Ljk.1;
		if vjk[1] eq 0 then
		    rgap := 0; break k;
		end if;
		lens := [ &+[ (RR!c)^2 : c in Eltseq(Ljk.i) ] : i in [1,2] ];
		rgap := Min(rgap,Floor(Log(2,1+Sqrt(lens[2]/lens[1]))));
		denjk, numjk_1, numjk_2 := Explode(Eltseq(vjk));
		numjk := GCD([m1,numjk_1,numjk_2]);
		numjk_1 div:= numjk;
		numjk_2 div:= numjk;
		denjk *:= (m1 div numjk);
		Append(~cj_1_int,numjk_1);
		Append(~cj_2_int,numjk_2);
		Append(~dj_int,denjk);
	    end for;
	    vprintf IgusaInvariant : "G%o relation gap: %o bits\n", j, rgap;
	    vprintf IgusaInvariant : "G%o relations time: %o\n", j, Cputime(tyme);
            if rgap lt 16 then
                vprintf IgusaInvariant : "   N%o check failed.\n", j;
		return false, Floor(1.32*prec), 0;
	    end if;
	    Nj := LCM(dj_int);
            if rgap le 256 then
                vprintf IgusaInvariant :  "N%o: %o\n", j, Nj;
		bool, new_prec := IsValidLIXClassPolyNi(Nj,prec);
		if not bool then
		    vprintf IgusaInvariant : "   N%o check failed.\n", j;
		    return false, new_prec, 0;
		end if;
	    end if;
	    cj_1_int := [ cj_1_int[k] * (Nj div dj_int[k]) : k in [1..deg] ];
	    cj_2_int := [ cj_2_int[k] * (Nj div dj_int[k]) : k in [1..deg] ];
	    cj_1 := [ cj_1_int[k]*B0[1] + cj_2_int[k]*B0[2] : k in [1..deg] ];
	    Gj_1 := Polynomial(cj_1);
            Append(~Gj_seq,<Gj_1,Nj>);
        end for;
    end if;
    return true, Gj_seq, rgap;
end function;

function RealReflexFieldCompletion(K,Zp)
    // Requires p to be split in the real subfield of the reflex field.
    // Workaround a bug in V2.17-V2.18: pass in Zp rather than creating it here.
    p := ResidueCharacteristic(Zp); prec := Precision(Zp);
    Or := MaximalOrder(TotallyRealSubfield(QuarticCMReflexField(K)));
    ZZ := IntegerRing();
    pp := Decomposition(Or,p)[1][1];
    _, phi := Completion(Or,pp : Precision := prec+8);
    return hom< Or->Zp | [ Zp | ZZ!phi(x) : x in Basis(Or) ] >;
end function;

function RelativeToGlobalIgusaLIXInvariants(H1_1, Gi_1_seq)
    /*
        Given:
            G_j^{(1)(i_1) = N_j^(1) H_1^{(1)}'(i_1) i_j
        then set
            N_j = N_j^{(1)} N_j^{(2)}, and
            G_j = G_j^{(1)} N_j^{(2)} H_1^{(2)} + G_j^{(2)} N_j^{(1)} H_1^{(1)}
        from which
            G_j(i_1) = G_j^{(1)}(i_1) N_j^{(2)} H_1^{(2)}(i_1)
                     = N_j^(1) N_j^{(2)} H_1^{(1)}'(i_1) H_1^{(2)}(i_1) i_j
                     = N_j H_1'(i_1).
        Then we may clear any common denominators from N_j and G_j.

        Since N_j^{(1)} = N_j^{(2)}, we take N_j = N_j^{(i)}.
    */
    PZ := PolynomialRing(IntegerRing());
    H1_2 := Polynomial([ Trace(c) - c : c in Eltseq(H1_1) ]);
    H1 := PZ!(H1_1 * H1_2);
    N0 := GCD(Eltseq(H1));
    H1 div:= N0;
    IgLIX := [ <H1,1> ];
    for i in [1..#Gi_1_seq] do
        Gi_1 := Gi_1_seq[i][1]; Ni := Gi_1_seq[i][2];
        Gi_2 := Polynomial([ Trace(c) - c : c in Eltseq(Gi_1) ]);
        Gi := PZ!(Gi_1 * H1_2 + Gi_2 * H1_1);
        Ni_0 := GCD([N0] cat Eltseq(Gi));
        Gi div:= Ni_0; Ni *:= (N0 div Ni_0);
        Append(~IgLIX,<Gi,Ni>);
    end for;
    return IgLIX;
end function;

function RenormalizeIgusaLIXInvariantsChar2(IgLIX)
    /*
    This applies to the normalization of Igusa invariants used
    in the ECHIDNA database, for lifting from characteristic 2.
    */ 
    H1_tup, G2_tup, G3_tup := Explode(IgLIX);
    H1 := H1_tup[1];
    x := Parent(H1).1;
    G2 := G2_tup[1]; N2 := G2_tup[2];
    G3 := G3_tup[1]; N3 := G3_tup[2];
    H1 := Evaluate(H1,128*x);
    c1 := GCD(Eltseq(H1));
    H1 div:= c1;
    G2 := 64*Evaluate(G2,128*x);
    N2 *:= c1;
    c2 := GCD(Eltseq(G2) cat [N2]); 
    if c2 gt 1 then
        G2 div:= c2;
        N2 div:= c2;
    end if;
    G3 := 16*Evaluate(G3,128*x);
    N3 *:= c1;
    c3 := GCD(Eltseq(G3) cat [N3]); 
    if c3 gt 1 then
        G3 div:= c3;
        N3 div:= c3;
    end if;
    return [ <H1,1>, <G2,N2>, <G3,N3> ];
end function;

function shortJJtoII(JJ,p)
    // Given short JJ = [j1,j2,j4] output II = [i4,i2,i3],
    // the ECHIDNA IgusaLIX functions.
    j1, j2, j4 := Explode(JJ);
    j3 := 4*j4 + j2^2/j1;
    // Absolute Igusa-Clebsch invariants:
    if p eq 2 then
        // These need to be normalised to be 2-adically integral, then 
        // latter in in the code a change of variables made back to the
        // original normalisation.
        i1 := 8*j1;
        i2 := (j1 - 24*j2);          // N2 times 2
        i3 := (j1 - 20*j2 - 72*j3);  // N3 times 8
        i4 := i2*i3/j1;              // N1 times 128 
    else
        i1 := 8*j1;
        i2 := (j1 - 24*j2)/2;
        i3 := (j1 - 20*j2 - 72*j3)/8;
        i4 := i2*i3/i1;
    end if;
    return [i4,i2,i3];
end function;

function IItoJJ(II,pi)
    // Given II = [i4,i2,i3] output JJ = [J2,J4,J6,J8,J10]
    // = [1,j2/j1,j3/j1,j4/j1,1/j1], inverting the above
    // function for the ECHIDNA IgusaLIX invariants.
    // The reduction map pi to the residue field is then 
    // applied to the result. 
    Rp := Universe(II);  p := ResidueCharacteristic(Rp);
    i4, i2, i3 := Explode(II);
    if p eq 2 then
        j1 := (i2*i3) div i4;
        j2 := (j1 - i2)/3 div 8;
        j3 := (j1 - 20*j2 - i3)/9 div 8;
    else
        j1 := (i2*i3) div (8*i4);
        j2 := (j1 - 2*i2)/8 div 3;
        j3 := (j1 - 20*j2 - 8*i3)/8 div 9;
    end if;
    u1 := 1/j1;
    j4 := (j3 - j2^2*u1) div 4;
    J4 := pi(j2*u1); J8 := pi(j4*u1); J6 := 4*J8 + J4^2; J10 := pi(u1);
    return [ 1, J4, J6, J8, J10 ];
end function;

intrinsic IgusaLIXInvariants(DAB::[RngIntElt],p::RngIntElt,prec::RngIntElt :
    Conductor := [],
    RepresentativeCurve := 0,
    RelationsDegree := 0,
    GaloisConjugates := true,
    InterpolationAlgorithm := "LagrangeTrace",
    IgusaLIXDatabase := 0,
    WriteDatabase := false,
    UseCurvesDatabase := true,
    Verify := true) -> SetIndx
    {The Igusa LIX invariants computed by canonical lift from characteristic p.}
    if WriteDatabase then
        require Type(IgusaLIXDatabase) eq DBUser :
            "Parameter \"IgusaLIXDatabase\" must have type DBUser when \"WriteDatabase\" is true.";
    end if;
    if p eq 0 then
        return IgusaLIXInvariants(DAB,prec :
            Conductor := Conductor,
            GaloisConjugates := GaloisConjugates,
            RelationsDegree := RelationsDegree);
    end if;
    K := QuarticCMField(DAB);
    h := ClassNumber(K);
    e := QuarticCMFieldType(K) eq [4] select 1 else 2;
    C := RepresentativeCurve;
    PZ := PolynomialRing(IntegerRing()); x := PZ.1;
    if Type(C) eq SeqEnum then
        require #C gt 0 : "Parameter \"RepresentativeCurve\" must be a curve or nonempty sequence.";
        if #C eq 5 and Type(Universe(C)) eq FldFin then
            // Sequence was a 5-tuple of Igusa invariants:
            C := HyperellipticCurveFromIgusaInvariants(C);
            return IgusaLIXInvariants(DAB,p,prec :
                Conductor := Conductor,
                RepresentativeCurve := C,
                RelationsDegree := RelationsDegree,
                GaloisConjugates := GaloisConjugates,
                InterpolationAlgorithm := InterpolationAlgorithm,
                IgusaLIXDatabase := IgusaLIXDatabase,
                WriteDatabase := WriteDatabase,
                Verify := Verify);
        end if;
        // C should be a sequence of curves or IgusaInvariants
        Curves := [];
        for X in C do
            if Type(X) eq SeqEnum then
                FF := Universe(X);
                require #X eq 5 and Type(FF) eq FldFin and Characteristic(FF) eq p : 
                    "Given RepresentativeCurve must be a sequence of curves or Igusa invariants defined over a finite field of given characteristic.";
                Y := HyperellipticCurveFromIgusaInvariants(X);
                psi := FrobeniusCharacteristicPolynomial(Y);
            else
                FF := BaseField(X);
                require Type(FF) eq FldFin and Characteristic(FF) eq p : 
                    "Given RepresentativeCurve must be defined over a finite field of given characteristic.";
                Y := X;
            end if;
            psi := FrobeniusCharacteristicPolynomial(Y);
	    require IsIrreducible(psi) :
                "Given RepresentativeCurve must have irreducible Frobenius charpoly.";
            L := NumberField(psi);
            require IsIsomorphic(K,L) :
                "Given RepresentativeCurve is not consistent with quartic invariants.";
            Append(~Curves,Y);
        end for;
        deg := Degree(FF);
        if GaloisConjugates and RelationsDegree ne 0 then
	    if e eq 1 and Conductor ne [] then
		// For nontrinial Conductor the invariants might split over real subfield (e = 2).
		require RelationsDegree in { e*#Curves*deg : e in [1,2] } :
		    "Number of curves in \"RepresentativeCurve\" times degree (= " * Sprint(#Curves*deg) *
		    ") must equal 1/e (= 1/" * Sprint(e) *
		    ") of the \"RelationsDegree\" (= " * Sprint(RelationsDegree) * ").";
	    else
		require e*#Curves*deg eq RelationsDegree :
		    "Number of curves in \"RepresentativeCurve\" times degree (= " * Sprint(#Curves*deg) *
		    ") must equal 1/e (= 1/" * Sprint(e) *
		    ") of the \"RelationsDegree\" (= " * Sprint(RelationsDegree) * ").";
	    end if;
        end if;
    elif Type(C) eq CrvHyp then
        require not GaloisConjugates :
            "Parameter \"Galois conjugates\" true is incompatible with specification of a single \"RepresentativeCurve\".";
        FF := BaseField(C);
        deg := Degree(FF);
        require Type(FF) eq FldFin and Characteristic(FF) eq p : 
            "Given RepresentativeCurve must be defined over a finite field of given characteristic.";
        psi := FrobeniusCharacteristicPolynomial(C);
        require IsIrreducible(psi) :
            "Given RepresentativeCurve must have irreducible Frobenius charpoly.";
        L := NumberField(psi);
        require IsIsomorphic(K,L) :
            "Given RepresentativeCurve is not consistent with quartic invariants.";
        Curves := [ C ];
    elif UseCurvesDatabase then // Type(C) eq RngIntElt
        require UseCurvesDatabase :
            "Parameter \"UseCurvesDatabase\" must be true or \"RepresentativeCurve\"[s] provided when \"GaloisConjugates\" is true.";
        K := QuarticCMField(DAB);
        pi_seq, deg_seq := QuarticCMFieldOrdinaryWeilNumbers(K,p);
        chi_seq := [ PZ | MinimalPolynomial(pi) : pi in pi_seq ];
        require #chi_seq gt 0 : "Argument 2 must be a prime of ordinary reduction for argument 1.";
        chi := chi_seq[1];
        deg := deg_seq[1];
        DBG2 := Genus2CurvesDatabase();
        JJ_seq := IgusaInvariantsSequences(DBG2,chi,Conductor)[1];
        Curves := [ HyperellipticCurveFromIgusaInvariants(JJ_seq[i]) : i in [1..#JJ_seq by deg] ];
    else // Type(C) eq RngIntElt
        require not GaloisConjugates :
            "Parameter \"UseCurvesDatabase\" must be true or \"RepresentativeCurve\"[s] provided when \"GaloisConjugates\" is true.";
        weil, degs := QuarticCMFieldOrdinaryWeilNumbers(K,p);
        require #weil gt 0:
            "Argument 2 must admit ordinary reduction at argument 2.";
        char_polys := [ PZ | MinimalPolynomial(pi) : pi in weil ];
        chi := char_polys[1]; deg := degs[1];
        FF := FiniteField(p^deg);
        vprint IgusaInvariant : "Found minimal polynomials of Frobenius:";
        vprint IgusaInvariant : char_polys;
        vprint IgusaInvariant : "Conductor abelian invariants:";
        vprint IgusaInvariant : [ FrobeniusVerschiebungConductorAbelianInvariants(chi) : chi in char_polys ];
        repeat
            C := RandomHyperellipticCurveWithFrobeniusCharpoly(chi);
            vprint IgusaInvariant : "Found curve:", C;
            J := Jacobian(C);
            R, cond := EndomorphismRing(J);
            vprint IgusaInvariant : "Endomorphism ring conductor:", cond;
        until Conductor eq cond;
        Curves := [ C ];
    end if;
    tyme := Cputime();
    Zp := pAdicQuotientRing(p,prec);
    Rp := UnramifiedExtension(Zp,deg);
    II_seq := [ ];
    for C in Curves do
        JJ := CanonicalLiftAbsoluteIgusaInvariants(C,prec : pAdicLiftingRing := Rp);
        vprint IgusaInvariant : "Canonical lifting time:", Cputime(tyme);
        j1, j2, j4 := Explode(JJ);
        j3 := 4*j4 + j2^2/j1;
        // Absolute Igusa-Clebsch invariants:
        if p eq 2 then
            // These need to be normalised to be 2-adically integral, then
            // latter in in the code a change of variables made back to the
            // original normalisation.
            i1 := 8*j1;
            i2 := (j1 - 24*j2);          // N2 times 2
            i3 := (j1 - 20*j2 - 72*j3);  // N3 times 8
            i4 := i2*i3/j1;              // N1 times 128
        else
            i1 := 8*j1;
            i2 := (j1 - 24*j2)/2;
            i3 := (j1 - 20*j2 - 72*j3)/8;
            i4 := i2*i3/i1;
        end if;
        Append(~II_seq,[i4,i2,i3]);
    end for;
    // Absolute Igusa invariants:
    tyme := Cputime();
    RR := RealField(8);
    if GaloisConjugates then
        reldeg := #Curves * deg; // == RelationsDegree div 2 if nonzero.
        vprint IgusaInvariant : "Searching for relations of degree:", reldeg;
        if e eq 1 then
            phi := hom< IntegerRing()->Zp | >;
            H1 := PZ!RelativeClassPolynomialFromRoots([ II[1] : II in II_seq ],phi);
        elif e eq 2 then
            phi := RealReflexFieldCompletion(K,Zp);
            H1_1 := RelativeClassPolynomialFromRoots([ II[1] : II in II_seq ],phi);
            H1_2 := Parent(H1_1)![ Trace(c) - c : c in Eltseq(H1_1) ];
            H1 := PZ!(H1_1 * H1_2);
        else
            require false : "Argument 1 must be invariants of a cyclic or non-normal CM field.";
        end if;
        N0 := GCD(Eltseq(H1));
        H1 div:= N0;
        rgap1 := 0;
    else
        e := QuarticCMFieldType(K) eq [4] select 1 else 2;
        deg := RelationsDegree gt 0 select RelationsDegree else e*h;
        vprint IgusaInvariant : "Searching for relations of degree:", deg;
        H1, rgap1 := AbsoluteClassPolynomialFromRoots([ II[1] : II in II_seq ],deg);
    end if;
    llldeg := GaloisConjugates select 3 else Degree(H1);
    while Degree(H1) gt 1 and Coefficient(H1,0) eq 0 do
        H1 div:= Parent(H1).1;
    end while;
    if LeadingCoefficient(H1) lt 0 then H1 *:= -1; end if;
    vprint IgusaInvariant : "H1 relations time:", Cputime(tyme);
    if not GaloisConjugates then
        vprint IgusaInvariant : "H1 relation gap:", rgap1;
    end if;
    vprint IgusaInvariant : "H1:\n", H1;
    if rgap1 lt 128 then
        bool, new_prec := IsValidLIXClassPolyH1(H1,DAB,prec : LatticeDimension := llldeg);
        if not bool then
            vprintf IgusaInvariant : "***\n    Given precision %o was not sufficient!!!", prec;
            vprintf IgusaInvariant : "...increasing to %o...\n***\n", new_prec;
            return IgusaLIXInvariants(DAB, p, new_prec :
                Conductor := Conductor,
                RepresentativeCurve := Curves,
                RelationsDegree := RelationsDegree,
                GaloisConjugates := GaloisConjugates,
                InterpolationAlgorithm := InterpolationAlgorithm,
                IgusaLIXDatabase := IgusaLIXDatabase,
                WriteDatabase := WriteDatabase,
                UseCurvesDatabase := false,
                Verify := Verify);
        end if;
    end if;
    if GaloisConjugates and e eq 2 then
        IgLIX_set := {@ @};
        for Hi_tup in RelativeFactors(H1_1,II_seq,phi) do
            Hi_1 := Hi_tup[1]; Ii_seq := Hi_tup[2];
            if GetVerbose("IgusaInvariant") gt 0 then
                if Degree(H1) ne Degree(Hi_1)*e then
                    Hi_2 := Parent(Hi_1)![ Trace(c) - c : c in Eltseq(Hi_1) ];
                    Hi := PZ!(Hi_1 * Hi_2);
                    print "H1 (factor):";
                    print Hi;
                end if;
            end if;
            vprint IgusaInvariant : "Computing Lagrange interpolations for class polynomial of degree:", Degree(Hi_1);
            bool, Gi_seq, rgap := RelativeLagrangeInterpolationFromRoots(Hi_1,Ii_seq,phi : Al := InterpolationAlgorithm);
            if not bool then
                new_prec := Gi_seq;
                vprintf IgusaInvariant : "***\n    Given precision %o was not sufficient!!!", prec;
                vprintf IgusaInvariant : "...increasing to %o...\n***\n", new_prec;
                _, pi := ResidueClassField(Rp);
                IgLIXi := IgusaLIXInvariants(DAB, p, new_prec :
                    Conductor := Conductor,
                    GaloisConjugates := GaloisConjugates,
                    RepresentativeCurve := [ IItoJJ(II,pi) : II in Ii_seq ],
                    RelationsDegree := 2*Degree(Hi_1))[1];
                rgap := Infinity();
            else
                IgLIXi := RelativeToGlobalIgusaLIXInvariants(Hi_1, Gi_seq);
            end if;
            if p eq 2 then
                IgLIXi := RenormalizeIgusaLIXInvariantsChar2(IgLIXi);
            end if;
	    if LeadingCoefficient(IgLIXi[1][1]) lt 0 then
		for i in [1..3] do
		    IgLIXi[i][1] *:= -1;
		end for;
	    end if;
            // Verify consistency or increment precision and recompute.
            vprint IgusaInvariant : "Igusa invariants sequence:";
            vprint IgusaInvariant : IgLIXi;
            vprint IgusaInvariant : "Checking precision:", prec;
            // If the relations gap is sufficiently big then let it pass...
            if rgap ge 256 then
                bool := true;
            else
                vprint IgusaInvariant : "Checking auxilliary polynomial size.";
                bool, new_prec := IsValidLIXClassPolyGi(IgLIXi,prec : LatticeDimension := llldeg);
            end if;
            if not bool then
                _, pi := ResidueClassField(Rp);
                printf "***\n    Given precision %o was not sufficient!!!", prec;
                printf "...increasing to %o...\n***\n", new_prec;
                IgLIXi := IgusaLIXInvariants(DAB, p, new_prec :
                    Conductor := Conductor,
                    GaloisConjugates := GaloisConjugates,
                    RepresentativeCurve := [ IItoJJ(II,pi) : II in Ii_seq ],
                    RelationsDegree := 2*Degree(Hi_1))[1];
            end if;
            if Verify then
                vprint IgusaInvariant : "Checking specialization at a 32 bit prime.";
                tyme := Cputime();
                bool := IsConsistentIgusaLIXInvariantsRandomPrime(IgLIXi,DAB,32 : Conductor := Conductor);
                vprint IgusaInvariant : "Verification tyme:", Cputime(tyme);
            else
                bool := true;
            end if;
            if not bool then
                new_prec := Floor(1.414*prec);
                vprintf IgusaInvariant : "***\n    Given precision %o was not sufficient!!!", prec;
                vprintf IgusaInvariant : "...increasing to %o...\n***\n", new_prec;
                _, pi := ResidueClassField(Rp);
                IgLIXi := IgusaLIXInvariants(DAB, p, new_prec :
                    Conductor := Conductor,
                    GaloisConjugates := GaloisConjugates,
                    RepresentativeCurve := [ IItoJJ(II,pi) : II in Ii_seq ],
                    RelationsDegree := 2*Degree(Hi_1))[1];
            else
                vprint IgusaInvariant : "Found invariants:";
                vprint IgusaInvariant : IgLIXi;
            end if;
            if WriteDatabase then
                Write(IgusaLIXDatabase,DAB,IgLIXi);
            end if;
            Include(~IgLIX_set,IgLIXi);
        end for;
    else
        IgLIX_set := {@ @};
        for Hi_tup in GlobalFactors(H1,II_seq) do
            Hi := Hi_tup[1]; Ii_seq := Hi_tup[2];
            new_prec := prec;
            bool, Gi_seq, rgap := AbsoluteLagrangeInterpolationFromRoots(Hi,Ii_seq);
            if not bool then
                new_prec := Gi_seq;
                vprintf IgusaInvariant : "***\n    Given precision %o was not sufficient!!!", prec;
                vprintf IgusaInvariant : "...increasing to %o...\n***\n", new_prec;
                _, pi := ResidueClassField(Rp);
                IgLIXi := IgusaLIXInvariants(DAB, p, new_prec :
                    Conductor := Conductor,
                    GaloisConjugates := GaloisConjugates,
                    RepresentativeCurve := [ IItoJJ(II,pi) : II in Ii_seq ],
                    RelationsDegree := Degree(Hi))[1];
                rgap := Infinity();
            else
                IgLIXi := [ <Hi,1> ] cat Gi_seq;
            end if;
            if p eq 2 then
                IgLIXi := RenormalizeIgusaLIXInvariantsChar2(IgLIXi);
            end if;
            // Verify consistency or increment precision and recompute.
            vprint IgusaInvariant : "Igusa invariants sequence:";
            vprint IgusaInvariant : IgLIXi;
            vprint IgusaInvariant : "Checking precision:", prec;
            // If the relations gap is sufficiently big then let it pass...
            if rgap ge 256 then
                bool := true;
            else
                vprint IgusaInvariant : "Checking auxilliary polynomial size.";
                bool, new_prec := IsValidLIXClassPolyGi(IgLIXi,prec : LatticeDimension := llldeg);
            end if;
            if not bool then
                _, pi := ResidueClassField(Rp);
                printf "***\n    Given precision %o was not sufficient!!!", prec;
                printf "...increasing to %o...\n***\n", new_prec;
                IgLIXi := IgusaLIXInvariants(DAB, p, new_prec :
                    Conductor := Conductor,
                    GaloisConjugates := GaloisConjugates,
                    RepresentativeCurve := [ IItoJJ(II,pi) : II in Ii_seq ],
                    RelationsDegree := Degree(Hi))[1];
            end if;
            if Verify then
                vprint IgusaInvariant : "Checking specialization at a 32 bit prime.";
                tyme := Cputime();
                bool := IsConsistentIgusaLIXInvariantsRandomPrime(IgLIXi,DAB,32 : Conductor := Conductor);
                vprint IgusaInvariant : "Verification tyme:", Cputime(tyme);
            else
                bool := true;
            end if;
            if not bool then
                new_prec := Floor(1.414*prec);
                vprintf IgusaInvariant : "***\n    Given precision %o was not sufficient!!!", prec;
                vprintf IgusaInvariant : "...increasing to %o...\n***\n", new_prec;
                _, pi := ResidueClassField(Rp);
                IgLIXi := IgusaLIXInvariants(DAB, p, new_prec :
                    Conductor := Conductor,
                    GaloisConjugates := GaloisConjugates,
                    RepresentativeCurve := [ IItoJJ(II,pi) : II in Ii_seq ],
                    RelationsDegree := Degree(Hi))[1];
            else
                vprint IgusaInvariant : "Found invariants:";
                vprint IgusaInvariant : IgLIXi;
            end if;
            if WriteDatabase then
                Write(IgusaLIXDatabase,DAB,IgLIXi);
            end if;
            Include(~IgLIX_set,IgLIXi);
        end for;
    end if;
    return IgLIX_set;
end intrinsic;
