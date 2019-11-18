//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        Copyright (C) 2014 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function StrengToIgusaInvariants(jj)
    // Streng uses the triple of invariants jj = [j1,j2,j3] 
    // = [I4*psi6/I10,I2*I4^2/I10,I4^5/I10^2] where psi6=(I2I4-3I6)/2)
    //require #jj eq 3 : "Argument 1 must be a sequence of 3 Streng invariants.";
    j1, j2, j3 := Explode(jj);
    /*
    // These are the [i4,i2,i3] used by Weng
    i4 := (j2-2*j1)/3; // I4I6/I10 
    i2 := j2^3/j3;     // I2^3I4/I10
    i3 := i4*i2/j2;    // I2^2I6/I10
    // Now we write down the Igusa invariants from the Weng invariants.
    JJ := [
        1,
        (-16*i4 + i3)/(24*i3),
        (80*i4*i2 - 384*i4*i3 + i2*i3)/(432*i2*i3),
        (-768*i4^2*i2 + 416*i4*i2*i3 - 1536*i4*i3^2 + i2*i3^2)/(6912*i2*i3^2),
        8*i4/(i2*i3)
    ];
    // Composing these two transformations, and
    // projectively renormalizing, we obtain:
    [
        j2,
        (j2^2 - 16*j3)/24,
        (256*j1*j3 + j2^3 - 48*j2*j3)/432,
        (1024*j1*j2*j3 + j2^4 - 96*j2^2*j3 - 768*j3^2)/6912,
        8*j3^2
        ];
    */
    return [
        1,
        (j2^2 - 16*j3)/(24*j2^2),
        (256*j1*j3 + j2^3 - 48*j2*j3)/(432*j2^3),
        (1024*j1*j2*j3 + j2^4 - 96*j2^2*j3 - 768*j3^2)/(6912*j2^4),
        8*j3^2/j2^5
        ];
    /*
    For completeness we give the inverse transform here.
    [
        (J2^2 - 24*J4)*(J2^3 - 36*J2*J4 + 216*J6)/(2^8*J10), // j1
        J2*(J2^2 - 24*J4)^2/(2^5*J10), // j2
        (J2^2 - 24*J4)^5/(2^7*J10)^2 // j3
    ];
    */
end function;

function WengToIgusaInvariants(ii)
    // Weng uses the triple of invariants ii = [i4,i2,i3] 
    // = [I4*I6/I10,I2*I4^2/I10,I4^5/I10^2].
    i4, i2, i3 := Explode(ii);
    // Now we write down the Igusa invariants from the Weng invariants.
    return [
        1,
        (-16*i4 + i3)/(24*i3),
        (80*i4*i2 - 384*i4*i3 + i2*i3)/(432*i2*i3),
        (-768*i4^2*i2 + 416*i4*i2*i3 - 1536*i4*i3^2 + i2*i3^2)/(6912*i2*i3^2),
        8*i4/(i2*i3) ];
    /*
    For completeness we state the inverse transformation:
    [ 
        (J2^5 - 44*J2^3*J4 - 72*J2^2*J6 + 480*J2*J4^2 + 1728*J4*J6)/(2^7*J10), // i4
        J2^3*(J2^2 - 24*J4)/(2*J10), // i2
        J2^2*(J2^3 - 20*J2*J4 - 72*J6)/(8*J10) // i3
    ]
    */
end function;

function HenselLiftingField(FF,prec)
    p := Characteristic(FF); 
    r := Degree(FF);
    R := pAdicField(p,prec);
    return UnramifiedExtension(R,r);
end function;

function HenselLiftingPrecision(IgCMH,p)
    H1 := IgCMH[1][1];
    H1_conj := Polynomial([ Trace(c)-c : c in Eltseq(H1) ]);
    H1_abs := PolynomialRing(IntegerRing())!(H1*H1_conj);
    H1_abs div:= GCD(Eltseq(H1_abs));
    n1 := &+[ Valuation(c,p) : c in Eltseq(H1_abs) ];
    n2 := Valuation(IgCMH[2][2],p);
    n3 := Valuation(IgCMH[3][2],p);
    d1 := Degree(H1);
    k1 := Valuation(LeadingCoefficient(H1_abs),p);
    k2 := Valuation(Coefficient(H1_abs,0),p);
    v1 := 1; 
    m1 := 4;
    repeat
        m1 := Max(Ceiling(Log(2,v1)),m1+1);
        S1 := pAdicQuotientRing(p,2^m1);
        P1 := PolynomialRing(S1);
        v1 := Valuation(S1!Discriminant(P1!H1_abs)) + k1*d1;
    until v1 lt 2^m1;
    return Max([ v1+1, n1 , n2, n3 ]) + Max(64 div p,8);
end function;

function IgusaValuationNormalization(JJ)
    p := UniformizingElement(Universe(JJ));
    n := Max([ Floor(-Valuation(JJ[i])/i) : i in [1..5] ]);
    return n eq 0 select JJ else [ p^(n*i)*JJ[i] : i in [1..5] ];
end function;

function IgusaCMHToAbsoluteInvariantsOverLiftingField(IgCMH,FF :
    LiftingPrecision := 0, InvariantType := 2)
    p := Characteristic(FF);
    m := LiftingPrecision eq 0 select HenselLiftingPrecision(IgCMH,p) else LiftingPrecision;
    vprint IgusaInvariant : "Lifting to precision..", m;
    S := HenselLiftingField(FF,m);
    Fr := BaseRing(Parent(IgCMH[1][1]));
    if Type(Fr) in {FldRat,RngInt} then
        bool := true; w := 0;
        to_S := func< c, sgn | S!c >;
        auts := [1];
    else
        D := Discriminant(Fr);
        d := SquareFree(D);
        bool, w := IsSquare(S!d);
        to_S := func< c, sgn | cc[1] + sgn*cc[2]*w where cc := Eltseq(c) >;
        auts := [1,-1];
    end if;
    if not bool then return []; end if; 
    PS<x> := PolynomialRing(S);
    jj_seq := [ ];
    for sgn in auts do
        H1 := IgCMH[1][1]; N1 := IgCMH[1][2];
        G2 := IgCMH[2][1]; N2 := IgCMH[2][2];
        G3 := IgCMH[3][1]; N3 := IgCMH[3][2];
        //assert IgCMH[1][2] eq IntegerRing()!LeadingCoefficient(H1);
        H1 := PS![ to_S(c,sgn) : c in Eltseq(H1) ];
        G2 := PS![ to_S(c,sgn) : c in Eltseq(G2) ];
        G3 := PS![ to_S(c,sgn) : c in Eltseq(G3) ];
        dxH1 := Derivative(H1);
        // Caution: This selects only the ORDINARY Igusa invariants when p in {2,3}.
        H1_roots := [ r[1] : r in Roots(PS!H1) ];
        vprint IgusaInvariant, 2 : "Found roots of H1 with valuations:", [ Valuation(r) : r in H1_roots ];
        if p eq 2 then
            if InvariantType eq 1 then
                jj_1 := [ r : r in H1_roots | Valuation(r) eq -7 ];
            elif InvariantType eq 2 then
                jj_1 := [ r : r in H1_roots | Valuation(r) eq -8 ];
            end if;
        elif p eq 3 then
            jj_1 := [ r : r in H1_roots | Valuation(r) ge 0 ];
        else
            jj_1 := H1_roots;
        end if;
        jj_seq cat:= [
            [ j1,
            N1 * Evaluate(G2,j1)/(Evaluate(dxH1,j1) * N2),
            N1 * Evaluate(G3,j1)/(Evaluate(dxH1,j1) * N3) ] : j1 in jj_1 ];
    end for;
    return jj_seq;
end function;

intrinsic IgusaCMHToIgusaInvariants(IgCMH::SeqEnum,FF::Fld :
    ExactDegree := false, LiftingPrecision := 0, InvariantType := 2) -> SeqEnum
    {}
    // Treat special case (DAB = [5,5,5]):
    if Eltseq(IgCMH[1][1]) eq [0,1] and IgCMH[2][1] eq 0 and IgCMH[3][1] eq 0 then
        if Characteristic(FF) in {2,5} then
            return [ Parent([ FF | ]) | ];
        else
            return [ [ FF | 0, 0, 0, 0, 800000 ] ];
        end if;
    end if;
    //assert IgCMH[1][2] eq IntegerRing()!LeadingCoefficient(IgCMH[1][1]);
    N1 := IgCMH[1][2];
    N2 := IgCMH[2][2];
    N3 := IgCMH[3][2];
    P := PolynomialRing(FF);
    p := Characteristic(FF);
    if p ne 0 and (p in {2,3} or FF!N1 eq 0 or FF!N2 eq 0 or FF!N3 eq 0) then
        JJ_seq := [ Parent([ FF | ]) | ];
        jj_seq := IgusaCMHToAbsoluteInvariantsOverLiftingField(IgCMH,FF :
            LiftingPrecision := LiftingPrecision,
            InvariantType := InvariantType);
        vprintf IgusaInvariant, 2 : "Found %o lifted roots\n", #jj_seq;
        if #jj_seq eq 0 then return JJ_seq; end if;
	SS := RingOfIntegers(Universe(jj_seq[1]));
        KK, m := ResidueClassField(SS);
        for jj_lift in jj_seq do
            if InvariantType eq 1 then
                JJ_lift := WengToIgusaInvariants(jj_lift);
            elif InvariantType eq 2 then
                JJ_lift := AbsoluteStrengToIgusaInvariants(jj_lift);
            end if;
            JJ_lift := IgusaValuationNormalization(JJ_lift);
            vprint IgusaInvariant, 2 : "JJ vals:", [ Valuation(Ji) : Ji in JJ_lift ];
            if Valuation(JJ_lift[5]) ne 0 then continue; end if;
            if &or[ Valuation(Ji) lt 0 : Ji in JJ_lift ] then continue; end if;
            JJ := [ FF!m(SS!Ji) : Ji in JJ_lift ];
            if ExactDegree then
                deg := LCM([ Degree(MinimalPolynomial(Ji)) : Ji in JJ ]);
                if Degree(FF) ne deg then continue; end if;
            end if;
            Append(~JJ_seq,JJ);
        end for;
    else
        Fr := BaseRing(Parent(IgCMH[1][1]));
        if Type(Fr) in {FldRat,RngInt} then
            bool := true; w := 0;
            to_FF := func< c, sgn | FF!c >;
            auts := [1];
        else
            D := Discriminant(Fr);
            d := SquareFree(D);
            auts := [1,-1];
            bool, w := IsSquare(FF!d);
            to_FF := func< c, sgn | cc[1] + sgn*cc[2]*w where cc := Eltseq(c) >;
        end if;
        if not bool then return []; end if;
        JJ_seq := [ Parent([ FF | ]) | ];
        for sgn in auts do
            H1 := Polynomial([ to_FF(c,sgn) : c in Eltseq(IgCMH[1][1]) ]);
            rt_1 := Roots(P!H1);
            if #rt_1 eq 0 then continue; end if;
            jj_1 := [ r[1] : r in rt_1 | r[2] eq 1 ];
            G2 := Polynomial([ to_FF(c,sgn) : c in Eltseq(IgCMH[2][1]) ]);
            G3 := Polynomial([ to_FF(c,sgn) : c in Eltseq(IgCMH[3][1]) ]);
            dxH1 := Derivative(H1);
            jj_seq := [
                [ j1,
                N1 * Evaluate(G2,j1)/(Evaluate(dxH1,j1) * N2),
                N1 * Evaluate(G3,j1)/(Evaluate(dxH1,j1) * N3) ] : j1 in jj_1 ];
            if (InvariantType eq 1 and &or[ jj[2] eq 0 or jj[3] eq 0 : jj in jj_seq ]) or 
                (InvariantType eq 2 and &or[ jj[2] eq 0 : jj in jj_seq ]) then
                jj_lift_seq := IgusaCMHToAbsoluteInvariantsOverLiftingField(IgCMH,FF :
                    LiftingPrecision := LiftingPrecision,
                    InvariantType := InvariantType);
                vprintf IgusaInvariant, 2 : "Found %o lifted roots\n", #jj_seq;
                if #jj_lift_seq eq 0 then continue; end if;
                SS := RingOfIntegers(Universe(jj_lift_seq[1]));
                KK, m := ResidueClassField(SS);
                for jj_lift in jj_lift_seq do
                    if &or[ Valuation(j) lt 0 : j in jj_lift ] then continue; end if;
                    if InvariantType eq 1 then
                        JJ_lift := WengToIgusaInvariants(jj_lift);
                    elif InvariantType eq 2 then
                        JJ_lift := AbsoluteStrengToIgusaInvariants(jj_lift);
                    end if;
                    JJ_lift := IgusaValuationNormalization(JJ_lift);
                    if Valuation(JJ_lift[5]) ne 0 then continue; end if;
                    if &or[ Valuation(Ji) lt 0 : Ji in JJ_lift ] then continue; end if;
                    JJ := [ FF!m(SS!Ji) : Ji in JJ_lift ];
                    if JJ[5] eq 0 then continue; end if;
                    if Type(FF) in {FldFin,FldQuad,FldCyc,FldNum} and ExactDegree then
                        deg := LCM([ Degree(MinimalPolynomial(Ji)) : Ji in JJ ]);
                        if Degree(FF) ne deg then continue; end if;
                    end if;
                    Append(~JJ_seq,JJ);
                end for;
            else
                for jj in jj_seq do
                    if InvariantType eq 1 then
                        JJ := WengToIgusaInvariants(jj);
                    elif InvariantType eq 2 then
                        JJ := AbsoluteStrengToIgusaInvariants(jj);
                    end if;
                    if JJ[5] eq 0 then continue; end if;
                    if Type(FF) in {FldFin,FldQuad,FldCyc,FldNum} and ExactDegree then
                        deg := LCM([ Degree(MinimalPolynomial(Ji)) : Ji in JJ ]);
                        if Degree(FF) ne deg then continue; end if;
                    end if;
                    Append(~JJ_seq,JJ);
                end for;
            end if;
        end for;
    end if;
    return JJ_seq;
end intrinsic;

