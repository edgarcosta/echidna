//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//         Copyright (C) 2010 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// 2007: First version
// 2010: Extension to use Galois conjugates

import "igusa_lix_verify.m":
    IsValidLIXClassPolyH1, IsValidLIXClassPolyNi, IsValidLIXClassPolyGi;
forward IgusaLIXInvariantsByConjugates;

//////////////////////////////////////////////////////////////////////////////

function TraceMatrix(H)
    n := Degree(H);
    QQ := RationalField();
    PQ := PolynomialRing(QQ);
    KK<a> := quo< PQ | PQ!H >;
    // return Matrix([ [ Trace(a^(i+j)) : i in [0..n-1] ] : j in [0..n-1] ]);
    trace_seq := [ QQ | n ];
    c := 1;
    for i in [1..2*n-2] do
        c *:= a;
	Append(~trace_seq,Trace(c));
    end for;
    return Matrix([ trace_seq[[i..i+n-1]] : i in [1..n] ]);
end function;

//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaLIXInvariants(I::RngOrdIdl,prec : 
    Al := "LagrangeTrace",
    Conductor := [],
    InvariantType := "Weng",
    ReflexField := false,
    RelationsDegree := 0,
    PolarizingElement := 1,
    PrecisionScalar := 2,
    SmoothnessCheck := true) -> SeqEnum
    {The Igusa LIX invariants of I computed by analytic means.}
    require Conductor eq [] : "Not implemented for orders of nontrivial conductors.";
    K := NumberField(Order(I));
    require IsCMField(K) and Degree(K) eq 4 :
        "Argument must be an ideal is a quartic CM field.";
    if QuarticCMFieldType(K) eq [2,2] then
        require Type(ReflexField) ne BoolElt :
            "A ReflexField must be specified for biquadratic fields.";
    end if;
    return IgusaLIXInvariants(K,prec :
        Al := Al,
        InvariantType := InvariantType,
        ReflexField := ReflexField,
        RelationsDegree := RelationsDegree,
        RepresentativeIdeal := I,
        PolarizingElement := PolarizingElement,
        PrecisionScalar := PrecisionScalar, 
        SmoothnessCheck := SmoothnessCheck);
end intrinsic;

intrinsic IgusaLIXInvariants(DAB::[RngIntElt],prec::RngIntElt :
    Al := "LagrangeTrace", 
    Conductor := [],
    InvariantType := "Weng",
    ReflexField := false,
    RelationsDegree := 0,
    PolarizingElement := 1,
    PrecisionScalar := 2,
    SmoothnessCheck := true) -> SeqEnum
    {The Igusa LIX invariants of I computed by analytic means.}
    require Conductor eq [] : "Not implemented for orders of nontrivial conductors.";
    K := QuarticCMField(DAB);
    if QuarticCMFieldType(K) eq [2,2] then
        require Type(ReflexField) ne BoolElt :
            "A ReflexField must be specified for biquadratic fields.";
        for Ki in QuarticCMReflexFields(K) do
            if IsIsomorphic(Ki,ReflexField) then
                ReflexField := Ki; break;
            end if;
        end for;
    end if;
    return IgusaLIXInvariants(K,prec :
        Al := Al,
        InvariantType := InvariantType,
        ReflexField := ReflexField,
        RelationsDegree := RelationsDegree,
        PolarizingElement := PolarizingElement,
        PrecisionScalar := PrecisionScalar, 
        SmoothnessCheck := SmoothnessCheck);
end intrinsic;

intrinsic IgusaLIXInvariants(K::FldNum,prec::RngIntElt :
    Al := "LagrangeTrace", 
    Conductor := [],
    InvariantType := "Weng",
    GaloisConjugates := true,
    PolarizingElement := 1,
    ReflexField := false,
    RelationsDegree := 0,
    RepresentativeIdeal := 0,
    PrecisionScalar := 2,
    SmoothnessCheck := true) -> SeqEnum
    {The Igusa LIX invariants computed by analytic means.}
    require Conductor eq [] :
        "Not implemented for orders of nontrivial conductors.";
    if QuarticCMFieldType(K) eq [2,2] then
        require Type(ReflexField) ne BoolElt :
            "A ReflexField must be specified for biquadratic fields.";
        require IsCoercible(K,ReflexField.1) :
            "ReflexField must be subfield of argument 1.";
    end if;
    if GaloisConjugates then
        require Conductor eq [] :
            "Galois conjugates algorithm not implemented for nontrivial conductor.";
        return IgusaLIXInvariantsByConjugates(K,prec :
            Al := Al,
            InvariantType := InvariantType,
            ReflexField := ReflexField,
            PrecisionScalar := PrecisionScalar,
            SmoothnessCheck := SmoothnessCheck);
    end if;
    DAB := QuarticCMFieldInvariants(K);
    h := ClassNumber(K);
    IK := RepresentativeIdeal;
    PZ := PolynomialRing(IntegerRing()); x := PZ.1;
    // Just go through the ideal classes and find one for which
    // the determinant of the imaginary lattice is maximal.
    if Type(IK) ne RngOrdIdl then
        OK := MaximalOrder(K);
        G, m := ClassGroup(OK);
        CC := ComplexField(128);
        RR := RealField(32);
        rr := RR!0;
        for g in G do
            JK := MinkowskiReduction(m(g));
            bool, xi, sqr_clss, neg_clss := IsPrincipallyPolarizable(JK : ReflexField := ReflexField);
            print "bool:", bool; // HERE
            if not bool then continue; end if;
            for ui in sqr_clss, vi in neg_clss do
                num_classes +:= 1;
                tau := SmallPeriodMatrix(JK,ui*vi*xi,CC : Reduction := true);
                ss := RR!Determinant(Matrix(2,[ Im(c) : c in Eltseq(tau) ]));
                vprintf IgusaInvariant : "det(Im(tau)): %o %o\n", ss, ss gt rr select "*" else "";
                if ss gt rr then
                    IK := JK;
                    rr := ss;
                    PolarizingElement := ui*vi*xi;
                end if;
            end for;
        end for;
    else
        e := QuarticCMFieldType(K) eq [4] select 1 else 2;
        num_classes := e*h;
    end if;
    tyme := Cputime();
    JJ := AbsoluteIgusaInvariants(IK,prec :
        PrecisionScalar := PrecisionScalar,
        PolarizingElement := PolarizingElement);
    //EE := RosenhainInvariants(IK, prec : PolarizingElement := PolarizingElement);
    vprint IgusaInvariant : "Analytic Igusa time:", Cputime(tyme);
    if &and[ Im(j) lt 0.1^20 : j in JJ ] then
        JJ := [ Real(j) : j in JJ ];
    end if;
    j1, j2, j3, j4 := Explode(JJ);
    // Absolute Igusa-Clebsch invariants:
    if InvariantType eq "Weng" then
        i1 := 8*j1;
        i2 := (j1 - 24*j2)/2;
        i3 := (j1 - 20*j2 - 72*j3)/8;
        i4 := i2*i3/i1;
    elif InvariantType eq "Streng" then
        u1 := j1^-1;
        i4 := u1*(j1 - 36*j2 + 216*j3)*(j1 - 24*j2)/256;
        i2 := u1*(j1 - 24*j2)^2/32;
        i3 := u1^3*(j1 - 24*j2)^5/16384;
    end if;
    // Absolute Igusa invariants:
    deg := RelationsDegree gt 0 select RelationsDegree else num_classes;
    vprint IgusaInvariant : "Searching for relations of degree:", deg;
    vprint IgusaInvariant : "...precision of Igusa invariant:", Precision(i4);
    tyme := Cputime();
    // We can't do this because Magma's built-in LinearRelation (singular)
    // does not return more than one relation!
    /*
    RR := RealField(8);
    rels1 := AlgebraicRelations([i4],deg)[[1,2]];
    lens1 := [ &+[ (RR!c)^2 : c in Coefficients(H) ] : H in rels1 ];
    H1 := UnivariatePolynomial(rels1[1]);
    */
    H1 := UnivariatePolynomial(AlgebraicRelations([i4],deg)[1]);
    while Degree(H1) gt 1 and Coefficient(H1,0) eq 0 do
        H1 div:= Parent(H1).1;
    end while;
    // rgap1 := Sqrt(lens1[2]/lens1[1]);
    rgap1 := 0;
    vprint IgusaInvariant : "H1 polynomial time:", Cputime(tyme);
    // vprint IgusaInvariant : "H1 relation gap:", rgap1;
    if Sign(LeadingCoefficient(H1)) lt 0 then H1 *:= -1; end if;
    N1 := Evaluate(Derivative(H1),i4);
    vprint IgusaInvariant : "H1:\n", H1;
    if rgap1 lt 128 then
        bool, new_prec := IsValidLIXClassPolyH1(H1,DAB,prec : SmoothnessCheck := SmoothnessCheck);
        // We'd like to catch instances where RelationsDegree is set to less
        // than num_classes but the subscheme does not split as expected, rather 
        // than increasing precision indefinitely.
        if not bool and deg lt num_classes and prec ge 6400 then
            vprint IgusaInvariant : "Checking whether the relative degree is really:", 2*deg;
            RR := RealField(8);
            H1_test := UnivariatePolynomial(AlgebraicRelations([i4],2*deg)[1]);
            if Sign(LeadingCoefficient(H1_test)) lt 0 then H1_test *:= -1; end if;
            if IsValidLIXClassPolyH1(H1_test,DAB,prec : SmoothnessCheck := SmoothnessCheck) then
                // RelationsDegree must have been set to something too low, fix:
                assert RelationsDegree eq deg;
                RelationsDegree *:= 2; deg *:= 2;
                bool := true;
                H1 := H1_test;
                N1 := Evaluate(Derivative(H1),i4);
                vprint IgusaInvariant : "    Given RelationsDegree was too low! resetting to:", deg;
                vprint IgusaInvariant : "H1 polynomial time:", Cputime(tyme);
                vprint IgusaInvariant : "H1:\n", H1;
            end if;
        end if;
        if not bool then
            printf "***\n    Given precision %o was not sufficient!!!", prec;
            printf "...increasing to %o...\n***\n", new_prec;
            return IgusaLIXInvariants(K, new_prec :
                Al := Al,
                GaloisConjugates := GaloisConjugates,
                InvariantType := InvariantType,
                ReflexField := ReflexField,
                RepresentativeIdeal := IK,
                PolarizingElement := PolarizingElement,
                RelationsDegree := RelationsDegree,
                SmoothnessCheck := SmoothnessCheck);
        end if;
    end if;
    d1 := Degree(H1);
    Pows4 := [ i4^i : i in [0..d1-1] ];
    tyme := Cputime();
    // We can't do this because Magma's built-in LinearRelation (singular)
    // does not return more than one relation!
    /*
    rels := Basis(LinearRelations(Pows4 cat [ N1*i2 ]))[[1,2]];
    lens := [ &+[ (RR!c)^2 : c in Eltseq(v) ] : v in rels ];
    rgap := Floor(Log(2,1+Sqrt(lens[2]/lens[1])));
    v_G2 := rels[1];
    */
    v_G2 := Basis(LinearRelations(Pows4 cat [ N1*i2 ]))[1];
    vprint IgusaInvariant : "G2 relations time:", Cputime(tyme);
    // vprintf IgusaInvariant : "G2 relation gap: %o bits\n", rgap;
    G2 := Polynomial(Eltseq(v_G2)[1..d1]);
    N2 := -v_G2[d1+1];
    if N2 lt 0 then G2 *:= -1; N2 *:= -1; end if;
    vprint IgusaInvariant :  "G2:\n", G2;
    vprint IgusaInvariant :  "N2:", N2;
    /*
    if rgap lt 16 then
        bool := false;
        new_prec := Floor(1.32*prec);
    elif rgap lt 256 then
        // this shouldn't be expensive but we can skip it if the relation gap is big
        bool, new_prec := IsValidLIXClassPolyNi(N2,prec);
    else
        bool := true;
    end if;
    */
    bool, new_prec := IsValidLIXClassPolyNi(N2,prec);
    if not bool then
        vprint IgusaInvariant : "   N2 check failed.";
        printf "***\n    Given precision %o was not sufficient!!!", prec;
        printf "...increasing to %o...\n***\n", new_prec;
        return IgusaLIXInvariants(K, new_prec :
            Al := Al,
            GaloisConjugates := GaloisConjugates,
            InvariantType := InvariantType,
            ReflexField := ReflexField,
            RepresentativeIdeal := IK,
            PolarizingElement := PolarizingElement,
            RelationsDegree := RelationsDegree,
            SmoothnessCheck := SmoothnessCheck);
    end if;
    tyme := Cputime();
    v_G3 := Basis(LinearRelations(Pows4 cat [ N1*i3 ]))[1];
    vprint IgusaInvariant : "G3 relations time:", Cputime(tyme);
    // vprintf IgusaInvariant : "G3 relation gap: %o bits\n", rgap;
    G3 := Polynomial(Eltseq(v_G3)[1..d1]);
    N3 := -v_G3[d1+1];
    if N3 lt 0 then G3 *:= -1; N3 *:= -1; end if;
    vprint IgusaInvariant :  "G3:\n", G3;
    vprint IgusaInvariant :  "N3:", N3;
    bool, new_prec := IsValidLIXClassPolyNi(N3,prec);
    if not bool then
        vprint IgusaInvariant : "   N3 check failed.";
        printf "***\n    Given precision %o was not sufficient!!!", prec;
        printf "...increasing to %o...\n***\n", new_prec;
        return IgusaLIXInvariants(K, new_prec :
            Al := Al,
            GaloisConjugates := GaloisConjugates,
            InvariantType := InvariantType,
            ReflexField := ReflexField,
            RepresentativeIdeal := IK,
            PolarizingElement := PolarizingElement,
            RelationsDegree := RelationsDegree,
            SmoothnessCheck := SmoothnessCheck);
    end if;
    IgLIX := [ <H1,1>, <G2,N2>, <G3,N3> ];
    vprint IgusaInvariant : "Checking precision:", prec;
    bool, new_prec := IsValidLIXClassPolyGi(IgLIX,prec);
    if bool then
        vprint IgusaInvariant : "   ...coefficient check satisfied.";
        bool := IsConsistentIgusaLIXInvariantsRandomPrime(IgLIX,DAB,32 : ReflexField := ReflexField);
        new_prec := Floor(1.32*prec);
    elif new_prec lt 1.32 * prec then
        vprint IgusaInvariant :
            "   ...coefficient check nearly satisfied, seeking further verification.";
        bool := &and [ IsConsistentIgusaLIXInvariantsRandomPrime(IgLIX,DAB,32 : ReflexField := ReflexField) : i in [1..2] ];
    end if;
    if bool then
        vprint IgusaInvariant : "Found invariants:";
        vprint IgusaInvariant : IgLIX;
        return IgLIX;
    else
        printf "***\n    Given precision %o was not sufficient!!!", prec;
        printf "...increasing to %o...\n***\n", new_prec;
        return IgusaLIXInvariants(K, new_prec :
            Al := Al,
            GaloisConjugates := GaloisConjugates,
            InvariantType := InvariantType,
            ReflexField := ReflexField,
            RepresentativeIdeal := IK,
            PolarizingElement := PolarizingElement,
            RelationsDegree := RelationsDegree,
            SmoothnessCheck := SmoothnessCheck);
    end if;
end intrinsic;

function HasReflexFieldDiscriminant(IK,xi,D1)
    tau := SmallPeriodMatrix(IK,xi,ComplexField() : Reduction := true);
    tr := func< x | Trace(x) div 2 >;
    ZE := Center(EndomorphismRing(tau));
    mat := Matrix(2,[ tr(x*(tr(y)-y)) : x, y in Basis(ZE) ]);
    if D1 eq -Determinant(mat) then
        return true;
    else
        return false;
    end if;
end function;

function IgusaLIXInvariantsByConjugates(K,prec :
    Al := "LagrangeTrace",
    InvariantType := "Weng",
    ReflexField := false,
    PrecisionScalar := 2,
    SmoothnessCheck := true)
    vprint IgusaInvariant : "Computing analytic invariants to precision:", prec;
    DAB := QuarticCMFieldInvariants(K);
    if QuarticCMFieldType(K) eq [2,2] then
        assert Type(ReflexField) ne BoolElt;
        assert IsCoercible(K,ReflexField.1);
    end if;
    OK := MaximalOrder(K);
    if QuarticCMFieldType(K) eq [2,2] and false then
        print "!!!HERE considering only CM types for reflex field!!!";
        K1 := ReflexField;
        G, m1 := ClassGroup(K1);
        II := Parent(ideal< OK | 1 >);
        m := map< G->II | g :-> ideal< OK | m1(g) > >;
    else
        G, m := ClassGroup(OK);
    end if;
    JJ_seq := [ ];
    total_tyme := Cputime();
    CC := ComplexField(prec);
    extra := Floor(3.0/8*prec);
    for g in G do
        IK := MinkowskiReduction(m(g));
        bool, xi, units, minus_units := IsPrincipallyPolarizable(IK : ReflexField := ReflexField);
        vprint IgusaInvariant : "Polarizable ideal:", bool;
        if QuarticCMFieldType(K) eq [2,2] then
            // Check if the reflex field is correct:
            // The period matrix is computed inside
            // the call to absolute Igusa invariants.
            // Here we need to restrict to the units
            // and minus_units such that xi*u*v has
            // the right reflex field. 
            DE := Discriminant(ReflexField);
            unit_classes := [ u*v : u in units, v in minus_units |
                HasReflexFieldDiscriminant(IK,u*v*xi,DE) ];
        elif QuarticCMFieldType(K) eq [4] then
            unit_classes := [ 1 ];
        else
            unit_classes := [ u*v : u in units, v in minus_units ];
        end if;
        if bool then
            for u in unit_classes do
                tyme := Cputime();
                JJ := AbsoluteIgusaInvariants(IK,prec+extra :
                    PolarizingElement := xi*u,
                    PrecisionScalar := PrecisionScalar,
                    UseReducedRepresentative := false);
                printf "Reducing precision from %o to %o.\n", Precision(Universe(JJ)), prec;
                Append(~JJ_seq,ChangeUniverse(JJ,CC));
                vprint IgusaInvariant : "Analytic Igusa time:", Cputime(tyme);
            end for;
        end if;
    end for;
    vprint IgusaInvariant : "Total analytic Igusa time:", Cputime(total_tyme);
    d1 := #JJ_seq;
    if d1 eq 0 then return {@ @}; end if;
    II_seq := [ ];
    for JJ in JJ_seq do
        j1, j2, j3, j4 := Explode(JJ);
        // Absolute Igusa-Clebsch invariants:
        if InvariantType eq "Weng" then
            i1 := 8*j1;
            i2 := (j1 - 24*j2)/2;
            i3 := (j1 - 20*j2 - 72*j3)/8;
            i4 := i2*i3/i1;
        elif InvariantType eq "Streng" then
            u1 := j1^-1;
            i4 := u1*(j1 - 36*j2 + 216*j3)*(j1 - 24*j2)/256;
            i2 := u1*(j1 - 24*j2)^2/32;
            i3 := u1^3*(j1 - 24*j2)^5/16384;
        end if;
        Append(~II_seq,[i4,i2,i3]);
    end for;
    // CC<i> := Universe(II_seq[1]);
    // print "II:";
    // print [i1,i2,i3,i4];
    // Absolute Igusa invariants:
    // Should include the map phi: S -> RR of the totally real subring S of OK:
    /*
    S0 := TotallyRealSubring(OK);
    RR := RealField(Universe(II_seq[1]));
    r0 := Roots(PolynomialRing(RR)!MinimalPolynomial(S0![0,1]))[1][1];
    phi := hom< S0->RR | 1, r0 >;
    H1 := GaloisDescentAlgebraicRelation([ II_seq[i][1] : i in [1..#II_seq] ],phi);
    */
    try
        H1 := GaloisDescentAlgebraicRelation([ II_seq[i][1] : i in [1..#II_seq] ]);
    catch e
        new_prec := Floor(Sqrt(2)*prec);
        printf "***\n    Given precision %o was not sufficient for H1 construction!", prec;
        printf "...increasing to %o...\n***\n", new_prec;
        return IgusaLIXInvariantsByConjugates(K, new_prec :
            Al := Al,
            InvariantType := InvariantType,
            ReflexField := ReflexField,
            PrecisionScalar := PrecisionScalar,
            SmoothnessCheck := SmoothnessCheck);
    end try;
    vprint IgusaInvariant : "H1 polynomial time:", Cputime(tyme);
    if Sign(LeadingCoefficient(H1)) lt 0 then H1 *:= -1; end if;
    if IsIrreducible(H1) then
        vprint IgusaInvariant : "H1:\n", H1;
        bool, new_prec := IsValidLIXClassPolyH1(H1,DAB,prec :
            SmoothnessCheck := SmoothnessCheck, LatticeDimension := 2);
    else
        facs := [ fac[1] : fac in Factorization(H1) ];
        vprintf IgusaInvariant : "Found %o H1 factors:\n", #facs;
        for H1_i in facs do 
            vprint IgusaInvariant : "H1:\n", H1_i;
            bool, new_prec := IsValidLIXClassPolyH1(H1_i,DAB,prec :
                SmoothnessCheck := SmoothnessCheck, LatticeDimension := 2);
            if not bool then break; end if;
        end for;
    end if;
    if not bool then
        printf "***\n    Given precision %o was not sufficient!!!", prec;
        printf "...increasing to %o...\n***\n", new_prec;
        return IgusaLIXInvariantsByConjugates(K, new_prec :
            Al := Al,
            InvariantType := InvariantType,
            ReflexField := ReflexField,
            PrecisionScalar := PrecisionScalar,
            SmoothnessCheck := SmoothnessCheck);
    end if;
    // Solve for simultaneous solution for all invariants.
    if Al eq "TraceMatrix" then
        tyme := Cputime();
        A1 := TraceMatrix(H1);
        vprint IgusaInvariant : "Trace matrix time:", Cputime(tyme);
        tyme := Cputime();
        U1 := A1^-1; // coefficients in QQ
        vprint IgusaInvariant : "Trace matrix inversion time:", Cputime(tyme);
        //
        V := RSpace(Parent(i4),d1);
        v2_trace := V!0;
        v3_trace := V!0;
        for i in [1..#II_seq] do
            i4, i2, i3 := Explode(II_seq[i]);
            N1 := Evaluate(Derivative(H1),i4);
            v2 := [ N1*i2 ];
            v3 := [ N1*i3 ];
            for i in [1..d1-1] do
                Append(~v2,v2[i]*i4);
                Append(~v3,v3[i]*i4);
            end for;
            v2_trace +:= V!v2;
            v3_trace +:= V!v3;
        end for;
        // Check that the imaginary parts of v2_trace anv v3_trace are < epsilon?
        RR := RealField(prec);
        eps := 1/RealField(8)!10^(Max((prec div 2)-16,8));
        // G2:
        c2 := [ &+[ Real(v2_trace[i]) * U1[i,j] : i in [1..d1] ] : j in [1..d1] ];
        c2_int := [ ]; d2_int := [ ];
        tyme := Cputime();
        for i in [1..d1] do
            r2 := RationalApproximation(c2[i],eps : Al := "LLL");
            Append(~c2_int,Numerator(r2));
            Append(~d2_int,Denominator(r2));
        end for;
        vprint IgusaInvariant : "G2 relations time:", Cputime(tyme);
        N2 := LCM(d2_int);
        c2_int := [ c2_int[i] * (N2 div d2_int[i]) : i in [1..d1] ];
        G2 := Polynomial(c2_int);
        vprint IgusaInvariant :  "G2:\n", G2;
        vprint IgusaInvariant :  "N2:", N2;
        // G3:
        c3 := [ &+[ Real(v3_trace[i]) * U1[i,j] : i in [1..d1] ] : j in [1..d1] ];
        c3_int := [ ]; d3_int := [ ];
        tyme := Cputime();
        for i in [1..d1] do
            r3 := RationalApproximation(c3[i],eps : Al := "LLL");
            Append(~c3_int,Numerator(r3));
            Append(~d3_int,Denominator(r3));
        end for;
        vprint IgusaInvariant : "G3 relations time:", Cputime(tyme);
        N3 := LCM(d3_int);
        c3_int := [ c3_int[i] * (N3 div d3_int[i]) : i in [1..d1] ];
        G3 := Polynomial(c3_int);
        vprint IgusaInvariant :  "G3:\n", G3;
        vprint IgusaInvariant :  "N3:", N3;
        IgLIX := [ <H1,1>, <G2,N2>, <G3,N3> ];
    else // Al eq "LagrangeTrace"
        H1_seq := Eltseq(H1)[[2..d1+1]];
        Gj_seq := [ ];
        // First analytically reconstruct the polynomial:
        tyme := Cputime();
        V := RSpace(Parent(i4),d1);
        v2_trace := V!0;
        v3_trace := V!0;
        for II in II_seq do
            i4, i2, i3 := Explode(II);
            v2 := [ i2 ];
            v3 := [ i3 ];
            for k in [1..d1-1] do
                Append(~v2,v2[k]*i4);
                Append(~v3,v3[k]*i4);
            end for;
            v2_trace +:= V!v2;
            v3_trace +:= V!v3;
        end for;
        RR := RealField(prec);
        eps := 1/RealField(8)!10^(Max((prec div 2)-16,8));
        if not &and[ Abs(Im(c)) lt eps : c in Eltseq(v2_trace) ] then
            print "Errors v2:", [ Abs(Im(c)) : c in Eltseq(v2_trace) ];
            print "Errors v3:", [ Abs(Im(c)) : c in Eltseq(v3_trace) ];
            assert &and[ Abs(Im(c)) lt eps : c in Eltseq(v2_trace) ];
        elif not &and[ Abs(Im(c)) lt eps : c in Eltseq(v3_trace) ] then
            print "Errors v2:", [ Abs(Im(c)) : c in Eltseq(v2_trace) ];
            print "Errors v3:", [ Abs(Im(c)) : c in Eltseq(v3_trace) ];
            assert &and[ Abs(Im(c)) lt eps : c in Eltseq(v3_trace) ];
        end if;
        //
        VR := RSpace(RR,d1);
        v2_trace := VR![ Re(c) : c in Eltseq(v2_trace) ];
        v3_trace := VR![ Re(c) : c in Eltseq(v3_trace) ];
        // G2:
        G2_coeffs := [ &+[ H1_seq[d1-k+i]*v2_trace[i+1] : i in [0..k] ] : k in [d1-1..0 by -1] ];
        G3_coeffs := [ &+[ H1_seq[d1-k+i]*v3_trace[i+1] : i in [0..k] ] : k in [d1-1..0 by -1] ];
        vprint IgusaInvariant : "Analytic coefficients time:", Cputime(tyme);
        // Now algebraically reconstruct the polynomial:
        for j in [2,3] do
            tyme := Cputime();
            rgap := Infinity();
            dj_int := [ ]; cj_int := [ ];
            Gj_coeffs := j eq 2 select G2_coeffs else G3_coeffs;
            for k in [1..d1] do
                cjk := Gj_coeffs[k];
                rjk := RationalApproximation(cjk,eps : Al := "LLL");
                Append(~cj_int,Numerator(rjk));
                Append(~dj_int,Denominator(rjk));
                if rjk eq 0 then
		    rgap := 0; break k;
		else
		    hght := Max([ Abs(cj_int[k]), Abs(dj_int[k]) ]);
		    rgap := Min(rgap,Floor(prec-Log(10,hght)));
                end if;
            end for;
            if rgap lt 16 then
                bool := false;
                new_prec := Floor(1.32*prec);
                vprint IgusaInvariant : "Failed relations gap check:", rgap;
		return IgusaLIXInvariantsByConjugates(K, new_prec :
                    Al := Al,
                    InvariantType := InvariantType,
                    ReflexField := ReflexField,
                    PrecisionScalar := PrecisionScalar,
                    SmoothnessCheck := SmoothnessCheck);
            else
                Nj := LCM(dj_int);
                cj_int := [ cj_int[i] * (Nj div dj_int[i]) : i in [1..d1] ];
                Gj := Polynomial(cj_int);
                vprint IgusaInvariant :  "Gj:\n", Gj;
                vprint IgusaInvariant :  "Nj:", Nj;
                vprintf IgusaInvariant : "G%o relation gap: %o bits\n", j, rgap;
                vprintf IgusaInvariant : "G%o relations time: %o\n", j, Cputime(tyme);
                bool, new_prec := IsValidLIXClassPolyNi(Nj,prec);
            end if;
            if not bool then
                vprintf IgusaInvariant : "   N%o check failed.\n", j;
		return IgusaLIXInvariantsByConjugates(K, new_prec :
                    Al := Al,
                    InvariantType := InvariantType,
                    ReflexField := ReflexField,
                    PrecisionScalar := PrecisionScalar,
                    SmoothnessCheck := SmoothnessCheck);
            end if;
            Append(~Gj_seq,<Gj,Nj>);
        end for;
        IgLIX := [<H1,1>] cat Gj_seq;
    end if;
    print "Checking precision:", prec;
    bool, new_prec := IsValidLIXClassPolyGi(IgLIX,prec : LatticeDimension := 2);
    IgLIX_dcmp := IgusaLIXDecomposition(IgLIX);
    if bool then
        vprint IgusaInvariant : "   ...coefficient check satisfied.";
        for IgLIX in IgLIX_dcmp do
            bool := IsConsistentIgusaLIXInvariantsRandomPrime(IgLIX,DAB,32 : ReflexField := ReflexField);
            new_prec := Floor(1.32*prec);
            if not bool then break; end if;
        end for;
    elif new_prec lt 1.32 * prec then
        vprint IgusaInvariant :
            "   ...coefficient check nearly satisfied, seeking further verification.";
        for IgLIX in IgLIX_dcmp do
            for i in [1..2] do
                bool := IsConsistentIgusaLIXInvariantsRandomPrime(IgLIX,DAB,32 : ReflexField := ReflexField);
                if not bool then break; end if;
            end for;
            if not bool then break; end if;
        end for;
    end if;
    if bool then
        vprint IgusaInvariant : "Found invariants:";
        vprint IgusaInvariant : IgLIX_dcmp;
        return IgLIX_dcmp;
    else
        printf "***\n    Given precision %o was not sufficient!!!", prec;
        printf "...increasing to %o...\n***\n", new_prec;
        return IgusaLIXInvariantsByConjugates(K, new_prec :
            Al := Al,
            InvariantType := InvariantType,
            ReflexField := ReflexField,
            PrecisionScalar := PrecisionScalar,
            SmoothnessCheck := SmoothnessCheck);
    end if;
end function;

