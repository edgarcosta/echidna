//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
EXAMPLES:

FF := FiniteField(101);

// Ex. 1
jj := [ FF | 57, 26, 41, 60, 63, 58, 95, 60, 57, 14 ];
C := HyperellipticCurveFromAbsoluteIgusaInvariants(jj);
tassert jj eq AbsoluteIgusaInvariants(C);
chi := FrobeniusCharacteristicPolynomial(C);

for i in [1..#JJ] do
    printf "i = %2o:";
    Ci := HyperellipticCurveFromAbsoluteIgusaInvariants(JJ[i]);
    Ji := Jacobian(Ci);
    Ri, ind_i := EndomorphismRing(Ji);
    print ind_i;
end for;

// Ex. 2
jj := [ FF | 5, 57, 6, 36, 28, 89, 37, 4, 13, 81 ]

*/

function AbsoluteIgusaToIsogenousInvariantsAVI(jj,ell)
    assert #jj eq 10;
    C := HyperellipticCurveFromAbsoluteIgusaInvariants(jj);
    return [ AbsoluteIgusaInvariants(t[2]) : t in RationallyIsogenousCurvesG2(C,ell) ];
end function;

function CanonicalLiftRosenhainInvariantsOverSplittingField(C,prec)
    tt := Level2ThetaCurveCoefficientsOverSplittingField(C);
    xx := AffineLevel2ThetaNullPointFromLevel2ThetaCurveCoefficients(tt);
    XX := CanonicalLiftAffineLevel2ThetaNullPoint(xx,prec+16);
    // Take the lifting ring, and create a non-quotient ring which
    // has a well-defined field of fractions:
    S1 := ChangePrecision(Universe(XX),prec);
    RR := pAdicRing(2,prec+16);
    SS := UnramifiedExtension(RR,Degree(S1));
    XX := [ SS!Eltseq(xi) : xi in XX ];
    AA := Level2ThetaNullPointFromAffineLevel2ThetaNullPoint(XX);
    return Level2ThetaNullPointToRosenhainInvariants(AA);
end function;

intrinsic AbsoluteIgusaInvariantIsogenyAdjacencyMatrix(
    jj::SeqEnum[FldElt],p::RngIntElt : Depth := 0) -> AlgMatElt, SeqEnum
    {The adjaceny matrix of (p,p)-isogenous Jacobian varieties to jj,
    followed by the indexed set }

    FF := Universe(jj);
    q := Characteristic(FF);
    require p ne q or (p eq 2 and Type(FF) eq FldFin):
        "Universe of argument 1 must not have characteristic p.";
    jj_set := {@ jj @};
    i := 1;
    Gr := [ ];
    r := 0;
    n := #jj_set;
    while i le #jj_set do
        for ji in AbsoluteIgusaToIsogenousInvariants(jj_set[i],p) do
            j := Index(jj_set,ji);
            if j ne 0 then
                Append(~Gr,[i,j]);
            else
                Include(~jj_set,ji);
                Append(~Gr,[i,#jj_set]);
            end if;
        end for;
        if i eq n then
            r +:= 1;
            if Depth*(r - Depth) gt 0 then
                break;
            end if;
            n := #jj_set;
        end if;
        i +:= 1;
    end while;
    A := MatrixAlgebra(Integers(),n)!0;
    for ij in Gr do
        if ij[2] le n then
            A[ij[1],ij[2]] +:= 1;
        end if;
    end for;
    if n lt #jj_set then
        jj_set := jj_set[[1..n]];
    end if;
    return A, jj_set;
end intrinsic;

intrinsic IgusaInvariantIsogenyAdjacencyMatrix(
    JJ::SeqEnum[FldElt],p::RngIntElt : Depth := 0) -> AlgMatElt, SeqEnum
    {The adjaceny matrix of (p,p)-isogenous Jacobian varieties to JJ,
    followed by the indexed set.}
    //require p in {2,3} : "Argument 2 must in 2 or 3.";
    require p eq 2 or p ne Characteristic(Universe(JJ)) :
        "Argument 2 must be 2 or different from the characteristic of argument 1.";
    JJ_set := {@ IgusaToNormalizedIgusaInvariants(JJ) @};
    i := 1;
    Gr := [ ];
    r := 0;
    n := #JJ_set;
    while i le #JJ_set do
        for Ji in IgusaToIsogenousInvariants(JJ_set[i],p : Normalize := true) do
            j := Index(JJ_set,Ji);
            if j ne 0 then
                Append(~Gr,[i,j]);
            else
                Include(~JJ_set,Ji);
                Append(~Gr,[i,#JJ_set]);
            end if;
        end for;
        if i eq n then
            r +:= 1;
            if Depth*(r - Depth) gt 0 then
                break;
            end if;
            n := #JJ_set;
        end if;
        i +:= 1;
    end while;
    A := MatrixAlgebra(Integers(),n)!0;
    for ij in Gr do
        if ij[2] le n then
            A[ij[1],ij[2]] +:= 1;
        end if;
    end for;
    if n lt #JJ_set then
        JJ_set := JJ_set[[1..n]];
    end if;
    return A, JJ_set;
end intrinsic;

intrinsic IgusaToIsogenousInvariantsOverSplittingField(
    JJ::SeqEnum[FldFinElt],p::RngIntElt : Normalize := false) -> SeqEnum
    {The sequence of Igusa invariants of Jacobians (p,p)-isogenous
    to the given abelian variety invariants, where p = 2 or 3.}

    FF := Universe(JJ);
    q := Characteristic(FF);
    //require p in {2,3} : "Argument 2 must be 2 or 3.";
    require p ne q or (p eq 2 and Type(FF) eq FldFin):
        "Universe of argument 1 must not have characteristic p.";
    return IgusaToIsogenousInvariants(JJ,p : ExtensionDegree := 0);
end intrinsic;

intrinsic AbsoluteIgusaToIsogenousInvariantsOverSplittingField(
    jj::SeqEnum[FldFinElt],p::RngIntElt) -> SeqEnum
    {The sequence of absolute Igusa invariants of Jacobians (p,p)-isogenous
    to the given abelian variety invariants, where p = 2 or 3.}

    FF := Universe(jj);
    q := Characteristic(FF);
    require p ne q or (p eq 2 and Type(FF) eq FldFin):
        "Universe of argument 1 must not have characteristic p.";
    return AbsoluteIgusaToIsogenousInvariants(jj,p : ExtensionDegree := 0);
end intrinsic;

intrinsic IgusaToIsogenousInvariants(
    JJ::SeqEnum[FldElt],p::RngIntElt :
    ExtensionDegree := 1, Normalize := true) -> SeqEnum
    {The sequence of Igusa invariants of Jacobians (p,p)-isogenous
    to the given abelian variety invariants, where p = 2 or 3.
    If ExtensionDegree is set greater than 1, then an extension of this
    degree is allowed (when the first argument is defined over a
    finite field).}

    FF := Universe(JJ);
    q := Characteristic(FF);
    require p ne q or (p eq 2 and Type(FF) eq FldFin):
        "Universe of argument 1 must not have characteristic p.";
    require ExtensionDegree eq 1 or Type(FF) eq FldFin :
        "Argument 1 must be defined over a finite field if ExtensionDegree > 1.";
    jj := IgusaToAbsoluteIgusaInvariants(JJ);
    jj_seq := AbsoluteIgusaToIsogenousInvariants(jj,p : ExtensionDegree := ExtensionDegree);
    return [ AbsoluteIgusaToNormalizedIgusaInvariants(ji) : ji in jj_seq ];
end intrinsic;

intrinsic AbsoluteIgusaToIsogenousInvariants( jj::SeqEnum[FldElt],p::RngIntElt :
    ExtensionDegree := 1, Algorithm := "") -> SeqEnum
    {The sequence of absolute Igusa invariants of Jacobians (p,p)-isogenous
    to the given abelian variety invariants, where p = 2 or 3.
    If ExtensionDegree is set greater than 1, then an extension of this
    degree is allowed (when the first argument is defined over a
    finite field).}

    FF := Universe(jj);
    q := Characteristic(FF);
    require p ne q or (p eq 2 and Type(FF) eq FldFin):
        "Universe of argument 1 must not have characteristic p.";
    require ExtensionDegree eq 1 or Type(FF) eq FldFin :
        "Argument 1 must be defined over a finite field if ExtensionDegree > 1.";
    C := HyperellipticCurveFromAbsoluteIgusaInvariants(jj);
    if p eq 2 and q eq 2 then
        prec := 96;
        ee := CanonicalLiftRosenhainInvariantsOverSplittingField(C,prec);
        LL := Universe(ee);
        O := RingOfIntegers(LL);
        R := quo< O | 2^prec >;
        _, pi := ResidueClassField(R);
        IsogenousIgusaInvariants := [];
        for ei in ModularRichelotRepresentatives(ee) do
            ji := RosenhainToRichelotAbsoluteIgusaInvariants(ei);
            Append(~IsogenousIgusaInvariants, [ pi(j) : j in ji ]);
        end for;
    elif Algorithm eq "AVI" or p gt 3 then
        if ExtensionDegree eq 1 then
	    KK := FF; LL := FF;
	else
            KK := FiniteField(#FF^ExtensionDegree);
	    LL := Universe(jj);
	    jj := ChangeUniverse(jj,KK);
        end if;
        IsogenousIgusaInvariants := AbsoluteIgusaToIsogenousInvariantsAVI(jj,p);
    elif p eq 2 then
        ee := RosenhainInvariantsOverSplittingField(C);
        LL := Universe(ee);
        IsogenousIgusaInvariants := [ ];
        for ei in ModularRichelotRepresentatives(ee) do
            try
		jj := RosenhainToRichelotAbsoluteIgusaInvariants(ei);
                Append(~IsogenousIgusaInvariants,jj);
            catch e
                print "Isogenous Igusa invariants are degenerate."; // e`Object;
            end try;
	end for;
    elif p eq 3 and q eq 2 then
        tt := Level2ThetaCurveCoefficientsOverSplittingField(C);
        xx := AffineLevel2ThetaNullPointFromLevel2ThetaCurveCoefficients(tt);
        KK := Universe(xx);
        AA := AffineSpace(KK,3);
        yy := [ AA.i : i in [1..3] ];
        XX := Scheme(AA,AffineLevel2ThetaNullCorrespondenceRelations(xx,yy,3));
        comps := [ ReducedSubscheme(Y) : Y in IrreducibleComponents(XX) ];
        deg := LCM([ IntegerRing() | Degree(Y) : Y in comps ]);
        if deg eq 1 then
            LL := KK;
        else
            LL := FiniteField(q,Degree(KK) * deg);
            comps := [ BaseExtend(Y,LL) : Y in comps ];
        end if;
        S := [ ];
        for Y in comps do
            S cat:= [ Eltseq(P) : P in RationalPoints(Y) ];
        end for;
        IsogenousLevel2ThetaCurveCoefficients := [
            AffineLevel2ThetaNullPointToLevel2ThetaCurveCoefficients(Eltseq(P)) : P in S ];
        IsogenousIgusaInvariants := [
            AbsoluteIgusaInvariants(
            HyperellipticCurveFromLevel2ThetaCurveCoefficients(tt)) : tt in IsogenousLevel2ThetaCurveCoefficients ];
    elif p eq 3 then // q ne 2, 3
        ee := RosenhainInvariantsOverSplittingField(C);
        ss := Level2ThetaNullPointFromRosenhainInvariantsOverSplittingField(ee);
        tt := Level4ThetaNullPointFromLevel2ThetaNullPointOverSplittingField(ss);
        LL := Universe(tt);
        MM := ThetaNullSpace(LL,2,4,2);
        XX := ThetaNullCorrespondenceSpace(MM,p);
        pi_1 := map< XX->MM | ProjectionMorphism(XX,1)[2] : Check := false >;
        pi_2 := map< XX->MM | ProjectionMorphism(XX,2)[2] : Check := false >;
        P := MM(LL)!tt;
        S := RationalPoints(pi_2(P@@pi_1));
        IsogenousLevel2Points := [
            Level4ThetaNullPointToLevel2ThetaNullPoint(Eltseq(ti)) : ti in S ];
        IsogenousRosenhainPoints := [
            Level2ThetaNullPointToRosenhainInvariants(si) : si in IsogenousLevel2Points ];
        IsogenousIgusaInvariants := [
            RosenhainToAbsoluteIgusaInvariants(ei) : ei in IsogenousRosenhainPoints ];
    end if;
    if ExtensionDegree eq 0 then
        return IsogenousIgusaInvariants;
    elif ExtensionDegree eq 1 then
        KK := FF;
    else
        require Type(FF) eq FldFin :
            "Argument 1 must be defined over a finite field if ExtensionDegree > 1.";
        KK := FiniteField(q,GCD(Degree(LL), Degree(FF) * ExtensionDegree));
    end if;
    jseq := [ Parent([ KK | ]) | ];
    for jj_ext in IsogenousIgusaInvariants do
        bool, jj := CanChangeUniverse(jj_ext,KK);
        if bool then
            Append(~jseq,jj);
        end if;
    end for;
    //vprintf IgusaInvariant, 2 : "Found %o Igusa invariants.", #jseq;
    return jseq;
end intrinsic;

