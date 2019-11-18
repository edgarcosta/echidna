//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare verbose IgusaInvariant, 2;

/*
Example:
> DAB := [ 5, 7, 11 ];
> IgLIX := IgusaLIXInvariants(DBIX,DAB);
> FF := FiniteField(37);
> IgusaLIXToIgusaInvariants(IgLIX[1],FF);
[
    [ 1, 11, 34, 6, 32 ],
    [ 0, 2, 26, 36, 20 ]
]
> JJ_1 := $1[1];
> // There are two more invariants over an extension (of p-rank 0):
> KK<t> := FiniteField(37,2);
> IgusaLIXToIgusaInvariants(IgLIX[1],KK : ExactDegree);
[
    [ 1, t^667, t^1161, t^1260, t^656 ],
    [ 1, t^55, t^549, t^108, t^1016 ]
]
> // Note that there are additional Igusa invariants over the prime field
> // with the same endomorphism algebra but non-maximal endomorphism ring.
> JJ_2 := [ FF | 1, 26, 13, 10, 11 ];
*/

/*

Annegret Weng uses the triple of invariants
$$
(i1,i2,i3) = (I4*I6/I10,I2^3*I4/I10,I2^2*I6/I10).
$$
The more naturally definition of i1 is I2^5/I10 with i4 = I4*I6/I10 (with
the conventions for absolute Igusa invariants), but we use the above
definition of i1 in this document.

Thomas Houtmann provided the following intrinsic for conversion from the
invariants of Weng (used in defining Igusa LIX polynomials) to Igusa-Clebsch.

function WengToIgusaClebschInvariants(ii)
    // {Converts the j-invariants ii used by A. Weng into Igusa-Clebsch invariants.}
    I2 := 1;
    I10 := ii[1]/(ii[2]*ii[3]);
    I4 := ii[2]*I10; // /I2^3;
    I6 := ii[3]*I10; // /I2^2;
    return [ I2, I4, I6, I10 ];
end function;

Concisely, we have:

*/

function WengToIgusaClebschInvariants(ii)
    return [1,i1/i3,i1/i2,i1/(i2*i3)] where i1, i2, i3 := Explode(ii);
end function;

/*

Converting from Igusa-Clebsch to Igusa invariants, we obtain:

*/

function WengToIgusaInvariants(ii)
    // Weng uses the triple of invariants ii = [i4,i2,i3], where
    //       xx = [I4*I6/I10,I2^3*I4/I10,I2^2*I6/I10].
    i4, i2, i3 := Explode(ii);
    /*
    J2 := 1;
    J10 := 8*i4/(i2*i3);
    J4 := (-16*i4 + i3)/(24*i3);
    J6 := (80*i4*i2 - 384*i1*i3 + i2*i3)/(432*i2*i3);
    J8 := (-768*i4^2*i2 + 416*i4*i2*i3 - 1536*i4*i3^2 + i2*i3^2)/(6912*i2*i3^2);

    Example:
    > FF<I2,I4,I6,I10> := FunctionField(ZZ,4);
    > II := [I2,I4,I6,I10];
    > ii := IgusaClebschToAbsoluteIgusaClebschInvariants(II);
    > i1, i2, i3 := Explode(ii);
    > i4 := I4*I6/I10; assert i4 eq i2*i3/i1;
    > WengToIgusaInvariants([i4,i2,i3]);
    [
        1,
        (I2^2 - 16*I4)/(24*I2^2),
        (I2^3 + 80*I2*I4 - 384*I6)/(432*I2^3),
        (I2^4 + 416*I2^2*I4 - 1536*I2*I6 - 768*I4^2)/(6912*I2^4),
        8*I10/I2^5
    ]
    > jj := AbsoluteIgusaClebschToIgusaInvariants(ii);
    > jj eq IgusaToAbsoluteIgusaInvariants( WengToIgusaInvariants([i4,i2,i3]) );
    true
    */
    return [
        1,
        (-16*i4 + i3)/(24*i3),
        (80*i4*i2 - 384*i4*i3 + i2*i3)/(432*i2*i3),
        (-768*i4^2*i2 + 416*i4*i2*i3 - 1536*i4*i3^2 + i2*i3^2)/(6912*i2*i3^2),
        8*i4/(i2*i3)
    ];
end function;

/*

Hence

*/

function IgusaClebschToWengInvariants(II)
    I2, I4, I6, I10 := Explode(II);
    return [ I4*I6/I10, I2^3*I4/I10, I2^2*I6/I10 ];
end function;

/*

Below we give a preference to the triple (j1,j2,j4), since j3 == j2^2
modulo 2, so (j1,j2,j4) provide a system of local parameters for the
ordinary genus 2 curves (j1 \ne 0).

// Normalised Igusa invariants:
JJ := [
    1,
    J4/J2^2, // = j2/j1
    J6/J2^3, // = j3/j1 = (j2/j1)^2 + 4*j4/j1
    J8/J2^4, // = j4/j1 = (J2*J6 - J4^2)/(4*J2^4) = (j3/j1-(j2/j1)^2)/4
    J10/J2^5 // = 1/j1
];
// 4*j4 + j2^2/j1 = j3
// 
JJ := [1,j2/j1,(j2/j1)^2+4*j4/j1,j4/j1,1/j1];
*/

//////////////////////////////////////////////////////////////////////////////
// The "LIX" representation to Igusa and Igusa-Clebsch invariants.
//////////////////////////////////////////////////////////////////////////////

/*

The following "LIX" representation is used in Gaudry, Houtmann, Kohel,
Ritzenthaler, and Weng:  Let i4, i2, i3 be the "absolute" invariants of Weng,
then we define polynomials H1, G2, G3 and integers N2, N3 such that

  H4(i4) = 0,  i2 = G2(i4)/(H4'(i4)*N2),   i3 = G3(i4)/(H4'(i4)*N3).

Remark.  In what follows I am inconsistent in writing i1 or i4 for the first
invariant (similarly H1 or H4), but since i1 is often taken to be I2^5/I10,
prefer to write i4 = I4*I6/I10 to denote this choice of first invariant.

I prefer to use a multivariate ideal presentation for the defining ideal, and 
use "absolute" Igusa invariants j1, j2, j3, j4, etc. of Igusa:

  j1 = J2^5/J10, j2 = J2^3*J4/J10, j3 = J2^2*J6/J10, j4 = J2*J8/J10.

Since J8 = (J2*J6 - J4^2)/4, I give preference to the invariants j1, j2, j4.

I refer to a set of generators for the ideal of relations by the "Igusa scheme",
as it determined a zero-dimensional CM subscheme of the moduli space of genus
two curves.

The function below compose the above function with the following:

function IgusaLIXToWengInvariantsOverSplittingField(IgLIX)
    P := PolynomialRing(Integers(),3 : Global);
    x1 := P.1;  x2 := P.2; x4 := P.3;
    H4tup, G2tup, G3tup := Explode(LIX);
    H4 := H4tup[1]; // assert H4tup[2] eq 1;
    K<i4> := NumberField(H4);
    N4 := Evaluate(Derivative(H4),i4);
    i2 := Evaluate(G2tup[1],i4)/(N4*G2tup[2]);
    i3 := Evaluate(G3tup[1],i4)/(N4*G3tup[2]);
    return [ i4, i2, i3 ];
end function;

*/

function SplittingPoint(S)
    H1 := UnivariatePolynomial(S[1]);
    H2 := UnivariatePolynomial(S[2]);
    H4 := UnivariatePolynomial(S[3]);
    K1<j1> := NumberField(H1 : DoLinearExtension);
    P2<J2,J4> := PolynomialRing(K1,2);
    S1 := [ Evaluate(H,[j1,J2,J4]) : H in S[[2..#S]] ];
    G2 := UnivariatePolynomial(Resultant(S1[#S1-1],S1[#S1],2));
    vprint IgusaInvariant : "Found G2: deg =", Degree(G2);
    G2 := GCD(H2,G2);
    vprint IgusaInvariant : "      GCD(H2,G2) =", GCD(H2,G2);
    rts2 := Roots(GCD(H2,G2));
    vprintf IgusaInvariant : "Found %o root(s) for j2.\n", #rts2;
    j2 := rts2[1][1];
    P1 := PolynomialRing(K1); X := P1.1;
    G4 := GCD([ Evaluate(H,[j2,X]) : H in S1[[2..#S1]] ]);
    rts4 := Roots(G4);
    vprintf IgusaInvariant : "Found %o root(s) for j4.\n", #rts4;
    j4 := rts4[1][1];
    return [j1,j2,j4];
end function;

//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaLIXDecomposition(IgLIX::SetIndx[SeqEnum[Tup]]) -> SetIndx
    {}
    IgLIX_set := {@ @};
    for IgLIXi in IgLIX do
	IgLIX_set join:= IgusaLIXDecomposition(IgLIXi);
    end for;
    return IgLIX_set;
end intrinsic;

intrinsic IgusaLIXDecomposition(IgLIX::SeqEnum[Tup]) -> SetIndx
    {}
    PQ := PolynomialRing(RationalField());
    PZ := PolynomialRing(IntegerRing());
    H1 := PQ!IgLIX[1][1];
    fact := Factorization(H1);
    //require &and[ f[2] eq 1 : f in fact ] : 
    //        "Argument must not have multiplicities in the components";
    if #fact eq 1 and fact[1][2] eq 1 then
        return {@ IgLIX @};
    end if;
    DH1 := Derivative(H1);
    G2 := PQ!IgLIX[2][1]; N2 := IgLIX[2][2]; 
    G3 := PQ!IgLIX[3][1]; N3 := IgLIX[3][2];
    IgLIX_set := {@ @};
    for i in [1..#fact] do
        H1_i := fact[i][1]; e1_i := fact[i][2];
        n1_i := LCM([ Denominator(c) : c in Coefficients(H1_i) ]);
        H1_i *:= n1_i;
        /*
        Given j1 a root of H1, the remaining invariants are defined by:

        j2 = G2(j1)/(N2*DH1(j1)) mod H1(j1)
        j3 = G3(j1)/(N3*DH1(j1)) mod H1(j1)

        Thus if H1_i is a factor of H1, we define new j2_i, j3_i by

        j2_i = G2(j1)/(N2*DH1_i(j1)) = j2 * DH1(j1)/DH1_i(j1) mod H1_i(j1)
        j3_i = G3(j1)/(N3*DH1_i(j1)) = j3 * DH1(j1)/DH1_i(j1) mod H1_i(j1)

        So we just need to compute DH1_i(j1)^-1 mod H1_i(j1).
        */
        if e1_i gt 1 then
            DH1_inv := InverseMod(Derivative(H1) div H1_i^(e1_i-1),H1_i);
        else
            DH1_inv := InverseMod(Derivative(H1),H1_i);
        end if;
        DS_i := (Derivative(H1_i) * DH1_inv) mod H1_i;
        if e1_i eq 1 then
            G2_i := (G2 * DS_i) mod H1_i;
        else
            G2_i := ((G2 div H1_i^(e1_i-1)) * DS_i) mod H1_i;
        end if;
        n2_i := LCM([ Denominator(c) : c in Coefficients(G2_i) ]);
        G2_i *:= n2_i; N2_i := N2 * n2_i;
        m2_i := GCD([ Numerator(c) : c in Coefficients(G2_i) ] cat [ N2_i ]);
        G2_i div:= m2_i; N2_i div:= m2_i;
        //
        if e1_i eq 1 then
            G3_i := (G3 * DS_i) mod H1_i;
        else
            G3_i := ((G3 div H1_i^(e1_i-1)) * DS_i) mod H1_i;
        end if;
        n3_i := LCM([ Denominator(c) : c in Coefficients(G3_i) ]);
        G3_i *:= n3_i; N3_i := N3 * n3_i;
        m3_i := GCD([ Numerator(c) : c in Coefficients(G3_i) ] cat [ N3_i ]);
        G3_i div:= m3_i; N3_i div:= m3_i;
        Include(~IgLIX_set,[ <PZ!H1_i,1>, <PZ!G2_i,N2_i>, <PZ!G3_i,N3_i> ]);
    end for;
    return IgLIX_set;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaLIXToIgusaScheme(IgLIX::SeqEnum[Tup]) -> SeqEnum
    {Given the LIX representation for Igusa CM invariants, returns a sequence
    of relations among the absolute Igusa invariants j1, j2, and j4.}
    JJ := IgusaLIXToIgusaInvariantsOverSplittingField(IgLIX);
    J2, J4, J6, J8, J10 := Explode(JJ); assert J2 eq 1;
    U10 := 1/J10;
    j1 := J2^5*U10;
    j2 := J2^3*J4*U10;
    j4 := J2*J8*U10;
    P := PolynomialRing(Integers(),3 : Global);
    x1 := P.1/P!1;  x2 := P.2/P!1; x4 := P.3/P!1;
    H1 := Numerator(Evaluate(MinimalPolynomial(j1),x1));
    H2 := Numerator(Evaluate(MinimalPolynomial(j2),x2));
    H4 := Numerator(Evaluate(MinimalPolynomial(j4),x4));
    n := TotalDegree(H1);
    case n:
    when 1:
        t := 0;
    when 2:
        t := 1;
    when 3:
        t := 1;
    else
        t := 0;
        while Binomial(t+3,3) le n+4 do
            t +:= 1;
        end while;
    end case;
    m := Binomial(t+3,3);
    mons := &join[ MonomialsOfDegree(P,i) : i in [t..0 by -1] ];
    jj_invs := [j1,j2,j4]; 
    mons_jj := [ Evaluate(mon,jj_invs) : mon in mons ];
    M := Matrix([ Eltseq(mon_jj) : mon_jj in mons_jj ]);
    M *:= LCM([ Denominator(c) : c in Eltseq(M) ]);
    M := Matrix(IntegerRing(),Ncols(M),Eltseq(M));
    N := LLL(BasisMatrix(Kernel(M))); 
    s := Min(m-n,3);
    for i in [1..s] do
        j := 1;
        while N[i,j] eq 0 do
            j +:= 1;
        end while;
        if N[i,j] lt 0 then
            N[i] *:= -1;
        end if;
    end for;
    return [ H1, H2, H4 ] cat 
        [ &+[ N[i,j]*mons[j] : j in [1..m] ] : i in [1..s] ];
end intrinsic;

intrinsic IgusaLIXToIgusaInvariantsOverSplittingField(IgLIX::SeqEnum[Tup]) -> SeqEnum
    {Given the LIX representation for Igusa CM invariants, returns the
    first five absolute Igusa invariants over the splitting field.}
    // Here we denote Weng's choice of invariants by
    //   (i4,i2,i3) = (I4*I6/I10,I2^3*I4/I10,I2^2*I6/I10)
    // in order to define i1 = I2^5/I10. 
    H4tup, G2tup, G3tup := Explode(IgLIX);
    H4 := H4tup[1];
    require IsIrreducible(H4) :
        "Argument is not irreducible: try IgusaLIXDecomposition(IgLIX);";
    K4<i4> := NumberField(H4 : DoLinearExtension);
    if i4 eq 0 then
        return [ K4 | 0, 0, 0, 0, 800000 ];
    end if;
    N1 := Evaluate(Derivative(H4),i4);
    i2 := Evaluate(G2tup[1],i4)/(N1*G2tup[2]);
    require i2 ne 0 : "Argument must define a Igusa CM scheme with nozero i2.";
    i3 := Evaluate(G3tup[1],i4)/(N1*G3tup[2]);
    require i3 ne 0 : "Argument must define a Igusa CM scheme with nozero i3.";
    i1 := i2*i3/i4;
    J2 := 1;
    // J4 = (-16*i4 + i3)/(24*i3) = (i1 - 16*i2)/(24*i1):
    J4 := (i1 - 16*i2)/(24*i1);
    // J6 = (80*i4*i2 - 384*i4*i3 + i2*i3)/(432*i2*i3) = (i1 + 80*i2 - 384*i3)/(432*i1)
    J6 := (i1 + 80*i2 - 384*i3)/(432*i1);
    // J8 = (-768*i4^2*i2 + 416*i4*i2*i3 - 1536*i4*i3^2 + i2*i3^2)/(6912*i2*i3^2)
    //    = (i1^2 + 416*i1*i2 - 1536*i1*i3 - 768*i2^2)/(6912*i1^2)
    J8 := (i1^2 + 416*i1*i2 - 1536*i1*i3 - 768*i2^2)/(6912*i1^2);
    // J10 = 8*i4/(i2*i3) = 8/i1
    J10 := 8/i1;
    return [ J2, J4, J6, J8, J10 ];
end intrinsic;

function HenselLiftingField(FF,prec)
    p := Characteristic(FF); 
    r := Degree(FF);
    R := pAdicField(p,prec);
    return UnramifiedExtension(R,r);
end function;

function IgusaValuationNormalization(JJ)
    p := UniformizingElement(Universe(JJ));
    n := Max([ Floor(-Valuation(JJ[i])/i) : i in [1..5] ]);
    return n eq 0 select JJ else [ p^(n*i)*JJ[i] : i in [1..5] ];
end function;

function HenselLiftingPrecision(IgLIX,p)
    H1 := IgLIX[1][1];
    n1 := &+[ Valuation(c,p) : c in Eltseq(H1) ];
    n2 := Valuation(IgLIX[2][2],p);
    n3 := Valuation(IgLIX[3][2],p);
    d1 := Degree(H1);
    k1 := Valuation(LeadingCoefficient(H1),p);
    k2 := Valuation(Coefficient(H1,0),p);
    v1 := 1; 
    m1 := 4;
    repeat
	m1 := Max(Ceiling(Log(2,v1)),m1+1);
	P1 := PolynomialRing(pAdicQuotientRing(p,2^m1));
        v1 := Valuation(Discriminant(P1!H1)) + d1*k1;
    until v1 lt 2^m1;
    return Max([ v1+1, n1 , n2, n3 ]) + Max(64 div p,8);
end function;

function IgusaLIXToWengInvariantsOverLiftingField(IgLIX,FF : LiftingPrecision := 0)
    p := Characteristic(FF);
    H1 := IgLIX[1][1];
    G2 := IgLIX[2][1]; N2 := IgLIX[2][2];
    G3 := IgLIX[3][1]; N3 := IgLIX[3][2];
    m := LiftingPrecision eq 0 select HenselLiftingPrecision(IgLIX,p) else LiftingPrecision;
    vprint IgusaInvariant : "Lifting to precision..", m;
    S := HenselLiftingField(FF,m);
    PS<x> := PolynomialRing(S);
    dxH1 := Derivative(H1);
    // Caution: This selects only the ORDINARY Igusa invariants when p in {2,3}.
    if p eq 2 then
	ii_1 := [ r[1] : r in Roots(PS!H1) | Valuation(r[1]) eq -7 ];
    elif p eq 3 then
        ii_1 := [ r[1] : r in Roots(PS!H1) | Valuation(r[1]) ge 0 ];
    else
        ii_1 := [ r[1] : r in Roots(PS!H1) ]; //| Valuation(Evaluate(dxH1,r[1])) ge 0 ];
    end if;
    return [ [ i1, Evaluate(G2,i1)/(Evaluate(dxH1,i1) * N2), Evaluate(G3,i1)/(Evaluate(dxH1,i1) * N3) ] : i1 in ii_1 ];
end function;

intrinsic IgusaLIXToIgusaInvariants(IgLIX::SeqEnum,FF::Fld :
    ExactDegree := false, LiftingPrecision := 0) -> SeqEnum
    {}
    // i1 = (1728*j1*j2^3 + 408*j1*j2^2 + 6912*j1*j2*j4 - 44*j1*j2 - 288*j1*j4 + j1)/128,
    // i2 = (-24*j1*j2 + j1)/2,
    // i3 = (-72*j1*j2^2 - 20*j1*j2 - 288*j1*j4 + j1)/8
    // H1(j1/128) == 0 mod 2
    // H1'(j1/128) * N2 * i2 = G2(j1/128), hence
    //     H1'(j1/128) * j1 * N2 * 24 * j2 = H1'(j1/128) * N2 * j1 - 2 * G2(j1/128)
    // H1'(j1/128) * N3 * i3 = G3(j1/128), hence
    //     H1'(j1/128) * j1 * N3 * 288 * j4 = H1'(j1/128) * N3 * (-72*j1*j2^2 - 20*j1*j2  + j1) - 8 * G2(j1/128)
    if Eltseq(IgLIX[1][1]) eq [0,1] and IgLIX[2][1] eq 0 and IgLIX[3][1] eq 0 then
        if Characteristic(FF) in {2,5} then
            return [];
        else
            return [ [ FF | 0, 0, 0, 0, 800000 ] ];
        end if;
    end if;
    H1 := IgLIX[1][1];
    N1 := LeadingCoefficient(H1);
    N2 := IgLIX[2][2];
    N3 := IgLIX[3][2];
    P := PolynomialRing(FF);
    p := Characteristic(FF);
    rt_1 := Roots(P!H1);
    if #rt_1 eq 0 then
	ei_1 := 1; // should really consider the Newton polygon here...
    else
	ei_1 := Min([ r[2] : r in rt_1 ]);
    end if;
    if p ne 0 and (p in {2,3} or N1 mod p eq 0 or N2 mod p eq 0 or N3 mod p eq 0 or ei_1 gt 1) then
        jj_seq := [ Parent([ FF | ]) | ];
	ii_seq := IgusaLIXToWengInvariantsOverLiftingField(IgLIX,FF : LiftingPrecision := LiftingPrecision);
	if #ii_seq eq 0 then return jj_seq; end if;
	SS := RingOfIntegers(Universe(ii_seq[1]));
        KK, m := ResidueClassField(SS);
        for ii_lift in ii_seq do
            jj_lift := IgusaValuationNormalization(WengToIgusaInvariants(ii_lift));
            if Valuation(jj_lift[5]) ne 0 then continue; end if;
            if &or[ Valuation(j) lt 0 : j in jj_lift ] then continue; end if;
            jj := [ FF!m(SS!j) : j in jj_lift ];
            if ExactDegree then
                deg := LCM([ Degree(MinimalPolynomial(ji)) : ji in jj ]);
                if Degree(FF) ne deg then continue; end if;
            end if;
            Append(~jj_seq,jj);
        end for;
    else
        jj_seq := [ Parent([ FF | ]) | ];
	ii_1 := [ r[1] : r in rt_1 | r[2] eq 1 ];
	G2 := IgLIX[2][1];
        G3 := IgLIX[3][1];
        dxH1 := Derivative(H1);
        ii_seq := [
            [ i1,
            Evaluate(G2,i1)/(Evaluate(dxH1,i1) * N2),
            Evaluate(G3,i1)/(Evaluate(dxH1,i1) * N3) ] : i1 in ii_1 ];
        for ii in ii_seq do
	    if 0 in ii then
                ii_lift_seq := IgusaLIXToWengInvariantsOverLiftingField(IgLIX,FF);
		SS := RingOfIntegers(Universe(ii_lift_seq[1]));
                KK, m := ResidueClassField(SS);
                flag := false;
                for ii_lift in ii_lift_seq do
                    if &or[ Valuation(i) lt 0 : i in ii_lift ] then continue; end if;
                    if [ FF!m(i) : i in ii_lift ] ne ii then continue; end if;
                    jj_lift := IgusaValuationNormalization(WengToIgusaInvariants(ii_lift));
                    if Valuation(jj_lift[5]) ne 0 then continue; end if;
                    if &or[ Valuation(j) lt 0 : j in jj_lift ] then continue; end if;
                    jj := [ FF!m(SS!j) : j in jj_lift ];
                    flag := true; break;
		end for;
                if not flag then continue; end if;
            else
                jj := WengToIgusaInvariants(ii);
            end if;
	    if jj[5] eq 0 then continue; end if;
            if Type(FF) in {FldFin,FldQuad,FldCyc,FldNum} and ExactDegree then
                deg := LCM([ Degree(MinimalPolynomial(ji)) : ji in jj ]);
                if Degree(FF) ne deg then continue; end if;
            end if;
	    Append(~jj_seq,jj);
        end for;
    end if;
    return jj_seq;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaToIgusaLIXInvariants(JJ::[FldRatElt]) -> SetIndx
    {}
    ZZ := IntegerRing();
    PZ := PolynomialRing(ZZ); x := PZ.1;
    II := IgusaToIgusaClebschInvariants(JJ);
    i1, i2, i3 := Explode(IgusaClebschToWengInvariants(II));
    H1 := MinimalPolynomial(i1);
    N1 := LCM([ Denominator(c) : c in Eltseq(H1) ]);
    H1 := PZ!(N1*H1);
    num2 := Numerator(N1*i2); den2 := Denominator(N1*i2);
    num3 := Numerator(N1*i3); den3 := Denominator(N1*i3);
    return [ <H1,1>, <PZ!num2,den2>, <PZ!num3,den3> ];
end intrinsic;

intrinsic IgusaToIgusaLIXInvariants(JJ::[FldNumElt]) -> SetIndx
    {Given a sequence of Igusa invariants over a number field, return
    the associated Igusa LIX invariants on which they vanish.}
    deg := Degree(Universe(JJ));
    ZZ := IntegerRing();
    PZ := PolynomialRing(ZZ); x := PZ.1;
    II := IgusaToIgusaClebschInvariants(JJ);
    i1, i2, i3 := Explode(IgusaClebschToWengInvariants(II));
    H1 := MinimalPolynomial(i1);
    H1 := PZ!(LCM([ Denominator(c) : c in Eltseq(H1) ])*H1);
    N1 := Evaluate(Derivative(H1),i1);
    d1 := Degree(H1);
    T1 := Matrix([ Eltseq(i1^k) : k in [0..d1-1] ]);
    v2 := Vector(Eltseq(N1*i2));
    v3 := Vector(Eltseq(N1*i3));
    if d1 eq deg then
	U1 := T1^-1;
	c2 := v2*U1;
	c3 := v3*U1;
    else
	bool2, c2 := IsConsistent(T1,v2); assert bool2;
	bool3, c3 := IsConsistent(T1,v3); assert bool3;
    end if;
    //
    c2 := Eltseq(c2);
    N2 := LCM([ Denominator(c) : c in c2 ]);
    G2 := PZ![ ZZ | N2*c : c in c2 ];
    //
    c3 := Eltseq(c3);
    N3 := LCM([ Denominator(c) : c in c3 ]);
    G3 := PZ![ ZZ | N3*c : c in c3 ];
    //
    return [ <H1,1>, <G2,N2>, <G3,N3> ];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Conversion from Igusa scheme to Igusa-Clebsch and Igusa invariants (over
// a splitting field), and to LIX univariate polynomial representations.
//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaSchemeToAbsoluteIgusaClebschInvariantsOverSplittingField(
    IgS::SeqEnum[RngMPolElt]) -> SeqEnum
    {Given the scheme representation for Igusa CM invariants, returns the
    absolute Igusa-Clebsch [i1,i2,i3] invariants over the splitting field.}
    pp := SplittingPoint(IgS);
    j1 := pp[1];
    j2 := pp[2];
    j4 := pp[3];
    j3 := 4*j4 + j2^2/j1;
    i1 := 8*j1;
    i2 := (j1 - 24*j2)/2;
    i3 := (j1 - 20*j2 - 72*j3)/8;
    return [ i1, i2, i3 ];
end intrinsic;

intrinsic IgusaSchemeToIgusaLIX(IgS::SeqEnum[RngMPolElt]) -> SeqEnum
    {}
    pp := SplittingPoint(IgS);
    K1 := Universe(pp);
    // Absolute Igusa invariants:
    j1 := pp[1];
    j2 := pp[2];
    j4 := pp[3];  
    j3 := 4*j4 + j2^2/j1;
    // Absolute Igusa-Clebsch invariants:
    i1 := 8*j1;
    i2 := (j1 - 24*j2)/2;
    i3 := (j1 - 20*j2 - 72*j3)/8;
    i4 := i2*i3/i1;
    ZZ := IntegerRing();
    // Absolute Igusa invariants:
    S0 := Eltseq(MinimalPolynomial(i4));
    N0 := LCM([ Denominator(c) : c in S0 ]);
    H4 := Polynomial([ IntegerRing() | N0*c : c in S0 ]);
    N1 := Evaluate(Derivative(H4),i4);
    // 
    K4 := NumberField(H4 : DoLinearExtension); 
    mK1_K4 := Inverse(hom< K4->K1 | i4 >);
    // 
    G2seq := Eltseq(mK1_K4(N1*i2));
    N2 := LCM([ Denominator(c2) : c2 in G2seq ]);
    G2 := Polynomial([ ZZ | N2*c2 : c2 in G2seq ]); 
    //
    G3seq := Eltseq(mK1_K4(N1*i3));
    N3 := LCM([ Denominator(c3) : c3 in G3seq ]);
    G3 := Polynomial([ ZZ | N3*c3 : c3 in G3seq ]); 
    /* 
    assert Evaluate(H4,i4) eq 0;
    assert Evaluate(G2,i4)/(N1*N2) eq i2;
    assert Evaluate(G3,i4)/(N1*N3) eq i3;
    */
    return [ <H4,1>, <G2,N2>, <G3,N3> ];
end intrinsic;
