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

function Level1SatakeRationalPoints(DAB,FF)
    assert Type(FF) eq FldFin;
    p := Characteristic(FF); q := #FF; r := Valuation(q,p);
    DBIX := IgusaLIXDatabase();
    IgLIXseq := IgusaLIXInvariants(DBIX,DAB);
    ss := {@ @};
    for IgLIX in IgLIXseq do
        JJset := { JJ : JJ in IgusaLIXToIgusaInvariants(IgLIX,FF) };
        for JJ in JJset do
            Include(~ss,IgusaToSatakeInvariants(JJ));
        end for;
    end for;
    return ss;
end function;

function IgusaLIXToSatakePointArray(IgLIXseq,FF)
    assert IsPrimeField(FF);
    p := Characteristic(FF);
    PF<x> := PolynomialRing(FF); 
    pnts := AssociativeArray(IntegerRing());
    for IgLIX in IgLIXseq do
        H1 := IgLIX[1][1];
        G2 := IgLIX[2][1]; N2 := IgLIX[2][2];
        G3 := IgLIX[3][1]; N3 := IgLIX[3][2];
        if N2 mod p eq 0 then continue; end if;
        if N3 mod p eq 0 then continue; end if;
        fac := [ f[1] : f in Factorization(PF!H1) | f[2] eq 1 ];
        for f in fac do
            d := Degree(f);
            KK := FiniteField(p^d);
            AssignNames(~KK,["t" * Sprint(d)]);
            for rr in Roots(f,KK) do
                i4 := rr[1];
                if i4 eq 0 then 
                    continue;
                    //JJ := [ KK | 0, 0, 0, 0, 800000 ];
                    ss := [ 0, 0, 5, 0 ];
                    if IsDefined(pnts,1) then
                        Append(~pnts[1],ss);
                    else
                        pnts[1] := [ss];
                    end if;
                    continue;
                end if;
                N1 := Derivative(H1)(i4); assert N1 ne 0;
                i2 := G2(i4)/(N1*N2);
                i3 := G3(i4)/(N1*N3);
                i1 := i2*i3/i4;
                if i1 eq 0 then continue; end if;
                /*
                // Igusa invariants:
                JJ := [ 1,
                    (i1 - 16*i2)/(24*i1),
                    (i1 + 80*i2 - 384*i3)/(432*i1),
                    (i1^2 + 416*i1*i2 - 1536*i1*i3 - 768*i2^2)/(6912*i1^2),
                    8/i1 ];
                */
                // Satake invariants:
                ss := [
                    12*i2/i1,
                    12*(i2 - 3*i3)/i1,
                    60*(648*i1 + i2^2 - 3*i2*i3)/i1^2,
                    12*(972*i1^2 + 2*i1*i2^2 - 12*i1*i2*i3 + 18*i1*i3^2 + 9*i2^3)/i1^3
                    ];
                if IsDefined(pnts,d) then
                    Append(~pnts[d],ss);
                else
                    pnts[d] := [ss];
                end if;
            end for;
        end for;
    end for;
    return pnts;
end function;

function OrbitRepresenatives(pnts,d)
    p := Characteristic(Universe(pnts[1]));
    Orbits := { { [ c^p^i : c in P ] : i in [0..d-1] } : P in pnts };
    return [ Representative(orb) : orb in Orbits ];
end function;

function Level1SatakeRMPoints(D,FF,num : TestPolynomial := 0)
    assert Type(FF) eq FldFin;
    assert IsPrimeField(FF);
    p := Characteristic(FF);
    DBCM := QuarticCMFieldDatabase();
    DBIX := IgusaLIXDatabase();
    ss := AssociativeArray(IntegerRing());
    h := 1;
    curr := 0;
    while curr lt num and h le 128 do
        DAB_invs := QuarticCMFieldInvariantsWithClassNumber(DBCM,h,2);
        DAB_invs := [ DAB : DAB in DAB_invs | DAB[1] eq D ];
        ninvs := #DAB_invs; 
        DAB_invs := [ DAB : DAB in DAB_invs | DAB in DBIX ];
        if ninvs eq #DAB_invs then
            printf "  h: %o (ninvs = %o)\n", h, ninvs;
        else
            printf "  h: %o (ninvs = %o < %o)\n", h, #DAB_invs, ninvs;
        end if;
        for DAB in DAB_invs do
            IgLIXseq := IgusaLIXInvariants(DBIX,DAB);
            pnts := IgusaLIXToSatakePointArray(IgLIXseq,FF);
            for d in Keys(pnts) do
                for P in pnts[d] do
                    if TestPolynomial(P) ne 0 then
                        print "DAB", DAB; assert false;
                    end if;
                end for;
                orbs := OrbitRepresenatives(pnts[d],d);
                if IsDefined(ss,d) then
                    ss[d] cat:= orbs;
                else
                    ss[d] := orbs;
                end if;
            end for;
            curr := &+[ d*#ss[d] : d in Keys(ss) ];
        end for;
        h +:= 1;
    end while;
    return ss;
end function;

function PointArrayToMatrix(mons,pnts,FF)
    A := RMatrixSpace(FF,#mons,0)!0;
    for d in Keys(pnts) do
        for P in pnts[d] do
            A := HorizontalJoin(A,Matrix([ Eltseq(m(P)) : m in mons ]));
        end for;
    end for;
    return A;
end function;

intrinsic Level1SatakeHumbertInterpolation(D::RngIntElt :
    NumberOfPrimes := 12,
    InitialPrime := 97,
    TestPolynomial := 0) -> RngMPolElt
    {}
    require D gt 0 and not IsSquare(D) and IsFundamental(D) :
        "Argument must be a positive fundamental discriminant.";
    ZZ := IntegerRing();
    P<s2,s3,s5,s6> := PolynomialRing(ZZ,[2,3,5,6]);
    if TestPolynomial eq 0 then TestPolynomial := P!0; end if;
    deg := DegreeOfLevel1HumbertPolynomial(D);
    print "Humbert degree:", deg;
    mons := MonomialsOfWeightedDegree(P,deg div 2);
    print "Number of monomials:", #mons;
    p := Max(InitialPrime-1,16*D);
    cffs_seq := [ ];
    mods_seq := [ ];
    while #cffs_seq lt NumberOfPrimes do
        p := NextPrime(p);
        while KroneckerSymbol(D,p) ne 1 do p := NextPrime(p); end while;
        print "p =", p;
        FF := FiniteField(p);
        time ss := Level1SatakeRMPoints(D,FF,#mons+8 : TestPolynomial := TestPolynomial);
        printf "Found %o points of degrees:\n", &+[ #ss[d] : d in Keys(ss) ];
        print [ <d,#ss[d]> : d in Sort(SetToSequence(Keys(ss))) ];
        print "and total weight", &+[ d*#ss[d] : d in Keys(ss) ];
        time A := PointArrayToMatrix(mons,ss,FF);
        time V := Kernel(A);
        if Dimension(V) ne 1 then
            print V;
            assert Dimension(V) eq 1;
        end if;
        //print V.1;
        Append(~cffs_seq,[ ZZ!c : c in Eltseq(V.1) ]);
        Append(~mods_seq,p);
    end while;
    cffs := [ CRT([ cffs[j] : cffs in cffs_seq ],mods_seq) : j in [1..#mons] ];
    M := &*mods_seq;
    time ncffs := LLL(VerticalJoin(Matrix(#mons,cffs),M*IdentityMatrix(ZZ,#mons)))[1];
    if ncffs[1] lt 0 then ncffs *:= -1; end if;
    return &+[ ncffs[i]*mons[i] : i in [1..#mons] ], M;
end intrinsic;

/*
// D in {5,8,12,13} terminate take 8-16 primes
D := 17;
SD := Level1SatakeHumbertPolynomial(ZZ,D);
Level1SatakeHumbertInterpolation(D :
    InitialPrime := 2,
    NumberOfPrimes := 32,
    TestPolynomial := SD);
D := 5;
SD := Level1SatakeHumbertPolynomial(ZZ,D);
Level1SatakeHumbertInterpolation(D :
    InitialPrime := NextPrime(2^19),
    NumberOfPrimes := 4,
    TestPolynomial := SD);
*/
