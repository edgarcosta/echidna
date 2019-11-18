////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                 AGM-X0(N) Heegner Class Polynomials                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare verbose Heegner, 3;

import "frobenius_representation.m" : SatohFrobeniusNorm;

function BalancedMod(t,m)
    t mod:= m;
    if t gt ((m+1) div 2) then
        t -:= m;
    end if;
    return t;
end function;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

function MyRoots(f)
    R := BaseRing(Parent(f));
    F := ResidueClassField(R);
    f0 := PolynomialRing(F)!f;
    return [ HenselLift(f,R!r0[1]) : r0 in Roots(f0) ];
end function;

function PhiX0(N,p,X)
    P := PolynomialRing(Parent(X));
    Y := P.1;
    case N:
    when 16: 
        case p:
        when 3:
            return X^4 - 16*X^3*Y^3 + 6*X^2*Y^2 - X*Y + Y^4;
        when 5:
            return X^6 - 256*X^5*Y^5 + 10*X^5*Y + 15*X^4*Y^2
                - 20*X^3*Y^3 + 15*X^2*Y^4 + 10*X*Y^5 - X*Y + Y^6;
        when 7:
            return X^8 - 4096*X^7*Y^7 + 224*X^7*Y^3 - 1792*X^6*Y^6
                + 140*X^6*Y^2 - 448*X^5*Y^5 + 14*X^5*Y + 70*X^4*Y^4
                + 224*X^3*Y^7 - 28*X^3*Y^3 + 140*X^2*Y^6 - 7*X^2*Y^2
                + 14*X*Y^5 - X*Y + Y^8;
        when 11:
            return
                X^12 - 1048576*X^11*Y^11 + 90112*X^11*Y^7 - 1584*X^11*Y^3
                - 1441792*X^10*Y^10 + 70400*X^10*Y^6 + 1298*X^10*Y^2
                - 1036288*X^9*Y^9 + 65472*X^9*Y^5 - 99*X^9*Y
                - 298496*X^8*Y^8 + 19151*X^8*Y^4 + 90112*X^7*Y^11
                - 74272*X^7*Y^7 + 4092*X^7*Y^3 + 70400*X^6*Y^10
                - 7876*X^6*Y^6 + 275*X^6*Y^2 + 65472*X^5*Y^9
                - 4642*X^5*Y^5 + 22*X^5*Y + 19151*X^4*Y^8
                - 1166*X^4*Y^4 - 1584*X^3*Y^11 + 4092*X^3*Y^7
                - 253*X^3*Y^3 + 1298*X^2*Y^10 + 275*X^2*Y^6
                - 22*X^2*Y^2 - 99*X*Y^9 + 22*X*Y^5 - X*Y + Y^12;
        when 17:
            return X^18 - 4294967296*X^17*Y^17 + 570425344*X^17*Y^13
                - 23396352*X^17*Y^9 + 287232*X^17*Y^5 - 306*X^17*Y
                + 3422552064*X^16*Y^14 - 529203200*X^16*Y^10
                + 19253248*X^16*Y^6 + 28441*X^16*Y^2
                + 10267656192*X^15*Y^15 - 2560229376*X^15*Y^11
                + 132596736*X^15*Y^7 - 793968*X^15*Y^3
                + 3422552064*X^14*Y^16 - 3873767424*X^14*Y^12
                + 194865152*X^14*Y^8 + 2120308*X^14*Y^4
                + 570425344*X^13*Y^17 - 5421268992*X^13*Y^13
                + 139394560*X^13*Y^9 + 12298888*X^13*Y^5
                + 1122*X^13*Y - 3873767424*X^12*Y^14
                - 312160256*X^12*Y^10 + 33457156*X^12*Y^6
                + 75208*X^12*Y^2 - 2560229376*X^11*Y^15
                - 419776512*X^11*Y^11 + 27917808*X^11*Y^7
                + 517956*X^11*Y^3 - 529203200*X^10*Y^16
                - 312160256*X^10*Y^12 + 9441902*X^10*Y^8
                + 761192*X^10*Y^4 - 23396352*X^9*Y^17
                + 139394560*X^9*Y^13 - 17290156*X^9*Y^9
                + 544510*X^9*Y^5 - 357*X^9*Y + 194865152*X^8*Y^14
                + 9441902*X^8*Y^10 - 1219376*X^8*Y^6 -
                8075*X^8*Y^2 + 132596736*X^7*Y^15 +
                27917808*X^7*Y^11 - 1639752*X^7*Y^7 -
                39066*X^7*Y^3 +
                19253248*X^6*Y^16 +
                33457156*X^6*Y^12 - 1219376*X^6*Y^8 -
                59109*X^6*Y^4 + 287232*X^5*Y^17 + 12298888*X^5*Y^13 +
                544510*X^5*Y^9 -
                82722*X^5*Y^5 + 34*X^5*Y + 2120308*X^4*Y^14 +
                761192*X^4*Y^10 - 59109*X^4*Y^6 +
                204*X^4*Y^2 - 793968*X^3*Y^15 + 517956*X^3*Y^11
                - 39066*X^3*Y^7 + 612*X^3*Y^3 +
                28441*X^2*Y^16 + 75208*X^2*Y^12 -
                8075*X^2*Y^8 + 204*X^2*Y^4 - 306*X*Y^17
                + 1122*X*Y^13 - 357*X*Y^9 + 34*X*Y^5 - X*Y + Y^18;
        end case;
    end case;
    assert false;
end function;

function ExtendPrimeGenerators(Q,p)
    D := Discriminant(Q);
    h := ClassNumber(Q);
    m := Conductor(Q);
    pp := PrimeForm(Q,p);
    if Order(pp) eq h then return [], []; end if;
    prms := [];
    ords := [];
    Sfrms := {@ pp^i : i in [0..Order(pp)-1] @};
    Qfrms := Sfrms;
    while #Qfrms lt h do
        p := NextPrime(p);
        while KroneckerSymbol(D,p) eq -1 or m mod p eq 0 do
            p := NextPrime(p);
        end while;
        qq := Q!1;
        pp := PrimeForm(Q,p);
        for i in [1..Order(pp)] do
            qq *:= pp;
            if qq notin Qfrms then
                assert i ne Order(pp);
                Qfrms join:= {@ ff*qq : ff in Sfrms @};
            else
                if i ne 1 then
                    Append(~prms,p);
                    Append(~ords,i);
                end if;
                break i;
            end if;
        end for;
        Sfrms := Qfrms;
    end while;
    return prms, ords;
end function;

intrinsic HeegnerClassPolynomial(
    N::RngIntElt,x::FldFinElt : DefaultPrecision := 100) -> RngUPolElt
    {}
    require x ne 0 : "Argument 2 must be nonzero.";
    FF := Parent(x);
    n := Degree(FF);
    p := Characteristic(FF);
    require N eq p :
	"Argument 1 must be the characteristic of the parent of argument 2.";
    prec := DefaultPrecision;

    //v1 := AGMLift(N,x,prec);
    //Nrm := AGMFrobeniusNorm(N,p,v1);
    v1 := SatohAGMLift(x,prec);
    Nrm := SatohFrobeniusNorm(p,v1);

    t := BalancedMod(Integers()!Nrm,p^(n-1));
    D := t^2-4*#FF;
    vprint Heegner, 2 : "D =", D;
    Q := QuadraticForms(t^2-4*#FF);
    prms, ords := ExtendPrimeGenerators(Q,p);
    vprint Heegner, 3 : "prms =", prms;
    vprint Heegner, 3 : "ords =", ords;
    Gelts := [v1];
    Relts := {@ x^p^k : k in [0..n-1] @};
    // "Relts =", Relts;
    for i in [1..#prms] do
        q := prms[i];
        vprint Heegner, 3 : "q =", q;
        vprint Heegner, 3 : "o =", ords[i];
        for j in [1..(ords[i] div 2)] do
            Celts := [];
            for v1 in Gelts do
                for u1 in MyRoots(PhiX0(N,q,v1)) do
                    u0 := FF!u1;
                    if u0 notin Relts then
                        // "New u0 =", u0;
                        Append(~Celts,u1);
                        Relts join:= {@ u0^p^k : k in [0..n-1] @};
                        // "Relts =", Relts;
                    else
                        
                    end if;
                end for;
            end for;
            Gelts cat:= Celts;
        end for;
    end for;
    Hrts := [];
    for v1 in Gelts do
        assert N eq 16;
        v2 := FrobeniusImage(v1);
        x1 := v2;
        y1 := v1*(4*v2^2+1);
        // x2 is twice the A-L image:
        x2 := (-2*v1+1) div (2*v1+1); 
        y2 := (-2*v1+1)*(2*v2+1) div ((2*v1+1)*(-2*v2+1));
        // zz := (y2+y1) div (2*x1+x2);
        zz := (y2+y1-2) div (2*x1+x2-2);
        // y1+y2 = 2*ww^3 - 3*ww + 2;
        // 2*x1+x2 = 2*ww^2 - 1;
        // y1^2 - (2*zz^3-3*zz+2)*y1 - (2*zz^3-4*zz^2+3*zz-1);
        if GetVerbose("Heegner") ge 3 then
            print "Valuations:";
            // Verify that all give zero:
            Valuation((4*v2^2+1)*v1^2-v2);
            Valuation((4*x1^2+1)*x1-y1^2);
            Valuation((x2^2+1)*x2-2*y2^2);
        end if;
        Append(~Hrts,zz);
    end for;
    S := Eltseq(&*[ MinimalPolynomial(zz) : zz in Hrts ]);
    R := ChangePrecision(U,Precision(U)-32) where U := Universe(S);
    f := PolynomialRing(Rationals())!
        RationalReconstruction([R!c : c in S]);
    return f, D, Hrts;
end intrinsic;

intrinsic HeegnerDivisor(N::RngIntElt,x::FldFinElt : Precision := 100)
    -> RngUPolElt
    {}
    f, D := HeegnerClassPolynomial(N,x : DefaultPrecision := Precision);
    H := NumberField(f); z := H.1;
    w := Sqrt(D*(4*z^4-12*z^2+16*z-7));
    // return f, Parent(f)!Eltseq(w), D;
    // K<t> := QuadraticField(D);
    P<x> := PolynomialRing(Rationals());
    // E := HyperellipticCurve(4*x^3+x);
    C := HyperellipticCurve(D*(4*x^4-12*x^2+16*x-7));
    J := Jacobian(C);
    // f := PolynomialRing(K)!f;
    return J![f,Parent(f)!Eltseq(w)];
end intrinsic;

/*

A2<x,y> := AffineSpace(QQ,2);
E := Curve(A2,y^2-4*x^3-x);
C := Curve(A2,y^2-(4*x^4-12*x^2+16*x-7)/4);
z := (-y+1)/(-2*x+1);
w := (z^2-3/2+1/z)-y/z;
m := map< E->C | [z,w] >;
m0 := Extend(ProjectiveClosure(m));
_, n0 := IsInvertible(m0);
P2<X,Y,Z> := Ambient(Domain(m0));
E0 := Domain(m0);
C0 := Codomain(m0);
i := Extend(map< E0->E0 |
    [(Y-2*X)/(Y+2*X)/2,(X*Z^2-4*X^3)/(Z*(4*X^2+4*X*Y+Y^2)),1] >);

*/
