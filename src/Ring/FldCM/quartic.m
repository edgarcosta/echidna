//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                         QUARTIC CM FIELDS                                //
//                                                                          //
//          Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*

DAB := [ 5, 53, 601 ];
K := QuarticCMField(DAB);
GoodOrdinaryPrimes(K,n);
FF := FiniteField(47,5);
JJ_seq := IgusaLIXToIgusaInvariants(IgLIX,FF);
for JJ in JJ_seq do
    C := HyperellipticCurveFromIgusaInvariants(JJ);
    chi := FrobeniusCharacteristicPolynomial(C);
    L := 
    IsIsomorphic(K,NumberField(chi));
end for;

*/
/*
DRK: Created 19/05/2006
*/

declare attributes FldNum:
    QuarticCMFieldType,
    QuarticCMFieldInvariants;

intrinsic IsQuarticCMField(K::FldNum) -> BoolElt
    {}
    return Degree(K) eq 4 and IsCMField(K);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic QuarticCMField(DAB::[RngIntElt]) -> FldNum
    {Given an integer sequence [D,A,B] return the quartic CM field with
    defining polynomial X^4 + A*X^2 + B, and A^2 - 4*B = m^2*d.}
    require #DAB eq 3 : "Argument must consist of three elements";
    D, A, B := Explode(DAB);
    require D gt 0 and IsFundamental(D) :
        "Argument 1 must be a positive fundamental discriminant.";
    if A eq 0 then
        require B lt 0 :
            "Argument 3 must be negative if argument 2 is zero.";
    else
        require D gt 0 : "Argument 1 must be positive.";
        require A gt 0 : 
            "Argument 2 must be positive or zero and argument 3 negative.";
        D2 := A^2-4*B;
        require D2 mod D eq 0 and IsSquare(D2 div D): 
            "Argument [D,A,B] must satisfy A^2 - 4*B = m^2*D.";
    end if;
    return QuarticCMField(D,A,B);
end intrinsic;

intrinsic QuarticCMField(D::RngIntElt,A::RngIntElt,B::RngIntElt) -> FldNum
    {Given integer D, A and B, such that A^2 - 4*B = m^2*D, return
    the quartic CM field with defining polynomial X^4 + A*X^2 + B.}
    X := PolynomialRing(Integers()).1;
    require D gt 0 and IsFundamental(D) :
        "Argument 1 must be a positive fundamental discriminant.";
    if A eq 0 then
        require B lt 0 :
            "Argument 3 must be negative if argument 2 is zero.";
        t := D mod 2; n := (t-D) div 4;
        K := AbsoluteField(NumberField([X^2-t*X+n,X^2-B]));
        K`QuarticCMFieldType := [2,2];
        return K;
    end if;
    require D gt 0 : "Argument 1 must be positive.";
    require A gt 0 : 
        "Argument 2 must be positive or zero and argument 3 negative.";
    D2 := A^2-4*B;
    require D2 mod D eq 0 and IsSquare(D2 div D): 
        "Arguments 1, 2 and 3 (= D, A and B), must satisfy A^2 - 4*B = m^2*D.";
    require D2 gt 0 and not IsSquare(D) : 
        "Arguments 2 and 3, A and B, must satisfy D = A^2 - 4*B > 0 and D non-square.";
    f := X^4 + A*X^2 + B;
    require IsIrreducible(f) :
        "Arguments must define an irreducible polynomial X^4 + A*X^2 + B.";
    K := NumberField(f);
    if IsSquare(B) then
        K`QuarticCMFieldType := [2,2];
    elif (4*B) mod D eq 0 and IsSquare((4*B) div D) then
        K`QuarticCMFieldType := [4];
    else
        K`QuarticCMFieldType := [8];
    end if;
    return K;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic QuarticCMFieldType(K::FldNum) -> SeqEnum
    {Given a quartic CM field, returns [2,2] for a biquadratic field, [4]
    for a cyclic field, and [8] for a non-normal (dihedral) field.}
    require IsQuarticCMField(K) : "Argument must be a quartic CM field.";
    if not assigned K`QuarticCMFieldType then
        /*
        Galois group computations are rather unstable in Magma when the
        group is far from the full symmetric group.  If the defining
        polynomial is already 'diagonalised' we can read off the group. 
        */
        f := DefiningPolynomial(K);
        if Coefficient(f,3) eq 0 and Coefficient(f,1) eq 0 then
            A := Coefficient(f,2);
            B := Coefficient(f,0);
            if IsSquare(B) then
                K`QuarticCMFieldType := [ 2, 2 ];
            elif IsSquare((A^2-4*B)*B) then
                K`QuarticCMFieldType := [ 4 ];
            else
                K`QuarticCMFieldType := [ 8 ];
            end if;
        elif IsNormal(K) then
            G := GaloisGroup(K);
            assert IsAbelian(G);
            K`QuarticCMFieldType := AbelianInvariants(G);
        else
            K`QuarticCMFieldType := [ 8 ];
        end if;
    end if;
    return K`QuarticCMFieldType;
end intrinsic;

intrinsic QuarticCMFieldInvariants(chi::RngUPolElt[RngInt]) -> SeqEnum
    {}
    require Degree(chi) eq 4 and IsIrreducible(chi) :
        "Argument must be an irreducible polynomial of degree 4.";
    K := NumberField(chi);
    require IsQuarticCMField(K) :
        "Argument must be a defining polynomial for a quartic CM field.";
    return QuarticCMFieldInvariants(K);
end intrinsic;

intrinsic QuarticCMFieldInvariants(K::FldNum) -> SeqEnum
    {Returns [D,A,B] such that K is isomorphic to the number field
    with defining polynomial X^4 + A*X^2 + B, with real quadratic
    subfield of discriminant D.  Note that A^2 - 4*B = m^2*D.} 
    require IsQuarticCMField(K) : "Argument must be a quartic CM field.";
    if assigned K`QuarticCMFieldInvariants then
        return K`QuarticCMFieldInvariants;
    end if;
    L, W := ImaginaryMinkowskiLattice(K);
    M := GramMatrix(L); assert M[1,1] le M[2,2] and M[1,2] ge 0;
    w0, w1 := Explode(W); w2 := w0-w1;
    /*
    if the field is not biquadratic then
       f1 is only necessary if the Gram matrix is [[2m,b],[b,2m]]
       f2 is only necessary if the Gram matrix M is [[2m,m],[m,2m]]
    if the field is biquadratic then
       f1 and f2 are need only if
          = f0 is linear, or
          = the Gram matrix [[2m,b],[b,2m]]
    */
    f0 := MinimalPolynomial(w0^2);
    f1 := MinimalPolynomial(w1^2);
    f2 := MinimalPolynomial(w2^2);
    ff := { fi : fi in [f0,f1,f2] | Degree(fi) eq 2 };
    A := Min([ Coefficient(fi,1) : fi in ff ]);
    B := Min([ Coefficient(fi,0) : fi in ff | Coefficient(fi,1) eq A ]);
    D := FundamentalDiscriminant(A^2-4*B);
    K`QuarticCMFieldInvariants := [D,A,B];
    return [D,A,B];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

/*
intrinsic QuarticCMFieldFromWengInvariants(Dab::SeqEnum[RngIntElt]) -> SeqEnum
    {}
    require #Dab eq 3 : "Argument must be a sequence of three integers.";
    D, a, b := Explode(Dab);
    require D gt 0 and D mod 4 in {0,1} and not IsSquare(D) :
        "First element of argument must be a positive discriminant.";
    t := D mod 4;
    n := (t^2-D) div 4;
    P<x> := PolynomialRing(RationalField());
    F<s> := NumberField(x^2+t*x+n);
    // Check that this is a quartic CM field!:
    require (2*a-t*b) gt 0 and (2*a-t*b)^2 gt b^2*D : "Argument must define a quartic CM field.";
    return NumberField(Evaluate(MinimalPolynomial(a+b*s),-x^2));
end intrinsic;

intrinsic QuarticCMFieldInvariantsFromWengInvariants(Dab::SeqEnum[RngIntElt]) -> SeqEnum
    {}
    require #Dab eq 3 : "Argument must be a sequence of three integers.";
    D := Dab[1];
    require D gt 0 and D mod 4 in {0,1} and not IsSquare(D) :
        "First element of argument must be a positive discriminant.";
    K := QuarticCMFieldFromWengInvariants(Dab);
    return QuarticCMFieldInvariants(K);
end intrinsic;
*/

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic QuarticCMReflexFields(K::FldNum) -> SeqEnum
    {}
    require IsQuarticCMField(K) : "Argument must be a quartic CM field.";
    t := QuarticCMFieldType(K);
    if t eq [2,2] then
        Flds := [ F[1] : F in Subfields(K,2) | Discriminant(F[1]) lt 0 ];
        Dscs := [ Discriminant(MaximalOrder(F)) : F in Flds ];
        return Dscs[1] lt Dscs[2] select Reverse(Flds) else Flds;
    elif t eq [4] then
        return [ K ];
    end if;
    X := PolynomialRing(RationalField()).1;
    _, A1, B1 := Explode(QuarticCMFieldInvariants(K));
    A2 := 2*A1; B2 := A1^2 - 4*B1;
    if A2 mod 4 eq 0 and B2 mod 16 eq 0 then
        A2 div:= 4;
        B2 div:= 16;
    end if;
    Kr := NumberField(X^4 + A2*X^2 + B2);
    Kr`IsCMField := true;
    Kr`TotallyRealSubfield := sub< Kr | Kr.1^2 >;
    Kr`QuarticCMFieldType := [8];
    return [ Kr ];
end intrinsic;

intrinsic QuarticCMReflexField(K::FldNum,deg::RngIntElt) -> FldNum
    {}
    require IsQuarticCMField(K) : "Argument must be a quartic CM field.";
    t := QuarticCMFieldType(K);
    if (t eq [4] and deg eq 4) or (t eq [8] and deg eq 8) then
        return QuarticCMReflexField(K);
    end if;
    require false : "Argument must have a unique reflex field of degree", deg;
end intrinsic;

intrinsic QuarticCMReflexField(K::FldNum) -> FldNum
    {}
    require IsQuarticCMField(K) : "Argument must be a quartic CM field.";
    t := QuarticCMFieldType(K);
    require t ne [2,2] : "Argument must not be a biquadratic quartic field.";
    if t eq [4] then
        return K;
    end if;
    X := PolynomialRing(RationalField()).1;
    _, A1, B1 := Explode(QuarticCMFieldInvariants(K));
    A2 := 2*A1; B2 := A1^2 - 4*B1;
    if A2 mod 4 eq 0 and B2 mod 16 eq 0 then
        A2 div:= 4;
        B2 div:= 16;
    end if;
    Kr := NumberField(X^4 + A2*X^2 + B2);
    Kr`IsCMField := true;
    Kr`TotallyRealSubfield := sub< Kr | Kr.1^2 >;
    Kr`QuarticCMFieldType := [8];
    return Kr;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Functions relating to primes of good ordinary reduction
//////////////////////////////////////////////////////////////////////////////

intrinsic QuarticCMFieldOrdinaryPrimes(chi::RngUPolElt[RngInt],n::RngIntElt : Degree := 0) -> SeqEnum
    {The sequence of tuples consisting of a prime p of good ordinary reduction,
    among the first n primes, with the degree of the extension of the finite
    prime field.}
    return QuarticCMFieldOrdinaryPrimes(NumberField(chi),n : Degree := Degree);
end intrinsic;

intrinsic QuarticCMFieldOrdinaryPrimes(K::FldNum,n::RngIntElt : Degree := 0) -> SeqEnum
    {The sequence of tuples consisting of a prime p of good ordinary reduction,
    among the first n primes, with the degree of the extension of the finite
    prime field.}
    prms := [ ];
    for p in Primes(n) do
        _, degs := QuarticCMFieldOrdinaryWeilNumbers(K,p);
        if Degree ne 0 then
            degs := [ d : d in degs | d eq Degree ];
        end if;
        if #degs gt 0 then
            Append(~prms,<p,degs>);
        end if;
    end for;
    return prms;
end intrinsic;

intrinsic QuarticCMFieldOrdinaryFrobeniusCharpolys(
    K::FldNum,p::RngIntElt,r::RngIntElt) -> SeqEnum, SeqEnum, SeqEnum
    {Returns a sequence of characteristic polynomials of Weil numbers in K.}
    pi_seq, deg_seq, units := QuarticCMFieldOrdinaryWeilNumbers(K,p);
    PZ := PolynomialRing(Integers());
    chi_seq1 := [ PZ | ];
    chi_seq2 := [ PZ | ];
    chi_seq4 := [ PZ | ];
    for i in [1..#pi_seq] do
        if r mod deg_seq[i] ne 0 then
            vprintf FldCM : "  Skipping Weil number of degree %o (looking for degree | %o)\n", deg_seq[i], r; continue;
        end if;
        s := r div deg_seq[i];
        pi := pi_seq[i]^s;
        for u in units do
            chi := MinimalPolynomial(u*pi);
            twog := Degree(chi);
            if twog eq 1 and chi notin chi_seq1 then
                Append(~chi_seq1,PZ!chi);
            elif twog eq 2 and chi notin chi_seq2 then
                Append(~chi_seq2,PZ!chi);
            elif twog eq 4 and chi notin chi_seq4 then
                Append(~chi_seq4,PZ!chi);
            end if;
        end for;
    end for;
    weights := [ 1 : chi in [1..#chi_seq1] ] cat [ 2 : chi in [1..#chi_seq2] ] cat [ 4 : chi in [1..#chi_seq4] ];
    chi_seq := chi_seq1 cat chi_seq2 cat chi_seq4;
    if #weights eq 0 then return [ PZ | ]; end if;
    PP := PolynomialRing(IntegerRing(),weights);
    mm := MonomialsOfWeightedDegree(PP,4);
    return [ m(chi_seq) : m in mm ];
end intrinsic;

intrinsic QuarticCMFieldOrdinaryWeilNumbers(K::FldNum,p::RngIntElt) ->
    SeqEnum, SeqEnum, SeqEnum
    {Returns a collection of primitive ordinary primitive Weil numbers
    in K, of norm p^2r for positive integers r.  Primitive is defined
    to be minimal r.  The second returned value is the sequence of
    exponents r.  The third returned value is the sequence of torsion units.
    The returned Weil numbers are complete up to complex conjugation 
    and units.}
    require IsQuarticCMField(K) : "Argument 1 must be a quartic CM field.";
    OK := MaximalOrder(K);
    G, m := ClassGroup(K);
    U, s := UnitGroup(OK);
    u1 := s(U.2); // fundamental unit
    units := [ K | s(U!u) : u in TorsionSubgroup(U) ];
    dcmp := Decomposition(OK,p);
    n := #dcmp;
    // There do not exist ordinary Weil numbers unless every prime
    // over p splits in the relative extension K/K_0.  In particular
    // the number of primes must be even (and partitioned into
    // complex conjugate pairs).
    if n mod 2 eq 1 then
        return [ K | ], [ Integers() | ], units;
    end if;
    one := ideal< OK | 1 >;
    prms := [ Parent(one) | ];
    qrms := [ Parent(one) | ];
    c := ComplexConjugation(K);
    for i in [1..#dcmp] do
        pp := dcmp[i][1];
        ei := dcmp[i][2];
        qq := c(pp);
        // Every prime must split in the relative extension for there to 
        // exist an ordinary Weil number -- and since pp ne qq (below),
        // the ramification index ei appears in the real subfield.
        if pp eq qq then
            return [ K | ], [ Integers() | ], units;
        elif pp notin qrms then
            Append(~prms,pp^ei);
            Append(~qrms,qq^ei);
        end if;
        if 2*#prms eq n then break i; end if;
    end for;
    // Hard code in the number of primes for quartic fields.
    if #prms eq 1 then
        p1 := prms[1];
        r1 := Order(p1@@m);
        bool, pi := IsPrincipal(p1^r1);
        weil := [ K | pi ];
        pows := [ 2*r1 ]; // prime is either ramified or inert
    elif #prms eq 2 then
        p1 := prms[1]*prms[2];
        r1 := Order(p1@@m);
        bool, pi1 := IsPrincipal(p1^r1); assert bool;
        p2 := prms[1]*qrms[2];
        r2 := Order(p2@@m);
        bool, pi2 := IsPrincipal(p2^r2); assert bool;
        weil := [ K | pi1, pi2 ];
        pows := [ 2*r1, 2*r2 ];
    end if;
    // Need to normalise by units so that elements are Weil numbers.
    for i in [1..#weil] do
        pi := weil[i];
        ri := pows[i];
        q := p^(ri div 2); assert ri mod 2 eq 0; // g = 2;
        // In principle we need only use one of the coordinates to determine
        // the exponent k such that u1^k*pi is a Weil number.
        log_pi := [ Log(Norm(c)/q) : c in Conjugates(pi) ];
        log_u1 := [ Log(Norm(c)) : c in Conjugates(u1) ];
        k2 := -Round(2*log_pi[1]/log_u1[1]);
        assert Abs(k2*log_u1[1] + 2*log_pi[1]) lt 0.01;
        if k2 mod 2 eq 1 then
            pows[i] *:= 2;
            weil[i] := u1^k2 * weil[i]^2;
        elif k2 ne 0 then
            k1 := k2 div 2;
            weil[i] *:= u1^k1;
        end if;
        if GetVerbose("FldCM") ge 1 then
            print "log_pi =", VectorSpace(RealField(8),4)!log_pi;
            print "log_u1 =", VectorSpace(RealField(8),4)!log_u1;
            print "k1 =", k2 div 2;
            print "k2 mod 2 =", k2 mod 2;
        end if;
    end for;
    return weil, [ ri div 2 : ri in pows ], units;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

