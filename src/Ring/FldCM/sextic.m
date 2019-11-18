//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare attributes FldNum:
    SexticCMFieldType,
    SexticCMFieldInvariants,
    SexticCMReflexFieldInvariants;

intrinsic IsSexticCMField(K::FldNum) -> BoolElt
    {}
    return Degree(K) eq 6 and IsCMField(K);
end intrinsic;

intrinsic SexticCMField(DABC::[RngIntElt]) -> FldNum
    {Given an integer sequence [D,A,B,C] return the sextic CM field with
    defining polynomial X^6 + A*X^4 + B*X^2 + C.}
    require #DABC eq 4 : "Argument must consist of four elements";
    D, A, B, C := Explode(DABC);
    require D gt 0 : "Argument element 1 must be positive.";
    require A ge 0 and B ge 0 and C gt 0 : 
	"Argument elements 2, 3, and 4 must be positive.";
    require A^2 - 3*B ge 0 : 
	"Argument [D,A,B,C] must have A^2 - 3*B nonnegative.";
    D2 := -4*A^3*C + A^2*B^2 + 18*A*B*C - 4*B^3 - 27*C^2;
    require D2 mod D eq 0 and IsSquare(D2 div D): 
	"Argument elements(D, A, B, C), must satisfy disc(X^3+A*X^2+B*X+C) = m^2*D."; 
    return SexticCMField(D,A,B,C);
end intrinsic;

intrinsic SexticCMField(
    D::RngIntElt,A::RngIntElt,B::RngIntElt,C::RngIntElt) -> FldNum
    {Given integers [D,A,B,C] return the sextic CM field with
    defining polynomial X^6 + A*X^4 + B*X^2 + C.}
    require D gt 0 : "Argument element 1 must be positive.";
    require A ge 0 and B ge 0 and C gt 0 : 
	"Argument elements 2, 3, and 4 must be positive.";
    require A^2 - 3*B ge 0 : 
	"Argument [D,A,B,C] must have A^2 - 3*B nonnegative.";
    D2 := -4*A^3*C + A^2*B^2 + 18*A*B*C - 4*B^3 - 27*C^2;
    require D2 mod D eq 0 and IsSquare(D2 div D): 
	"Argument elements(D, A, B, C), must satisfy disc(X^3+A*X^2+B*X+C) = m^2*D."; 
    X := PolynomialRing(Integers()).1;
    f := X^6 + A*X^4 + B*X^2 + C;
    require IsIrreducible(f) :
	"Arguments must define an irreducible polynomial X^6 + A*X^4 + B*X^2 + C.";
    return NumberField(f);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic SexticCMFieldType(K::FldNum) -> SeqEnum
    {Given a sextic CM field K, returns [#H,#G/#H] where H is the Galois
    group of the totally real field and G is the Galois group of K.}
    require IsSexticCMField(K) : "Argument must be a sextic CM field.";
    if not assigned K`SexticCMFieldType then
	F := TotallyRealSubfield(K);
	G := GaloisGroup(K);
	H := GaloisGroup(F);
	K`SexticCMFieldType := [ #H, #G div #H ];
    end if;
    return K`SexticCMFieldType;
end intrinsic;

intrinsic SexticCMFieldInvariants(K::FldNum) -> SeqEnum
    {Returns [D,A,B,C] such that K is isomorphic to the number field
    with defining polynomial X^6 + A*X^3 + B*X^2 + C with real subfield
    of discriminant D.}
    require IsSexticCMField(K) : "Argument must be a sextic CM field.";
    L, B := ImaginaryMinkowskiLattice(K);
    f := MinimalPolynomial(B[1]);
    i := 1;
    a := Norm(L.i);
    while Degree(f) ne 6 and i lt 3 do
	i +:= 1;
	a := Norm(L.i);
	f := MinimalPolynomial(B[i]);
    end while;
    require Degree(f) eq 6 : "Argument must be a generic sextic CM field.";
    require i le 2 : "Argument must be a generic sextic CM field.";
    if i gt 1 or i eq 1 and Norm(L.2) eq a then
	S := ShortVectors(L,a,a);
	for T in S do
	    v := T[1];
	    g := MinimalPolynomial(&+[ v[i]*B[i] : i in [1..3] ]);
	    if Degree(g) eq 6 then
		assert Coefficient(g,4) eq Coefficient(f,4);
		for k in [2,0] do
		    if Coefficient(g,k) lt Coefficient(f,k) then
			vprint FldCM : "Replacing:", f;
			vprint FldCM : "     with:", g;
			f := g;
		    elif Coefficient(f,k) lt Coefficient(g,k) then
			break k;
		    end if;
		end for;
	    end if;
	end for;
    end if;
    F := TotallyRealSubfield(K);
    D := Discriminant(MaximalOrder(F));
    K`SexticCMFieldInvariants := [D] cat [ Coefficient(f,k) : k in [4,2,0] ];
    return K`SexticCMFieldInvariants;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic SexticCMReflexFields(K::FldNum) -> SeqEnum
    {}
    require IsSexticCMField(K) : "Argument must be a sextic CM field.";
    X := PolynomialRing(RationalField()).1;
    D1, A1, B1, C1 := Explode(SexticCMFieldInvariants(K));
    A2 := 4*A1;
    B2 := 6*A1^2 - 8*B1;
    C2 := 4*A1^3 - 16*A1*B1 + 64*C1;
    D2 := (A1^2 - 4*B1)^2;
    if A2 mod 4 eq 0 and B2 mod 16 eq 0 and C2 mod 64 eq 0 and D2 mod 256 eq 0 then
	A2 div:= 4;
	B2 div:= 16;
	C2 div:= 64;
	D2 div:= 256;
    end if;
    fZ := X^8 + A2*X^6 + B2*X^4 + C2*X^2 + D2;
    return [ NumberField(fi[1]) : fi in Reverse(Factorization(fZ)) | Degree(fi[1]) ne 1 ];
end intrinsic;

intrinsic SexticCMReflexField(K::FldNum,deg::RngIntElt) -> FldNum
    {}
    require IsSexticCMField(K) : "Argument must be a sextic CM field.";
    Flds := [ ];
    for K_r in SexticCMReflexFields(K) do
	if Degree(K_r) eq deg then
	    Append(~Flds,K_r);
	end if;
    end for;
    require #Flds eq 1 : "Argument must have a unique reflex field of degree", deg;
    return Flds[1];
end intrinsic;

intrinsic SexticCMReflexField(K::FldNum) -> FldNum
    {}
    require IsSexticCMField(K) : "Argument must be a sextic CM field.";
    t := SexticCMFieldType(K);
    // It could be natural to return K in the cyclic case, but the
    // reflex field could also be 
    // if t eq [3,2] then return K; end if;
    require t ne [3,2] : "Argument must be a generic CM field.";
    X := PolynomialRing(RationalField()).1;
    D1, A1, B1, C1 := Explode(SexticCMFieldInvariants(K));
    A2 := 4*A1;
    B2 := 6*A1^2 - 8*B1;
    C2 := 4*A1^3 - 16*A1*B1 + 64*C1;
    D2 := (A1^2 - 4*B1)^2;
    if A2 mod 4 eq 0 and B2 mod 16 eq 0 and C2 mod 64 eq 0 and D2 mod 256 eq 0 then
	A2 div:= 4;
	B2 div:= 16;
	C2 div:= 64;
	D2 div:= 256;
    end if;
    g := X^8 + A2*X^6 + B2*X^4 + C2*X^2 + D2;
    require IsIrreducible(g) : "Argument must be a generic CM field.";
    Kr := NumberField(g);
    Kr`IsCMField := true; 
    Kr`TotallyRealSubfield := sub< Kr | Kr.1^2 >;
    if t eq [3,8] then
	Kr`OcticCMFieldType := [12,2];
    elif t eq [6,8] then
	Kr`OcticCMFieldType := [24,2];
    else
	assert false;
    end if;
    Kr`OcticCMReflexFieldInvariants := [D1,A1,B1,C1];
    return Kr;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

/*
intrinsic SexticCMFieldOrdinaryFrobeniusCharpolys(
    K::FldNum,p::RngIntElt,r::RngIntElt) -> SeqEnum, SeqEnum, SeqEnum
    {Returns a sequence of characteristic polynomials of Weil numbers in K.
    KNOWN BUGS: For cyclic or biquadratic fields (type [2,2]) the field
    automorphisms are not taken into account.}
    pi_seq, deg_seq, units := SexticCMFieldOrdinaryWeilNumbers(K,p);
    PZ := PolynomialRing(Integers());
    chi_seq := [ PZ | ];
    abs_norm := 2*r; // g = 2
    for i in [1..#pi_seq] do
	if abs_norm mod deg_seq[i] eq 0 then
	    s := abs_norm div deg_seq[i];
	    pi := pi_seq[i]^s;
	    for u in units do
		chi := MinimalPolynomial(u*pi);
		twog := Degree(chi);
		if twog ne 4 then
		    chi := chi^(4 div twog);
		end if;
		if chi notin chi_seq then
		    Append(~chi_seq,PZ!chi);
		end if;
	    end for;
	end if;
    end for;
    return chi_seq;
end intrinsic;

intrinsic SexticCMFieldOrdinaryWeilNumbers(K::FldNum,p::RngIntElt) ->
    SeqEnum, SeqEnum, SeqEnum
    {Returns a collection of primitive ordinary primitive Weil numbers
    in K, of norm p^2r for positive integers r.  Primitive is defined
    to be minimal r.  The second returned value is the sequence of
    exponents r.  The third returned value is the sequence of torsion units.
    The returned Weil numbers are complete up to complex conjugation 
    and units.}
    require IsSexticCMField(K) : "Argument 1 must be a sextic CM field.";
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
    c := SexticCMFieldComplexConjugation(K);
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
    // Hard code in the number of primes for sextic fields.
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
	if GetVerbose("SexticCM") ge 1 then
	    print "log_pi =", VectorSpace(RealField(8),4)!log_pi;
	    print "log_u1 =", VectorSpace(RealField(8),4)!log_u1;
	    print "k1 =", k2 div 2;
	    print "k2 mod 2 =", k2 mod 2;
	end if;
    end for;
    return weil, pows, units;
end intrinsic;

*/
