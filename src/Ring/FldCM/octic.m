//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare attributes FldNum:
    OcticCMFieldType,
    OcticCMFieldInvariants,
    OcticCMReflexFieldInvariants;

intrinsic IsOcticCMField(K::FldNum) -> BoolElt
    {}
    return Degree(K) eq 8 and IsCMField(K);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic OcticCMField(Invs::[RngIntElt]) -> FldNum
    {Given an integer sequence Invs = [D,a,b,c,d] return the octic CM field
    with defining polynomial x^8 + a*x^6 + b*x^4 + c*x^2 + d, where D is
    the discriminant of the totally real subfield with defining polynomial
    x^4 + a*x^3 + b*x^2 + c*x + d.}
    require #Invs eq 5 : "Argument must consist of five elements";
    D, a, b, c, d := Explode(Invs);
    require D gt 0 : "Argument element 1 must be positive.";
    require a ge 0 and b ge 0 and c ge 0 and d ge 1 : 
	"Argument must consist of non-negative elements.";
    x := PolynomialRing(Integers()).1;
    g := x^4+a*x^3+b*x^2+c*x+d;
    D2 := Discriminant(g);
    require D2 mod D eq 0 and IsSquare(D2 div D): 
	"Argument elements (= D, a, b, d), must satisfy disc(x^4+a*x^3+b*x^2+c*x+d) = m^2*D."; 
    f := Evaluate(g,x^2);
    require IsIrreducible(f) :
	"Arguments must define an irreducible polynomial x^8+a*x^6+b*x^4+c*x^2+d.";
    return NumberField(f);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic OcticCMFieldInvariants(K::FldNum) -> SeqEnum
    {Returns [D,a1,a2,a3,a4] such that K is isomorphic to the number field
    with defining polynomial X^8 + a1*X^6 + a2*X^4 + a3*X^2 + a4 with real
    subfield of discriminant D.}
    require IsOcticCMField(K) : "Argument must be an octic CM field.";
    L, B := ImaginaryMinkowskiLattice(K);
    f := MinimalPolynomial(B[1]);
    i := 1;
    a := Norm(L.i);
    while Degree(f) ne 8 and i lt 4 do
	i +:= 1;
	a := Norm(L.i);
	f := MinimalPolynomial(B[i]);
    end while;
    require Degree(f) eq 8 : "Argument must be a generic octic CM field.";
    require i le 2 : "Argument must be a generic octic CM field.";
    if i gt 1 or i eq 1 and Norm(L.2) eq a then
	S := ShortVectors(L,a,a);
	for T in S do
	    v := T[1];
	    g := MinimalPolynomial(&+[ v[i]*B[i] : i in [1..4] ]);
	    if Degree(g) eq 8 then
		assert Coefficient(g,6) eq Coefficient(f,6);
		for k in [4,2,0] do
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
    K`OcticCMFieldInvariants := [D] cat [ Coefficient(f,k) : k in [6,4,2,0] ];
    return K`OcticCMFieldInvariants;
end intrinsic;

intrinsic OcticCMReflexFields(K::FldNum : Precision := 128) -> SeqEnum
    {}
    require IsOcticCMField(K) : "Argument must be an octic CM field.";
    if assigned K`OcticCMReflexFieldInvariants then
	Invs := K`OcticCMReflexFieldInvariants;
	if #Invs eq 4 then
	    D, A, B, C := Explode(Invs);
	    X := PolynomialRing(IntegerRing()).1;
	    Kr := NumberField(X^6 + A*X^4 + B*X^2 + C);
	    Kr`IsCMField := true; 
	    Kr`SexticCMFieldInvariants := Invs;
	    Kr`TotallyRealSubfield := sub< Kr | Kr.1^2 >;
	    return [ Kr ];
	else
	    require false : "Unrecognized OcticCMReflexFieldInvariants.";
	end if;
    end if;
    prec := Precision;
    Invs := OcticCMFieldInvariants(K);
    D, a, b, c, d := Explode(Invs);
    RR := RealField(prec); 
    CC := ComplexField(prec);
    PR := PolynomialRing(RR);
    PC := PolynomialRing(CC); t := PC.1;
    g := Polynomial([d,c,b,a,1]);
    Phi := [ Sqrt(CC!r[1]) : r in Roots(PR!g) ];
    rC := [ &+[ e[i]*Phi[i] : i in [1..4] ] : e in CartesianPower({1,-1},4) ];
    fZ := Polynomial([ Round(Real(c)) : c in Eltseq(&*[ t-r : r in rC ]) ]);
    return [ NumberField(fi[1]) : fi in Reverse(Factorization(fZ)) | Degree(fi[1]) ne 1 ];
end intrinsic;

intrinsic OcticCMReflexField(K::FldNum,deg::RngIntElt) -> SeqEnum
    {}
    Flds := [ ];
    for K_r in OcticCMReflexFields(K) do
	if Degree(K_r) eq deg then
	    Append(~Flds,K_r);
	end if;
    end for;
    require #Flds eq 1 :
	"Argument must have a unique reflex field of degree", deg;
    return Flds[1];
end intrinsic;

intrinsic OcticCMReflexField(K::FldNum) -> SeqEnum
    {}
    Flds := OcticCMReflexFields(K);
    require #Flds eq 1 : "Argument must have a unique reflex field.";
    return Flds[1];
end intrinsic;

intrinsic OcticCMFieldType(K::FldNum) -> SeqEnum
    {Given a octic CM field K, returns [#H,#G/#H] where H is the Galois
    group of the totally real field and G is the Galois group of K.}
    require IsOcticCMField(K) : "Argument must be an octic CM field.";
    if not assigned K`OcticCMFieldType then
	F := TotallyRealSubfield(K);
	G := GaloisGroup(K);
	H := GaloisGroup(F);
	K`OcticCMFieldType := [ #H, #G div #H ];
    end if;
    return K`OcticCMFieldType;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

