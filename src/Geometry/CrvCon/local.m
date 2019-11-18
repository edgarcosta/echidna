//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                       LOCAL CONDITIONS FOR CONICS                        // 
//                           Created June 2002                              //
//         Copyright (C) 2002 David Kohel <kohel@maths.usyd.edu.au>         //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//                       Bad Prime and Discriminant                         //
//////////////////////////////////////////////////////////////////////////////

intrinsic BadPrimes(C::CrvCon) -> SeqEnum
    {The sequence of primes at which C has intrinsic bad reduction.}
    require Type(BaseRing(C)) eq FldRat :
	"The base ring of the argument must be the rationals.";
    return RamifiedPrimes(QuaternionAlgebra(C));
end intrinsic;

intrinsic Discriminant(C::CrvCon) -> RngIntElt
    {}
    A := Ambient(C);
    f := DefiningPolynomial(C);
    a11, a12, a13, a22, a23, a33 := Explode(
        [ MonomialCoefficient(f,A.i*A.j) : i, j in [1..3] | i le j ]);
    return 4*a11*a22*a33-a11*a23^2-a12^2*a33+a12*a13*a23-a13^2*a22;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                      Hilbert Norm Residue Symbol                         //
//////////////////////////////////////////////////////////////////////////////

intrinsic NormResidueSymbol(
    a::FldRatElt,b::FldRatElt,p::RngIntElt) -> RngIntElt
    {}
    require IsPrime(p : Proof := false) : "Argument 3 must be prime";
    return NormResidueSymbol(
        Numerator(a)*Denominator(a),Numerator(b)*Denominator(b),p);
end intrinsic;

intrinsic NormResidueSymbol(a::RngIntElt,b::RngIntElt,p::RngIntElt) -> RngIntElt
    {Returns 1 if ax^2 + by^2 represents a nonzero p-adic square, otherwise -1.}
    require IsPrime(p : Proof := false) : "Argument 3 must be prime";
    while a mod p^2 eq 0 do a div:= p^2; end while;
    while b mod p^2 eq 0 do b div:= p^2; end while;
    if p ne 2 and &or[ KroneckerSymbol(x,p) eq 1 : x in {a,b,a+b} ] then
	return 1;
    end if;
    if a mod p eq 0 then 
	if b mod p eq 0 then
	    return NormResidueSymbol(p,-(b div p),p) *
		NormResidueSymbol(a div p,b,p);
        elif p eq 2 and (b mod 4) eq 3 then
	    if KroneckerSymbol(a+b,p) eq -1 then 
		return -1;
	    end if;    
	elif KroneckerSymbol(b,p) eq -1 then 
	    return -1;
	end if;
    elif b mod p eq 0 then
	if p eq 2 and (a mod 4) eq 3 then
	    if KroneckerSymbol(a+b,p) eq -1 then 
		return -1;
	    end if;
	elif KroneckerSymbol(a,p) eq -1 then 
	    return -1;
	end if;
    elif p eq 2 and (a mod 4) eq 3 and (b mod 4) eq 3 then
	return -1;
    end if;
    return 1;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
