//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//        Copyright (C) 2013 David Kohel <David.Kohel@univ-amu.fr>          //
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
// Normalize a polynomial with respect to the leading coefficient 
// or a given monomial.
//////////////////////////////////////////////////////////////////////////////

intrinsic NormalizeSequence(X::SeqEnum[RngMPolElt]) -> SeqEnum
    {Normalize the sequence of multivariate polynomials such that
    the first coordinate is monic in the leading monomial.}
    return NormalizeSequence(X,1);
end intrinsic;

intrinsic NormalizeSequence(X::SeqEnum[RngMPolElt],i::RngIntElt) -> SeqEnum
    {Normalize the sequence of multivariate polynomials such that
    the i-th coordinate is monic in the leading monomial.}
    bool, u := IsInvertible(Coefficients(X[i])[1]);
    require bool : "Argument must have unit leading coefficient.";
    return [ u*f : f in X ];
end intrinsic;

intrinsic NormalizeSequence(X::SeqEnum[RngMPolElt],i::RngIntElt,m::RngMPolElt) -> SeqEnum
    {Normalize the sequence of multivariate polynomials such that
    the i-th coordinate is monic in the monomial m .}
    bool, u := IsInvertible(Coefficients(X[i])[1]);
    require bool : "Argument must have unit monomial coefficient.";
    return [ u*f : f in X ];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Normalize a polynomial with respect to the leading coefficient 
// or a given monomial.
//////////////////////////////////////////////////////////////////////////////

intrinsic NormalizePolynomial(f::RngMPolElt) -> RngMPolElt
    {}
    bool, u := IsInvertible(Coefficients(f)[1]);
    require bool : "Argument must have unit leading coefficient.";
    return u*f;
end intrinsic;

intrinsic NormalizePolynomial(f::RngMPolElt,m::RngMPolElt) -> RngMPolElt
    {}
    bool, u := IsInvertible(MonomialCoefficient(f,m));
    require bool : "Argument must have unit monomial coefficient.";
    return u*f;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Normalize a sequence of field elements with respect to a coordinate.
//////////////////////////////////////////////////////////////////////////////

intrinsic NormalizePoint(P::SeqEnum[FldElt],i::RngIntElt) -> SeqEnum
    {Normalize a sequence (as a projective point) with respect to a given coordinate.}
    require 1 le i and i le #P :
	"Argument 2 must be between 1 and the length of argument 1.";
    bool, u := IsInvertible(P[i]);
    require bool : "Argument coefficient be invertible.";
    return [ u*f : f in P ];
end intrinsic;

