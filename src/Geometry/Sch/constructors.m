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

intrinsic Eltseq(X::Sch) -> SeqEnum
    {The sequence of defining polynomials for X.}
    return DefiningPolynomials(X);
end intrinsic;

intrinsic AffineScheme(I::RngMPol) -> Sch
    {}
    return Scheme(AffineSpace(Generic(I)),I);
end intrinsic;

intrinsic ProjectiveScheme(I::RngMPol) -> Sch
    {}
    require IsHomogeneous(I) : "Argument must be a homogeneous ideal.";
    return Scheme(ProjectiveSpace(Generic(I)),I);
end intrinsic;

intrinsic Curve(f::RngMPolElt) -> Crv
    {}
    R := Parent(f);
    if Rank(R) eq 2 then
	return Curve(AffineSpace(R),f);
    elif Rank(R) eq 3 then
	require IsHomogeneous(f) : "Argument must be homogeneous.";
	return Curve(ProjectiveSpace(R),f);
    end if;	
    require false :
	"Argument must be an element of a polynomial ring of rank 2 or 3.";
end intrinsic;

