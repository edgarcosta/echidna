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

intrinsic '^'(phi::MapSch,n::RngIntElt) -> MapSch
    {}
    require Domain(phi) cmpeq Codomain(phi) : 
	"Argument 1 must be an endomorphism.";
    require n ge 0 or IsIsomorphism(phi) :  
	"Argument 2 must be a nonnegative integer.";
    if n lt 0 then
	n *:= -1;
	phi := Inverse(phi);
    elif n eq 0 then
	return IdentityMap(Domain(phi));
    end if;
    if n eq 1 then
	return phi;
    end if;
    phi_m := phi^(n div 2);
    phi_2m := phi_m * phi_m;
    if n mod 2 eq 0 then
	return phi_2m;
    else
	return phi_2m * phi;
    end if;
end intrinsic;

intrinsic Eltseq(phi::MapSch) -> MapSch
    {}
    return AllDefiningPolynomials(phi);
end intrinsic;
