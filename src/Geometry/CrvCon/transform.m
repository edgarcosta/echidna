//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                    CONIC MODELS FOR GENUS ZERO CURVES                    //
//                      David Kohel, created June 2002                      //   
//         Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu.au>         //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic Conic(C::Crv) -> CrvCon, MapIsoSch
    {The conic C1 given by the (anti-)canonical embedding 
    of the genus zero curve C in the projective plane,
    followed by the birational isomorphism from C to C1.}
    // First see if there is an easy way out:
    bool, C1 := IsConic(C);
    if bool then
	funs := [P2.i : i in [1..3]] where P2 := Ambient(C);
	return C1, map< C -> C1 | funs, funs >;
    end if;
    K := BaseRing(C); 
    require IsField(K) : "Base ring of argument must be a field.";
    require IsProjective(C) : "Argument must be a projective model.";
    require IsIrreducible(C) and IsReduced(C) :
       "Argument must be irreducible and reduced";
    require Genus(C) eq 0 : "Argument must have genus 0";
    D := -CanonicalDivisor(C);
    V, m := RiemannRochSpace(D);
    assert Dimension(V) eq 3; 
    fncs := [ m(V.i) : i in [1..3] ];
    phi := map< C -> Ambient(C) | fncs >;
    bool, C0 := IsConic(phi(C));
    return C0, Restriction(phi,C,C0);
end intrinsic;

