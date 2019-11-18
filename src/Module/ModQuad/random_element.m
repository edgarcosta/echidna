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

intrinsic RandomElement(
    M::ModTupRng[RngInt] : Bound := 8, Primitive := false) -> ModTupRngElt
    {A random element of the quadratic module.}
    // Input: M quadratic module
    // Output: A random element with coordinates in [-Bound..Bound]
    r := Rank(M);
    v := [ Random([-Bound..Bound]) : i in [1..r] ];
    if Primitive eq true then
        v := [ a div m : a in v ] where m := GCD(v);
    end if;
    B := Basis(M);
    return &+[ v[i]*B[i] : i in [1..r] ];
end intrinsic;

