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
    O::AlgQuatOrd : Bound := 8, Primitive := false) -> AlgQuatOrdElt
    {A random element of the quaternion order.}
    // Input: O quaternion order
    // Output: A random element with coordinates in [-Bound..Bound]
    v := [ Random([-Bound..Bound]) : i in [1..4] ];
    if Primitive eq true then
        v := [ a div m : a in v ] where m := GCD(v);
    end if;
    return O!v;
end intrinsic;

intrinsic RandomElement(
    I::AlgQuatOrdIdl : Bound := 8, Primitive := false) -> AlgQuatOrdElt
    {A random element of the quaternion ideal.}
    // Input: I quaternion ideal
    // Output: A random element with coordinates in [-Bound..Bound]
    O := Order(I);
    v := [ Random([-Bound..Bound]) : i in [1..4] ];
    if Primitive eq true then
        v := [ a div m : a in v ] where m := GCD(v);
    end if;
    B := Basis(I);
    return O!&+[ v[i]*B[i] : i in [1..4] ];
end intrinsic;

