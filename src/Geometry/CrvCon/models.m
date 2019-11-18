//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                     ALTERNATIVE MODELS FOR CONICS                        //
//                       David Kohel, created 2002                          //
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

intrinsic LegendreModel(C1::CrvCon) -> CrvCon, MapIsoSch
    {A diagonalized or Legendre model aX^2+bY^2+cZ^2 for a conic,
    followed by the isomorphism.}
    PP := Ambient(C1);
    require Characteristic(BaseRing(PP)) ne 2 :
      "A Legendre model exists only in characteristic different from 2.";
    f0, M0 := LegendrePolynomial(C1);
    C0 := Conic(PP,f0);
    M1 := Adjoint(M0);
    eqns0 := [ &+[ M0[i,j]*PP.i : i in [1..3] ] : j in [1..3] ];
    eqns1 := [ &+[ M1[i,j]*PP.i : i in [1..3] ] : j in [1..3] ]; 
    return C0, iso< C1 -> C0 | eqns1, eqns0 >;
end intrinsic;

intrinsic ReducedLegendreModel(C1::CrvCon) -> CrvCon, MapIsoSch
    {A reduced Legendre model aX^2+bY^2+cZ^2 for a conic over Q, with 
    a, b, and c pairwise coprime, followed by the isomorphism.}
    PP := Ambient(C1);
    require Type(BaseRing(PP)) in {FldRat,RngInt} :
      "A reduced Legendre model exists only over Q or Z.";
    f0, M0 := ReducedLegendrePolynomial(C1);
    C0 := Conic(PP,f0);
    M1 := Adjoint(M0);
    eqns0 := [ &+[ M0[i,j]*PP.i : i in [1..3] ] : j in [1..3] ];
    eqns1 := [ &+[ M1[i,j]*PP.i : i in [1..3] ] : j in [1..3] ]; 
    return C0, iso< C1 -> C0 | eqns1, eqns0 >;
end intrinsic;
