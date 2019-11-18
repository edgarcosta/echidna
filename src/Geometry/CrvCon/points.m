//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//           Rational Points on Conics (syntax fix), created 2002           //
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

/*
Somewhat ambiguous whether the intrinsic should be called HasPoint
or HasRationalPoint, but provide the latter here.  The former may
be removed from documentation at some point.
*/

intrinsic RationalPoint(C::CrvCon) -> Pt
    {A point of the conic over the rationals, integers, or a
    finite field, if one exists.}
    require Type(BaseRing(C)) in {RngInt,FldRat,FldFin} :
        "Argument must be defined over the integers, rationals " *
        "or a finite field.";
    bool, P := HasRationalPoint(C);
    require bool : "Argument does not have a rational point";
    return P;
end intrinsic;

intrinsic ReducedPoint(C::CrvCon) -> Pt
    {A point of the conic over the rationals, integers, or a
    finite field, if one exists.}
    require Type(BaseRing(C)) in {RngInt,FldRat,FldFin} :
        "Argument must be defined over the integers, rationals " *
        "or a finite field.";
    bool, P := HasRationalPoint(C);
    require bool : "Argument does not have a rational point";
    return P;
end intrinsic;
