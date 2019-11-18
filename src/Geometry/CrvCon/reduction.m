//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                  Point Reduction on Conics (syntax fix)                  //
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

intrinsic IsHolzerReduced(p::Pt) -> BoolElt
    {For a point p on a conic, returns true if and only if the
    image of the point on the Legendre model satifies the bound
    of Holzer's Theorem.}
    require Type(Scheme(p)) eq CrvCon and 
        Type(Ring(Parent(p))) in {RngInt,FldRat}:
        "Argument must be a point on a conic over the rationals.";
    return IsReduced(p);
end intrinsic;
