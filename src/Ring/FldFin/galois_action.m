//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic GaloisImage(x::FldFinElt,i::RngIntElt) -> FldFinElt
    {The image of x under the i-th power Frobenius automorphism.}
    F := Parent(x);
    return x^(p^(i mod d)) where p := Characteristic(F) where d := Degree(F);
end intrinsic;
