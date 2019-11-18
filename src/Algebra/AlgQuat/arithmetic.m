//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                     Arithmetic on Elements                               //
//  Copyright (C) 2000 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic CharacteristicPolynomial(x::AlgQuatElt) -> RngUPolElt
   {The characteristic polynomial of x.}
   f := MinimalPolynomial(x);
   return f^(2 div Degree(f));
end intrinsic;

intrinsic CharacteristicPolynomial(x::AlgQuatOrdElt) -> RngUPolElt
   {The characteristic polynomial of x.}
   f := MinimalPolynomial(x);
   return f^(2 div Degree(f));
end intrinsic;

intrinsic Coordinates(x::AlgQuatElt) -> SeqEnum
   {The coordinates of x with respect to the basis of its parent.}
   return Eltseq(x);
end intrinsic;

