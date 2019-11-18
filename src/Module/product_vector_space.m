//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//         Copyright (C) 2010 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic ProductSpace(U::ModTupFld,r::RngIntElt) -> ModTupFld
    {The r-fold product vector space.}
    F := BaseField(U);
    V := VectorSpace(F,r*Degree(U));
    B := BasisMatrix(U);
    Z := Parent(B)!0;
    return sub< V | &cat[ Rows(HorizontalJoin([ i eq j select B else Z : j in [1..r] ])) : i in [1..r] ] >;
end intrinsic;

intrinsic ProductSpace(U::ModTupRng,r::RngIntElt) -> ModTupRng
    {The r-fold module product.}
    F := BaseField(U);
    V := VectorSpace(F,r*Degree(U));
    B := BasisMatrix(U);
    Z := Parent(B)!0;
    return sub< V | &cat[ Rows(HorizontalJoin([ i eq j select B else Z : j in [1..r] ])) : i in [1..r] ] >;
end intrinsic;

