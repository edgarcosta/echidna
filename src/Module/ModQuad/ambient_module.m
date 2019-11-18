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

intrinsic AmbientModule(M::ModTupRng) -> ModTupRng
    {The ambient module of M (of degree Degree(M)).}
    return Generic(M);
end intrinsic;

intrinsic AmbientSpace(M::ModTupRng) -> ModTupFld
    {}
    R := BaseRing(M);
    K := FieldOfFractions(R);
    A := ChangeRing(InnerProductMatrix(M),K);
    V := RSpace(K,Degree(M),A);
    return sub< V | [ V!Eltseq(x) : x in Basis(M) ] >;
end intrinsic;

