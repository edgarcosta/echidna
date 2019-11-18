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

intrinsic ClassGroup(f::RngUPolElt[RngInt]) -> GrpAb, Map
    {The class group of the maximal order of QQ(f).}
    require IsIrreducible(f) : "Argument must be irreducible.";
    return ClassGroup(NumberField(f));
end intrinsic;

intrinsic ClassGroup(f::RngUPolElt[FldRat]) -> GrpAb, Map
    {The class group of the maximal order of QQ(f).}
    require IsIrreducible(f) : "Argument must be irreducible.";
    return ClassGroup(NumberField(f));
end intrinsic;

intrinsic ClassNumber(f::RngUPolElt[RngInt]) -> RngIntElt
    {The class number of the maximal order of QQ(f).}
    require IsIrreducible(f) : "Argument must be irreducible.";
    return ClassNumber(NumberField(f));
end intrinsic;

intrinsic ClassNumber(f::RngUPolElt[FldRat]) -> RngIntElt
    {The class number of the maximal order of QQ(f).}
    require IsIrreducible(f) : "Argument must be irreducible.";
    return ClassNumber(NumberField(f));
end intrinsic;
