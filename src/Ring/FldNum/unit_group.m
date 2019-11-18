//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic FundamentalUnit(K::FldNum) -> FldNumElt
    {Returns a sequence generator for the free part for a unit group of rank 1.}
    rank := r+s-1 where r, s := Signature(K);
    require rank eq 1 : "Argument must have unit rank one.";
    return FundamentalUnit(MaximalOrder(K));
end intrinsic;

intrinsic FundamentalUnit(O::RngOrd) -> FldNumElt
    {Returns a sequence generator for the free part for a unit group of rank 1.}
    rank := r+s-1 where r, s := Signature(O);
    require rank eq 1 : "Argument must have unit rank one.";
    U, m := UnitGroup(O);
    assert Ngens(U) eq 2 and Order(U.1) ne 0 and Order(U.2) eq 0; 
    return m(U.2);
end intrinsic;

intrinsic FundamentalUnits(K::FldNum) -> SeqEnum
    {Returns a sequence of generators for the free part for a unit group of rank 1.}
    return FundamentalUnits(MaximalOrder(K));
end intrinsic;

intrinsic FundamentalUnits(O::RngOrd) -> SeqEnum
    {Returns a sequence of generators for the free part for a unit group of rank 1.}
    rank := r+s-1 where r, s := Signature(O);
    U, m := UnitGroup(O);
    assert Ngens(U) eq rank+1 and Order(U.1) ne 0 and &and[ Order(U.(i+1)) eq 0 : i in [1..rank] ];
    return [ m(U.(i+1)) : i in [1..rank] ];
end intrinsic;

