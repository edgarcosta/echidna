//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic NarrowClassGroup(OK::RngOrd) -> GrpAb, Map
    {}
    require IsMaximal(OK) : "Argument must be a maximal order.";
    r, s := Signature(NumberField(OK)); 
    require r gt 0 : "Argument must have a real infinite place.";
    return RayClassGroup(ideal< OK | 1 >,[1..r]);
end intrinsic;

intrinsic NarrowClassGroup(K::FldNum) -> RngIntElt
    {}
    return NarrowClassGroup(MaximalOrder(K));
end intrinsic;

intrinsic NarrowClassNumber(OK::RngOrd) -> RngIntElt
    {}
    require IsMaximal(OK) : "Argument must be a maximal order.";
    r, s := Signature(NumberField(OK)); 
    require r gt 0 : "Argument must have a real infinite place.";
    return #RayClassGroup(ideal< OK | 1 >,[1..r]);
end intrinsic;

intrinsic NarrowClassNumber(K::FldNum) -> RngIntElt
    {}
    return NarrowClassNumber(MaximalOrder(K));
end intrinsic;

intrinsic NarrowClassNumber(D::RngIntElt) -> RngIntElt
    {Returns the narrow class number of the maximal order O, number
    field K, or quadratic field of (fundamental) discriminant D.}
    require D gt 0 and D mod 4 in {0,1} and not IsSquare(D) and IsFundamental(D) : 
	"Argument must be a real fundamental discriminant of a quadratic field.";
    return NarrowClassNumber(MaximalOrder(QuadraticField(D)));
end intrinsic;

intrinsic NarrowClassField(K::FldNum) -> RngIntElt
    {}
    r, s := Signature(K);
    require r gt 0 : "Argument must have a real infinite place.";
    return NumberField(RayClassField(ideal< MaximalOrder(K) | 1 >,[1..r]));
end intrinsic;
