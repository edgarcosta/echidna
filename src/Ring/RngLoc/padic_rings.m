////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     Functionality for Local Rings                  //
//                           David Kohel                              //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic ResidueCharacteristic(S::RngPad) -> RngIntElt
    {}
    return Characteristic(ResidueClassField(S));
end intrinsic;

intrinsic ResidueCharacteristic(S::RngPadRes) -> RngIntElt
    {}
    return Characteristic(ResidueClassField(S));
end intrinsic;

intrinsic ResidueCharacteristic(S::RngPadResExt) -> RngIntElt
    {}
    return Characteristic(ResidueClassField(S));
end intrinsic;

intrinsic Characteristic(S::RngPadRes) -> RngIntElt
    {}
    return Characteristic(ResidueClassField(S))^Precision(S);
end intrinsic;

intrinsic Characteristic(S::RngPadResExt) -> RngIntElt
    {}
    return Characteristic(ResidueClassField(S))^Precision(S);
end intrinsic;

/*
intrinsic O(x::RngIntElt) -> RngPadElt
    {}
    bool, p, n := IsPrimePower(x);
    require bool : "Argument must be prime.";
    return O(pAdicRing(p)!p)^n;
end intrinsic;

intrinsic O(p::RngIntElt,n::RngIntElt) -> RngPadElt
    {}
    require IsPrime(p) : "Argument 1 must be prime.";
    require n ge 0 : "Argument 2 must be positive.";
    return O(pAdicRing(p)!p)^n;
end intrinsic;
*/

intrinsic ResidueCharacteristic(R::RngPadRes) -> RngIntElt
    {}
    return Prime(R);
end intrinsic;
    
intrinsic ResidueCharacteristic(R::RngPadResExt) -> RngIntElt
    {}
    return Prime(R);
end intrinsic;
    
intrinsic '/'(x::RngPadResElt, y::RngPadResElt) -> RngPadResElt
    {}
    bool, u := IsInvertible(y);
    require bool : "Argument 2 must be invertible.";
    return x*u;
end intrinsic;

intrinsic '/'(x::RngPadResExtElt, y::RngPadResExtElt) -> RngPadResExtElt
    {}
    bool, u := IsInvertible(y);
    require bool : "Argument 2 must be invertible.";
    return x*u;
end intrinsic;
