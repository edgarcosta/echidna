////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    Arithmetic operations, etc.                     //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function init_ModBrdtElt(M,v)
    // _, v := IsCoercible(Representation(M),v);
    x := New(ElementType(M));
    x`Parent := M;
    x`Element := v;
    return x;
end function;

intrinsic '*'(a::RngElt,x::ModBrdtElt) -> ModBrdtElt
    {}
    M := Parent(x);
    require Type(Parent(a)) eq RngInt or 
        Parent(a) cmpeq BaseRing(M) : "Elements have different parents."; 
    z := New(Type(x));
    z`Parent := M;
    z`Element := a*x`Element;
    return z;
end intrinsic;

intrinsic '*'(x::ModBrdtElt,T::AlgMatElt) -> ModBrdtElt
    {}
    M := Parent(x);
    require Type(BaseRing(Parent(T))) eq RngInt or 
        BaseRing(Parent(T)) eq BaseRing(M) : 
        "Arguments have different coefficient rings."; 
    // Assume that internal representation is via ambient module.
    if Degree(Parent(T)) eq Degree(M) then
        return init_ModBrdtElt(M,x`Element * T);
    elif Degree(Parent(T)) eq Dimension(M) then
        U := M`Module;
        B := BasisMatrix(M);
        y := ( Vector(Coordinates(U,x`Element)) * T ) * B;
        return init_ModBrdtElt(M,y);
    end if;
    require false : "Arguments have incompatible degrees."; 
end intrinsic;

intrinsic '*'(x::ModBrdtElt,a::RngElt) -> ModBrdtElt
    {}
    M := Parent(x);
    require Type(Parent(a)) eq RngInt or 
        Parent(a) cmpeq BaseRing(M) : "Elements have different parents."; 
    z := New(Type(x));
    z`Parent := M;
    z`Element := a*x`Element;
    return z;
end intrinsic;

intrinsic '+'(x::ModBrdtElt,y::ModBrdtElt) -> ModBrdtElt
    {}
    M := Parent(x);
    require Parent(y) eq M : "Elements have different parents."; 
    return init_ModBrdtElt(M,x`Element + y`Element);
end intrinsic;

intrinsic '-'(x::ModBrdtElt,y::ModBrdtElt) -> ModBrdtElt
    {}
    M := Parent(x);
    require Parent(y) eq M : "Elements have different parents."; 
    return init_ModBrdtElt(M,x`Element - y`Element);
end intrinsic;

