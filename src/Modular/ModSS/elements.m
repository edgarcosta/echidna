////////////////////////////////////////////////////////////////////////
//                             Coercion                               //
////////////////////////////////////////////////////////////////////////

function CreateModSSElt(M, v)
    assert Type(M) eq ModSS;
    assert Type(v) eq ModTupRngElt;
    assert v in RSpace(M);
    P := New(ModSSElt);
    P`parent := M;
    P`element := v;
    return P;
end function;

function CopyOfModSSElt(P)
    return CreateModSSElt(Parent(P),P`element);
end function;

intrinsic IsCoercible(M::ModSS,P::.) -> BoolElt, ModSSElt
    {Coerce P into M.}
    case Type(P):
    when ModSSElt:
	if Parent(P) subset M then
	    Q := CopyOfModSSElt(P);
	    Q`parent := M;
	    return true, Q;
	end if;
	else:
	    val, el := IsCoercible(RSpace(M),P);
	if val then
	    return true, CreateModSSElt(M,el);
	end if;
    end case;
    return false, "Illegal coercion";
end intrinsic;

intrinsic Parent(P::ModSSElt) -> ModSS
    {}
    return P`parent;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                         Basis Elements                             //
////////////////////////////////////////////////////////////////////////

intrinsic Basis(M::ModSS) -> SeqEnum
    {}
    if not assigned M`basis then
	W := RSpace(M);
	M`basis := [ M!b : b in Basis(W) ];
    end if;
    return M`basis;
end intrinsic;

intrinsic '.'(M::ModSS, i::RngIntElt) -> ModSSElt
    {}
    requirege i, 1;
    require i le Dimension(M) :
	"Argument 2 can be at most the dimension of argument 1.";
    return Basis(M)[i];
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                        Coordinate Access                           //
////////////////////////////////////////////////////////////////////////

intrinsic Eltseq(P::ModSSElt) -> SeqEnum
    {}
    return Eltseq(P`element);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                            Equality                                //
////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(P::ModSSElt, Q::ModSSElt) -> BoolElt
    {}
    return AmbientSpace(Parent(P)) eq AmbientSpace(Parent(Q)) and 
	Eltseq(P) eq Eltseq(Q);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                    Element Arithmetic Functions                    //
////////////////////////////////////////////////////////////////////////

intrinsic '-'(P::ModSSElt) -> ModSSElt
    {}
    return Parent(P)!(-P`element);
end intrinsic;

intrinsic '-'(P::ModSSElt, Q::ModSSElt) -> ModSSElt
    {}
    require AmbientSpace(Parent(P)) eq AmbientSpace(Parent(Q)) : 
	"Incompatible parents.";
    return P + -Q;
end intrinsic;

intrinsic '+'(P::ModSSElt, Q::ModSSElt) -> ModSSElt
    {}
    require AmbientSpace(Parent(P)) eq AmbientSpace(Parent(Q)) : 
	"Incompatible parents.";
    element := P`element+Q`element;
    if element in RSpace(Parent(P)) then
	return Parent(Parent(P))!element;
    elif element in RSpace(Parent(Q)) then
	return Parent(Parent(Q))!element;
    else
	return AmbientSpace(Parent(P))!element;
    end if;
end intrinsic;

intrinsic '*'(a::RngElt, P::ModSSElt) -> ModSSElt
    {} 
    val, el := IsCoercible(Integers(),a);
    require val : "Argument 1 must be coercible into the integers.";
    return Parent(P)!(el*P`element);
end intrinsic;

