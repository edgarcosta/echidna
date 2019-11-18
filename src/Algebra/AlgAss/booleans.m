////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic IsOrder(A::AlgAss) -> BoolElt
    {True iff A is an integral order in a ***simple*** algebra.}
    if BaseRing(A) cmpne Integers() or not IsUnitary(A) then
	return false;
    elif not assigned A`AmbientAlgebra then
	A`AmbientAlgebra := BaseChange(A,Rationals());
    end if;
    return IsSimpleXXX(A`AmbientAlgebra);
end intrinsic;

intrinsic IsSimpleXXX(A::AlgAss) -> BoolElt
    {}
    require IsField(BaseRing(A)) :
	"Argument must be an algebra over an order.";
    if Type(BaseRing(A)) eq FldFin then
	return IsSimple(A);
    end if;
    if not assigned A`IsSimple then
	A`IsSimple := Dimension(JacobsonRadical(A)) eq 0;
	A`IsSimple := A`IsSimple and #Decomposition(A) eq 1;
    end if;
    return A`IsSimple;
end intrinsic;

intrinsic IspMaximal(A::AlgAss,p::RngIntElt) -> BoolElt
    {}
    require BaseRing(A) cmpeq Integers() :
	"Argument must be defined over the integers.";
    assert false; // not implemented
    FF := FiniteField(p);
    for i in [1..Dimension(A)] do
	Q := LeftStructureConstants(A,i) cat 
	    RightStructureConstants(A,i);
	bool := &and[ c mod p eq 0 : c in Q ] and Q[i] mod p^2 eq 0;
	if bool then
	    return false;
	end if;
    end for;
    return true;
end intrinsic;

intrinsic IsMaximal(A::AlgAss) -> BoolElt
    {}
    require BaseRing(A) cmpeq Integers() :
	"Argument must be defined over the integers.";
    assert false; // not implemented
    return true;
end intrinsic;

intrinsic IsCentral(A::AlgAss) -> BoolElt
    {True iff the base ring of A equals the center.}
    return Dimension(Center(A)) eq 1;
end intrinsic;
