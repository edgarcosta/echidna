intrinsic BaseRing(M::ModSS) -> Rng
    {}
    return IntegerRing();
end intrinsic;

intrinsic Degree(P::ModSSElt) -> RngElt
    {}
    return &+Eltseq(P);
end intrinsic;

intrinsic Dimension(M::ModSS) -> RngIntElt
    {}
    if not assigned M`dimension then
	if IsAmbientSpace(M) then
	    if UsesBrandt(M) then
		M`dimension := Dimension(BrandtModule(M));
	    else
		M`dimension := #SupersingularPoints(M);
	    end if;
	else
	    assert assigned M`rspace;
	    M`dimension := Dimension(M`rspace);
	end if;
    end if;
    return M`dimension;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                          Level Invariants                          //
////////////////////////////////////////////////////////////////////////

intrinsic Prime(M::ModSS) -> RngIntElt
    {}
    return M`p;
end intrinsic;

intrinsic AuxiliaryLevel(M::ModSS) -> RngIntElt
    {}
    return M`auxiliary_level;
end intrinsic;

intrinsic Level(M::ModSS) -> RngIntElt
    {}
    return Prime(M) * AuxiliaryLevel(M);
end intrinsic;

