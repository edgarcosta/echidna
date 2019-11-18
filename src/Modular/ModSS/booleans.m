////////////////////////////////////////////////////////////////////////
//                      Boolean Invariants                            //
////////////////////////////////////////////////////////////////////////

intrinsic UsesBrandt(M::ModSS) -> BoolElt
    {}
    if not IsAmbientSpace(M) then
	return UsesBrandt(AmbientSpace(M));
    end if;
    return M`uses_brandt;
end intrinsic;

intrinsic UsesMestre(M::ModSS) -> BoolElt
    {}
    if not IsAmbientSpace(M) then
	return UsesMestre(AmbientSpace(M));
    end if;
    
    return not UsesBrandt(M);
end intrinsic;

intrinsic IsAmbientSpace(M::ModSS) -> BoolElt
    {}
    return not assigned M`ambient_space;
end intrinsic;

