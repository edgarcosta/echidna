////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    DECOMPOSITION OF LINEAR CODES                   //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
//                          Decompositions                            //
////////////////////////////////////////////////////////////////////////

intrinsic Decomposition(C::Code) -> SeqEnum
    {} 
    k := Dimension(C);
    if k eq 0 then
	return [ Parent(C) | ];
    elif k eq 1 then
	return [ C ];
    end if;
    val, D := IsIndecomposable(C);
    if val then 
	return [ C ];
    end if;
    E := Complement(C,D); 
    return Decomposition(D) cat Decomposition(E);
end intrinsic;

////////////////////////////////////////////////////////////////////////
// Direct Sum: The inverse operation to decomposition...              //
////////////////////////////////////////////////////////////////////////

intrinsic DirectSum(S::[Code]) -> Code
    {}
    t := #S;
    require t ge 1 : "Argument 1 must be nonempty.";
    if t eq 1 then
	return S[1];
    elif t eq 2 then
	return DirectSum(S[1],S[2]);
    end if;
    return DirectSum(S[1],DirectSum(S[2..t]));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                      Decomposition Booleans                        //
////////////////////////////////////////////////////////////////////////

intrinsic IsDecomposable(C::Code) -> BoolElt
    {} 
    val, D := IsIndecomposable(C);
    if val then
	return false, _;
    else 
	return true, D;
    end if;
end intrinsic;

function IndecomposableExtension(C,D0,E0)
    S0 := Support(D0);
    C1, h := PuncturedCode(C,S0);   
    k1 := Dimension(C1);
    E1 := PuncturedCode(E0,S0);   
    for i in [1..k1] do
	u1 := C1.i;
	if u1 notin E1 then
	    v1 := u1@@h;
	    break i;
	end if;
	assert i ne k1;
    end for;
    return SupportedSubcode(C,S0 join Support(v1));
end function;

intrinsic IsIndecomposable(C::Code) -> BoolElt
    {} 
    n := Length(C);
    k := Dimension(C);
    if k eq 1 then
	return true, _;
    end if;
    for i in [1..n] do
	V := AmbientSpace(C);
	if V.i in C then
	    return false, sub< C | V.i >;
	end if;
    end for; 
    // Initialize indecomposable subcode D and complement:
    D := sub< C | 0 >;
    E := D;
    // Extension of subcode by indecomposable:
    for i in [1..k-1] do
	D := IndecomposableExtension(C,D,E);
	assert Dimension(D) eq i; 
	// Test if D is a direct summand of C:
	E := Complement(C,D);
	if Dimension(D) + Dimension(E) eq k then
	    return false, D;
	end if;
    end for;
    return true, _;
end intrinsic;
