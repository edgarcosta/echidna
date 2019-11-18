////////////////////////////////////////////////////////////////////////
//                      Chinese Remainder Theorem                     //
////////////////////////////////////////////////////////////////////////

intrinsic CRT(X::[RngUPolElt],M::[RngUPolElt]) -> RngUPolElt, RngUPolElt
    {Returns the CRT lift of the sequence of polynomials X with 
    respect to the sequence of moduli M, followed by the LCM of M.}
    n := #X;
    require n gt 0 : "Arguments must have positive length.";
    require n eq #M : "Arguments must have the same length.";
    PP := Universe(X);
    require PP eq Universe(M) : "Arguments must have the same universes.";
    require IsField(BaseRing(PP)) :
        "The base ring of sequence universes must be a field.";
    if n eq 1 then
	return X[1] mod M[1], M[1];
    elif n eq 2 then
	m, a, b := XGCD(M[1],M[2]);
	require (X[1]-X[2]) mod m eq 0 :
	   "Arguments do not determine a consistent remainder system.";
 	g := (X[1]*b*(M[2] div m) + X[2]*a*(M[1] div m));
	return g mod m0, m0 where m0 := M[1]*(M[2] div m);
    else
	i := n div 2;
	g, m1 := CRT(X[[1..i]],M[[1..i]]);
	h, m2 := CRT(X[[i+1..n]],M[[i+1..n]]);
	return CRT([g,h],[m1,m2]);
    end if;
end intrinsic;
