////////////////////////////////////////////////////////////////////////
//                       Auxilliary Function                          //
////////////////////////////////////////////////////////////////////////

procedure AssignNameToFiniteFieldGeneratorIfItAintAssignedAlready(k)
    assert Type(k) eq FldFin;
    s := Sprintf("%o",k.1);
    if s[[Max(#s-1,1)..#s]] eq ".1" then
	AssignNames(~k,["t"]);
    end if;
end procedure;

////////////////////////////////////////////////////////////////////////
//                        Structure Creation                          //
////////////////////////////////////////////////////////////////////////

intrinsic SupersingularModule(p::RngIntElt : Brandt := false) -> ModSS
    {}
    require p ge 2 and IsPrime(p) : "Argument 1 must be prime.";
    return SupersingularModule(p,1 : Brandt := Brandt);
end intrinsic;

intrinsic SupersingularModule(p::RngIntElt, N::RngIntElt : Brandt := false) -> ModSS
    {}
    require p ge 2 and IsPrime(p) : "Argument 1 must be prime.";
    require N ge 1: "The first argument must be at least 1.";
    require GCD(p,N) eq 1 : "Arguments 1 and 2 must be coprime.";

    AssignNameToFiniteFieldGeneratorIfItAintAssignedAlready(GF(p^2));
    M := New(ModSS);
    M`p := p;
    M`auxiliary_level := N;
    M`atkin_lehner_primes := [];
    M`atkin_lehner_operators := [];
    M`hecke_primes := [];
    M`hecke_operators := [];
    if N in {1,2,3,5,7,13} and not Brandt then
	M`uses_brandt := false;
    else
	M`uses_brandt := true;
    end if;
    return M;
end intrinsic;
