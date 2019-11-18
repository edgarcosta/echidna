intrinsic BadPlaces(E::CrvEll) -> SeqEnum
    {The places of bad reduction for E.}
    K := BaseRing(E);
    require Type(K) in {FldNum, FldQuad, FldCyc} : 
        "Argument must be defined over a number field.";
    if not assigned E`BadPlaces then 
        E`BadPlaces := Support(Divisor(Discriminant(E)));
    end if;
    return E`BadPlaces; 
end intrinsic;

intrinsic BadPlaces(E::CrvEll,K::FldNum) -> SeqEnum
    {The places of K of bad reduction for E.}
    if K cmpeq BaseRing(E) then return BadPlaces(E); end if;
    bool, d := IsCoercible(K,Discriminant(E));
    require bool : "Base field of argument 1 must extend to argument 2.";
    EK := E(K);
    if not assigned EK`BadPlaces then
	bool, d := IsCoercible(K,Discriminant(E));
        EK`BadPlaces := Support(Divisor(d));
    end if;
    EK`EK := EK; 
    return EK`BadPlaces;
end intrinsic;
