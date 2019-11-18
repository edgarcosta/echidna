
intrinsic Factorization(f::FldFunRatUElt) -> SeqEnum
    {The factorization of f.}
    require f ne 0 : "Argument must be nonzero.";
    D := Factorization(Denominator(f));
    return Factorization(Numerator(f)) cat [ <P[1],-P[2]> : P in D ];
end intrinsic;

intrinsic Factorization(f::FldFunRatMElt) -> SeqEnum
    {The factorization of f.}
    require f ne 0 : "Argument must be nonzero.";
    D := Factorization(Denominator(f));
    return Factorization(Numerator(f)) cat [ <P[1],-P[2]> : P in D ];
end intrinsic;

intrinsic Factorization(x::FldRatElt) -> SeqEnum
    {The factorization of x.}
    require x ne 0 : "Argument must be nonzero.";
    D := Factorization(Denominator(x));
    return Factorization(Numerator(x)) cat [ <P[1],-P[2]> : P in D ];
end intrinsic;

