////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    Hessian Subscheme of a Curve                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic HessianSubscheme(C::Crv) -> Rng
    {}
    require IsProjective(C) : "Argument must be a projective curve.";
    f := Determinant(HessianMatrix(C));
    return C meet Scheme(Ambient(C),f);
end intrinsic;

intrinsic WeierstrassPlaces(C::Crv) -> SeqEnum
    {}
    FC := AlgorithmicFunctionField(FunctionField(C));
    return [ CurvePlace(C,pp) : pp in WeierstrassPlaces(FC) ];
end intrinsic;

