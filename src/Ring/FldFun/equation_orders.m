////////////////////////////////////////////////////////////////////////
//                    Coordinate Equation Orders                      //
////////////////////////////////////////////////////////////////////////

intrinsic EquationOrder(K::FldFun,i::RngIntElt) -> RngMPolRes, Map
    {The equation order of K associated to the the ith affine patch.}

    require i in {1,2,3} : "Argument 2 must be an integer in {1,2,3}.";
    C := Curve(K);
    R := CoordinateRing(AffinePatch(C,i));
    x := K.1; y := K.2; z := K!1;
    if i eq 1 then
	imags := [x/z,y/z];
    elif i eq 2 then
	imags := [x/y,1/y];
    else
	imags := [y/x,z/x];
    end if;
    return R, hom< R -> K | imags >;
end intrinsic;


