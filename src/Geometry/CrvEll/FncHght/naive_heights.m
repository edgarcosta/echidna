////////////////////////////////////////////////////////////////////////
// Naive heights.
////////////////////////////////////////////////////////////////////////

FunTypes := {FldFunRat,FldFun};
NumTypes := {FldRat,FldQuad,FldCyc,FldNum};

////////////////////////////////////////////////////////////////////////

function NaiveHeightFldFun(P)
    x := P[1];
    num := Degree(Numerator(x));
    den := Degree(Denominator(x));
    return Max(num,den);
end function;

function NaiveHeightFldRat(P)
    x := P[1];
    num := Log(Max(Abs(Numerator(x),1)));
    den := Log(Max(Abs(Denominator(x),1)));
    return Max(num,den);
end function;

function NaiveHeightFldNum(P)
    x := P[1];
    deg := Degree(Ring(Parent(P)));
    num := Log(Max(Abs(AbsoluteNorm(Numerator(x))),1));
    den := Log(Max(Abs(AbsoluteNorm(Denominator(x))),1));
    return Max(num,den)/deg;
end function;

intrinsic HauteurNaive(P::PtEll) -> FldElt
    {Hauteur naive sur un corps de fonctions o corps de nombres.}
    K := Ring(Parent(P));
    if Type(K) in FunTypes then
	require Type(K) eq FldFunRat :
	  "Implemented only for rational function fields.";
	return NaiveHeightFldFun(P);
    elif Type(K) eq FldRat then
	return NaiveHeightFldRat(P);
    elif Type(K) in NumTypes then
	return NaiveHeightFldNum(P);
    end if;
end intrinsic;

