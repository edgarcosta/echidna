// Silverman Height Bounds. Martine Girard

ZZ := Integers();

function LogPlus(x,y)
    // Log of the maximum of the absolute values x and y
    return Log(Max([1,Abs(x),Abs(y)]));
end function;

intrinsic SilvermanBounds(E::CrvEll : A1 := "Integral") -> FldReElt,FldReElt
    {Bounds for the difference between canonical and naive heights}
    require A1 in {"Integral", "Weierstrass"}:
	"A1 should be \"Integral\" or \"Weierstrass\"";
    require Type(BaseRing(E)) eq FldRat and IntegralModel(E) eq E:
	"Argument must be an integral model of an elliptic " *
	"curve over the rationals." ;
    j := jInvariant(E);
    D := Discriminant(E);
    b2 := bInvariants(E)[1];
    bb2 := (b2 eq 0) select 1 else 2;
    mu := LogPlus(j,1)/6 + LogPlus(D,1)/6 + LogPlus(b2/12,1) + Log(bb2);
    LwrBd := -(mu + LogPlus(Numerator(j),Denominator(j))/12 + 1.946);
    UprBd := mu + 2.14;
    if A1 eq "Weierstrass" then
	require WeierstrassModel(E) eq E:
	    "Model should be in Weierstrass form";
	_,_,_,A,B := Explode(aInvariants(E));
	if IsSquarefree(4*ZZ!A^3+27*ZZ!B^2) and
	    GCD(ZZ!A,3*ZZ!B) eq 1 and GCD(2,ZZ!B) eq 1 then
	    LwrBd := (A gt 0) select -4.274 else -(2.41+LogPlus(j,1)/4);
	end if;
    end if;
    return LwrBd, UprBd;
end intrinsic;







