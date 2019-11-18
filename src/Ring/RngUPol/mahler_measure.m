
intrinsic MahlerMeasure(f::RngUPolElt,prec::RngIntElt :
    Al := "Combination") -> FldReElt
    {The Mahler measure of the rataional or integral polynomial f.}
    require Type(BaseRing(Parent(f))) in {FldRat,RngInt} :
	"Base ring of parent of argument 1 must be the integers or rationals.";
    require prec gt 0 : "Argument 2 must be positive.";
    f := PolynomialRing(ComplexField(prec))!f;
    rts := [ AbsoluteValue(r[1]) : r in Roots(f : Al := Al) ];
    meas := &+[ RealField(prec) | Log(r) : r in rts | r gt 1 ];
    return meas;
end intrinsic;
