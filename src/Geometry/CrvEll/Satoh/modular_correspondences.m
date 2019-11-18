////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                Modular Correspondences for Satoh AGM               //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function PhiX(p,x,y)
    if p le 5 or p eq 11 or p eq 19 or p eq 23 then
	// D = -4 is supersingular
	Phi := ClassicalModularPolynomial(p);
	P<X,Y> := Parent(Phi);
	Phi := Numerator(Evaluate(Phi,[(1+12^3*X)/X,(1+12^3*Y)/Y]));
	return Evaluate(Phi,[x,y]);
    elif p eq 7 or p eq 13 or p eq 17 then
	// D = -7 is supersingular
	Phi := ClassicalModularPolynomial(p);
	P<X,Y> := Parent(Phi);
	Phi := Numerator(Evaluate(Phi,[(1-15^3*X)/X,(1-15^3*Y)/Y]));
	return Evaluate(Phi,[x,y]);
    elif p eq 11 then
	// D = -3 (or D = -4) is supersingular (latter sent to 1)
	Phi := ClassicalModularPolynomial(p);
	P<X,Y> := Parent(Phi);
	Phi := Numerator(Evaluate(Phi,[(1+12^3*X)/X,(1+12^3*Y)/Y]));
	return Evaluate(Phi,[x,y]);
	/*
	return Evaluate(ReciprocalClassicalModularPolynomial(p),[x,y]);
	*/
    elif p eq 17 then
	// D = -3 (or D = -7)
	Phi := ClassicalModularPolynomial(p);
	P<X,Y> := Parent(Phi);
	Phi := Numerator(Evaluate(Phi,[1/X,1/Y]));
	return Evaluate(Phi,[x,y]);
    end if;
end function;

intrinsic ModularCorrespondence(p::RngIntElt,R::Rng) -> RngMPolElt
    {}
    P<X,Y> := PolynomialRing(R,2 : Global := true);
    return PhiX(p,X,Y);
end intrinsic;

intrinsic ModularCorrespondence(p::RngIntElt) -> RngMPolElt
    {}
    P<X,Y> := PolynomialRing(Integers(),2 : Global := true);
    return PhiX(p,X,Y);
end intrinsic;

function DxPhiX(p,x,y)
    if p le 5 or p eq 11 then
	Phi := ReciprocalClassicalModularPolynomial(p);
    elif p eq 7 then
	Phi := ClassicalModularPolynomial(p);
	P<X,Y> := Parent(Phi);
	Phi := Numerator(Evaluate(Phi,[1/(X+1),1/(Y+1)]));
    elif p eq 13 then
	Phi := ClassicalModularPolynomial(p);
	P<X,Y> := Parent(Phi);
	Phi := Numerator(Evaluate(Phi,[1/(X-5),1/(Y-5)]));
    end if;
    return Evaluate(Derivative(Phi,1),[x,y]);
end function;

function DyPhiX(p,x,y)
    return DxPhiX(p,y,x);
end function;

