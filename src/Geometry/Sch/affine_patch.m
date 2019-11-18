
intrinsic AffinePatch(X::Sch,S::[RngMPolElt]) -> Sch, Map
    {}
    PP := Ambient(X);
    require IsProjective(PP) :
        "Argument 1 must be a projective variety.";
    require NumberOfGradings(PP) eq 1 :
	"Argument 1 must have a unique grading.";
    require #S eq 2 : "Argument 2 must have length 2.";
    F, G := Explode(S);
    K := BaseRing(PP); 
    R := CoordinateRing(PP);
    n := Rank(R);
    degs := Gradings(PP)[1];
    R1 := PolynomialRing(K,degs); 
    require Universe(S) cmpeq R and
        IsHomogeneous(R1!F) and IsHomogeneous(R1!G) : 
	"Argument 2 must be a sequence of homogeneous elements " *
	"of the coordinate ring of argument 1.";
    require WeightedDegree(R1!F) eq WeightedDegree(R1!G) + 1 : 
        "The degree of the first element argument 2 must be one " *
	"greater than degree of the second.";
    if TotalDegree(G) eq 0 then
	// Should check if G equals 1  (or a unit).
	if Length(F) eq 1 then
	    // Standard affine patch...
	    // Should check if leading coefficient is 1 (or a unit).
	    m := Monomials(F)[1];
	    i := Index(Exponents(m),1);
	    return AffinePatch(X,n-i+1);
	else
	    S := PolynomialRing(K,n);
	    z := 1;
	end if;
    else
	S := PolynomialRing(K,n+1);
	z := S.(n+1);
    end if;
    Smons := [ S.i : i in [1..n] ];
    f := Evaluate(F,Smons); g := Evaluate(G,Smons);
    if TotalDegree(G) eq 0 then 
	I := ideal< S | f - g >;
    else
	I := ideal< S | f - g, g*z - 1 >;
    end if;
    Rmons := [ R.i*(G/F)^degs[i] : i in [1..n] ];
    AA := Scheme(AffineSpace(S),I);
    // Rmons;
    // AA(Universe(Rmons))!Rmons;    
    return AA, map< AA -> PP | Smons >;
        // map< AA -> PP | Smons, Rmons >,
        // map< PP -> AA | Rmons >;
end intrinsic;
    
