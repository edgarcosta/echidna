////////////////////////////////////////////////////////////////////////
//                                                                    //
//                CONVERTING REDUCED MODULAR POLYNOMIALS              //
//                      TO STANDARD POLYNOMIALS                       //
//                           February 2001                            //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic ReducedToModularPolynomial(Phi::RngMPolElt,t::Tup) -> RngMPolElt
    {}
    P2 := Parent(Phi);
    X := P2.1; Y := P2.2;
    require Rank(P2) eq 2 :
        "Argument 1 must be an element of a bivariate polynomial ring.";
    R := BaseRing(P2);
    require Type(R) eq RngInt :
        "Parent of argument 1 must be defined over the integers.";
    require #t eq 2 : "Argument 2 must be a tuple of two elements.";
    ModelType := t[1];
    N := t[2];
    require Type(ModelType) eq MonStgElt and Type(N) eq RngIntElt :
        "Argument 2 must be a tuple consisting of a string and an integer.";
    if ModelType eq "Classical" then
	s := -N mod 3;
    elif ModelType eq "Dedekind eta" then
        r := 12 div GCD(N-1,12);
	v := ((N-1)*r) div 12;
	s := v mod 3;
     else 
	require false : "Second element of argument 2 must be either \"Dedekind eta\" or \"Classical\".";
    end if;
    S<w> := NumberField(x^2+x+1) where x := PolynomialRing(Integers()).1;
    Q2 := PolynomialRing(S,2);
    U := Q2.1; V := Q2.2;
    Phi3 := P2!&*[ Evaluate(Phi,[w^(2*i)*U,w^(2*s*i)*V]) : i in [0..2] ];
    assert &and[ &and[ e mod 3 eq 0 : e in Exponents(m) ] : m in Monomials(Phi3) ];
    return &+[ MonomialCoefficient(Phi3,m)*X^(n[1] div 3)*Y^(n[2] div 3)
                  where n := Exponents(m) :  m in Monomials(Phi3) ];
end intrinsic;

