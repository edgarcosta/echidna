////////////////////////////////////////////////////////////////////////
//                                                                    //
//                 INVARIANTS OF HASSE, HILBERT, AND WITT             //
//                           David Kohel                              //
//                           April 2000                               //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic WittInvariant(V::ModTupFld,p::RngIntElt) -> RngIntElt
    {}
    require Type(BaseRing(V)) eq FldRat :
        "Argument 1 must be defined over the rationals."; 
    require IsPrime(p) : "Argument 2 must be prime";
    n := Dimension(V);
    s := HasseInvariant(V,p);
    if n mod 8 in {1,2} then
	return s;
    elif n mod 8 in {3,4} then 
	return s * HilbertSymbol(-1,-Determinant(V),p);
    elif n mod 8 in {5,6} then 
	return s * HilbertSymbol(-1,-1,p);
    else
	return s * HilbertSymbol(-1,Determinant(V),p);
    end if;
end intrinsic;

intrinsic HasseInvariant(V::ModTupFld,p::RngIntElt) -> RngIntElt
    {}
    require Type(BaseRing(V)) eq FldRat :
        "Argument 1 must be defined over the rationals."; 
    require IsPrime(p) : "Argument 2 must be prime";
    n := Dimension(V);
    A := OrthogonalizeGram(GramMatrix(V));
    return &*[
	HilbertSymbol(A[i,i],A[j,i],p) : i,j in [1..n] | i lt j ];
end intrinsic;

intrinsic NormResidueSymbol(
    a::RngElt,b::RngElt,p::RngIntElt) -> RngIntElt
    {Returns 1 if ax^2 + by^2 represents a nonzero p-adic square,
    otherwise -1.}
    require IsPrime(p) : "Argument 3 must be prime";
    if Type(a) eq FldRatElt then
	a := Numerator(a)*Denominator(a);
    end if;
    if Type(b) eq FldRatElt then
	b := Numerator(b)*Denominator(b);
    end if;
    require Type(a) eq RngIntElt and Type(b) eq RngIntElt :
	"Arguments 1 and 2 must be rationals or integers.";
    return HilbertSymbol(a,b,p);      
end intrinsic;

intrinsic HilbertSymbol(a::RngElt,b::RngElt,p::RngIntElt) -> RngIntElt
    {Returns 1 if ax^2 + by^2 represents a nonzero p-adic square, otherwise -1.}
    require IsPrime(p) : "Argument 3 must be prime";
    if Type(a) eq FldRatElt then
	a := Numerator(a)*Denominator(a);
    end if;
    if Type(b) eq FldRatElt then
	b := Numerator(b)*Denominator(b);
    end if;
    require Type(a) eq RngIntElt and Type(b) eq RngIntElt :
	"Arguments 1 and 2 must be rationals or integers.";
    while a mod p^2 eq 0 do a div:= p^2; end while;
    while b mod p^2 eq 0 do b div:= p^2; end while;
    if p ne 2 and &or[ KroneckerSymbol(x,p) eq 1 : x in {a,b,a+b} ] then
	return 1;
    end if;
    if a mod p eq 0 then 
	if b mod p eq 0 then
	    return HilbertSymbol(p,-(b div p),p) *
		HilbertSymbol(a div p,b,p);
	elif p eq 2 and (b mod 4) eq 3 then
	    if KroneckerSymbol(a+b,p) eq -1 then 
		return -1;
	    end if;    
	elif KroneckerSymbol(b,p) eq -1 then 
	    return -1;
	end if;
    elif b mod p eq 0 then
	if p eq 2 and (a mod 4) eq 3 then
	    if KroneckerSymbol(a+b,p) eq -1 then 
		return -1;
	    end if;
	elif KroneckerSymbol(a,p) eq -1 then 
	    return -1;
	end if;
    elif p eq 2 and (a mod 4) eq 3 and (b mod 4) eq 3 then
	return -1;
    end if;
    return 1;
end intrinsic;

