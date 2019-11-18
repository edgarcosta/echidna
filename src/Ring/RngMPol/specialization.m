////////////////////////////////////////////////////////////////////////
//     Specialization of Polynomials with Multiivariate Base Ring     //
////////////////////////////////////////////////////////////////////////

intrinsic Specialization(f::RngUPolElt,S::[RngElt]) -> RngUPolElt
    {Given f in k[x1,..,xn][x], returns f([a1,..,an],x).}
    R := BaseRing(Parent(f));
    print "R:", R;
    require ElementType(R) in {RngMPolElt,FldFunRatMElt} : 
	"Argument 1 base ring must be a multivariate polynomial ring.";
    require Rank(R) eq #S :
	"Argument 2 universe incompatible with argument 1.";	
    K := BaseRing(R);
    bool, T := CanChangeUniverse(S,K);
    if bool then
	return PolynomialRing(K)![ Evaluate(c,T) : c in Eltseq(f) ];
    end if;
    L := Universe(S);
    if BaseRing(L) cmpne K then
	require false : "Argument 2 universe incompatible with argument 1.";
    end if;
    return PolynomialRing(L)![ Evaluate(c,S) : c in Coefficients(f) ];
end intrinsic;

intrinsic Specialization(f::RngMPolElt,S::[RngElt]) -> RngUPolElt
    {Given f in k[t1,..,tn][x1,..,xm], returns f([a1,..,an],x1,..,xm).}
    R := BaseRing(Parent(f));
    require ElementType(R) in {RngMPolElt,FldFunRatMElt} : 
	"Base ring of parent of argument 1 " *
	"must be a multivariate polynomial ring.";
    K := BaseRing(R);
    bool, S := CanChangeUniverse(S,K);
    require bool and Rank(R) eq #S : 
	"Universe of sequence incompatible with argument 1.";
    m := Rank(Parent(f));
    P := PolynomialRing(K,m : Global := true);
    cffs := Coefficients(f);
    nmons := [ P | &*[ P | P.i^e[i] : i in [1..m] ]
	where e := Exponents(mon) : mon in mons ]
	where mons := Monomials(f); 
    return &+[ P | Evaluate(cffs[i],S) * nmons[i] : i in [1..#cffs] ];
end intrinsic;

////////////////////////////////////////////////////////////////////////
//      Specialization of Polynomials with Univariate Base Ring       //
////////////////////////////////////////////////////////////////////////

intrinsic Specialization(f::RngUPolElt,a::RngElt) -> RngUPolElt
    {Given f in K[t][x] or K(t)[x], returns f(a,x).}
    R := BaseRing(Parent(f));
    require ElementType(R) in {RngUPolElt,FldFunRatUElt} : 
	"Base ring of parent of argument 1 " *
	"must be a univariate polynomial ring.";
    K := BaseRing(R);
    bool, a := IsCoercible(K,a);
    require bool and Rank(R) eq 1 :
	"Universe of sequence incompatible with argument 1.";
    return PolynomialRing(K)![ Evaluate(c,a) : c in Eltseq(f) ];
end intrinsic;

intrinsic Specialization(f::RngMPolElt,a::RngElt) -> RngUPolElt
    {Given f in K[t][x1,..,xm] or K(t)[x1,..,xm], returns f(a,x1,..,xm).}
    R := BaseRing(Parent(f));
    require ElementType(R) in {RngUPolElt,FldFunRatUElt} : 
	"Base ring of parent of argument 1 " *
	"must be a univariate polynomial ring.";
    K := BaseRing(R);
    bool, a := IsCoercible(K,a);
    require bool and Rank(R) eq 1 : 
	"Universe of sequence incompatible with argument 1.";
    m := Rank(Parent(f));
    P := PolynomialRing(K,m : Global := true);
    cffs := Coefficients(f);
    nmons := [ P | &*[ P | P.i^e[i] : i in [1..m] ]
	where e := Exponents(mon) : mon in mons ]
	where mons := Monomials(f); 
    return &+[ P | Evaluate(cffs[i],a) * nmons[i] : i in [1..#cffs] ];
end intrinsic;
