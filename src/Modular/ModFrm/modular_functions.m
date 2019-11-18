////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            Modular Functions                       //
//                         Power Series Expansions                    // 
//                               David Kohel                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////

/*

P2<X,J> := PolynomialRing(ZZ,2);
PS<q> := LaurentSeriesRing(QQ);
j := jInvariant(PS,201);
for p in [2,3,5,7,13] do
   jp := Evaluate(j,q^p + O(q^201));
   f := CanonicalDedekind(PS,p,201);
   s := 12 div GCD(p-1,12);
   u := f + p^s/f;
   u +:= -PS!Coefficient(u,0);
   v1 := Basis( LinearRelations(
         [u^(p-i)+O(q^201) : i in [0..p] ] cat [-j-jp]))[1];
   v2 := Basis( LinearRelations(
	 [u^(p+1-i)+O(q^201) : i in [0..p+1] ] cat [-j*jp]))[1];
   F1 := &+[ (ZZ!v1[i])*X^(n-i) : i in [1..n] ] where n := #Eltseq(v1)-1;
   F2 := &+[ (ZZ!v2[i])*X^(n-i) : i in [1..n] ] where n := #Eltseq(v2)-1;
   Phi := J^2 - F1*J + F2;
   Write(DBME,Phi,"Atkin",p);
end for;

for p in [11,17,19] do
   jp := Evaluate(j,q^p + O(q^201));
   M := BrandtModule(DBBM,p,1);
   w1, w0 := Explode(qExpansionBasis(M,201));
   u := w1/w0;
   u +:= -PS!Coefficient(u,0);
   v1 := Basis( LinearRelations(
         [u^(p-i)+O(q^201) : i in [0..p] ] cat [-j-jp]))[1];
   v2 := Basis( LinearRelations(
	 [u^(p+1-i)+O(q^201) : i in [0..p+1] ] cat [-j*jp]))[1];
   F1 := &+[ (ZZ!v1[i])*X^(n-i) : i in [1..n] ] where n := #Eltseq(v1)-1;
   F2 := &+[ (ZZ!v2[i])*X^(n-i) : i in [1..n] ] where n := #Eltseq(v2)-1;
   Phi := J^2 - F1*J + F2;
   Write(DBME,Phi,"Atkin",p);
end for;

*/

intrinsic SupersingularBasis(p::RngIntElt) -> SeqEnum
    {}
    require IsPrime(p) : "Argument must be prime.";
    FF := FiniteField(p);
    P := PolynomialRing(FF);
    x := P.1;
    H := SupersingularPolynomial(FF);
    g := Degree(H);
    g_plus := (Degree(H) - #Roots(H)) div 2;
    V := VectorSpace(FF,g);
    U := sub< V | V.1 >;
    for i in [1..g-1] do
	coeff := Eltseq(x^i+(x^(i*p) mod H));
	while #coeff lt g do coeff cat:= [0]; end while; 
	U := sub< V | U, V!coeff >;
	if Dimension(U) eq g_plus then break i; end if;
    end for;
    return [ P!Eltseq(c) : c in Basis(U) ];
end intrinsic;

intrinsic CanonicalDedekind(PS::RngSer,N::RngIntElt,prec::RngIntElt)
    -> RngSerElt {}
    bool, p := IsSquare(N);
    if bool then
	t := GCD(N-1,24);
	s := 24 div t;
	e := s; 
    else
	p := N; 
	t := GCD(N-1,24);
	s := 12 div t;
	e := 2*s; 
    end if;
    u := (N-1) div t;  
    q := PS.1;
    oerr := O(q^prec);
    // num := &*[ 1-q^(k*p) + oerr : k in [1..prec div p] ];
    num := PS!1;
    for k in [1..prec div N] do
	num -:= q^(k*N)*num + oerr;
    end for;
    // den := &*[ 1-q^k + oerr : k in [1..prec-1] ];
    den := PS!1;
    for k in [1..prec-1] do
	den -:= q^k*den + oerr;
    end for;
    return q^u * p^s * (num/den)^e;
end intrinsic;

intrinsic DedekindEta(PS::RngSerPuis,prec::RngIntElt) -> RngSerPuisElt
    {}
    q := PS.1;
    oerr := O(q^prec);
    // eta := &*[ 1-q^i + oerr : i in [1..prec-1] ];
    eta := PS!1;
    for i in [1..prec-1] do
	eta -:= q^i*eta + oerr;
    end for;
    return q^(1/24) * eta;
end intrinsic;

intrinsic DedekindEta(PS::RngSer,S::[Tup],prec::RngIntElt) -> RngSerElt
    {}
    v := &+[ t[1]*t[2] : t in S ];
    require v mod 24 eq 0 :
	"Argument 2 does not define a form without character.";
    v div:= 24;
    q := PS.1;
    oerr := O(q^prec);
    // eta := &*[ 1-q^i + oerr : i in [1..prec-1] ];
    eta := PS!1;
    for i in [1..prec-1] do
	eta -:= q^i*eta + oerr;
    end for;
    f := &*[ Evaluate(eta,q^t[1] + oerr)^t[2] : t in S ];
    return q^v * f;
end intrinsic;

intrinsic jInvariant(PS::RngSer,prec::RngIntElt) -> RngSerElt
    {}
    q := PS.1;
    oerr := O(q^prec);
    return jInvariant(q + oerr);
end intrinsic;

