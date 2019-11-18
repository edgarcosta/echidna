//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                  ATKIN LEHNER MODULAR POLYNOMIALS                        //
//         Copyright (C) 2009 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

forward BalancedMod, BalancedModPolynomials, TwistedEvaluatePolynomial;

function ModularPolynomialNormalize(Phi)
    P := Parent(Phi); x := P.1; j := P.2;
    for e in [1,-1] do
	Psi := Evaluate(Phi,[x-e,j]);
	while #Sprint(Psi) lt #Sprint(Phi) do
	    Phi := Psi;
	    Psi := Evaluate(Phi,[x-e,j]);
	end while;
    end for;
    return Phi;
end function;

function AtkinLehnerModularFunctionCompute(p,prec)
    assert p mod 12 eq 11;
    QQ := RationalField();
    ZZ := IntegerRing();
    DBJ := jInvariantDatabase();
    A := QuaternionOrder(p);
    M := BrandtModule(A,QQ);
    W := AtkinLehnerOperator(M,p);
    if p eq 11 then
	N := Kernel(W+1,M);
    else
	N := Kernel(W+1,CuspidalSubspace(M));
    end if;
    B := qExpansionBasis(N,prec); assert #B ge 2;
    PZ := LaurentSeriesRing(ZZ);
    return PZ!(B[#B-1]/B[#B]);
end function;

function AtkinLehnerPowerTerms(f,j,prec)
    PS := Parent(f); q := PS.1;
    oerr := O(q^prec);
    error if true, "Not implemented error.";
end function;

function AtkinLehnerModularPolynomialCompute(p : InitialPrime := 0)
    prec := 9*p; // ???
    QQ := RationalField();
    ZZ := IntegerRing();
    P2<X,J> := PolynomialRing(ZZ,2 : Global);
    tyme := Cputime();
    f := AtkinLehnerModularFunctionCompute(p,prec);
    vprint ModularPolynomial : "Atkin function time:", Cputime(tyme);
    tyme := Cputime();
    j := jInvariant(jInvariantDatabase(),ZZ,prec : Extend := true);
    vprint ModularPolynomial : "J-invariant time:", Cputime(tyme);
    deg := -Valuation(f);
    g0_plus := ModularGenusX0(p,[1]);
    I := [ [i,j] : i in [0..p+1], j in [0..2*deg] | i+j le p+1+g0_plus ];
    vprint ModularPolynomial : "Number of monomials:", #I;
    if InitialPrime ne 0 then
	q := InitialPrime;
	NextModularPrime := NextPrime;
    else
	q := PreviousPrime(Floor(2^23.5));
	NextModularPrime := PreviousPrime;
    end if;
    F1 := P2!0;
    m1 := 1;
    while true do
	if p eq q then
	    q := NextModularPrime(q);
	end if;
	tyme := Cputime();
	PS := LaurentSeriesRing(FiniteField(q));
	Rels := AlgebraicRelations([PS|f,j],[p+1,2*deg],p+1+g0_plus);
	vprintf ModularPolynomial : "Modular relations time (q = %o): %o\n", q, Cputime(tyme);
	Fq := Rels[1];
	mons := Monomials(Fq);
	cffs := Coefficients(Fq);
	if Fq eq Parent(Fq)!F1 then break; end if;
	if GetVerbose("ModularPolynomial") gt 0 then
	    Pq := Parent(Fq);
	    Mons := Monomials(F1);
	    Coeff := MonomialCoefficient;
	    printf "   Number of stable coefficients: %o/%o\n",
		#{ mon : mon in Mons | Coeff(F1,mon) eq Coeff(Fq,Pq!mon) }, #Mons ;
	end if;
	F2 := &+[ ZZ!cffs[i] * Monomial(P2,Exponents(mons[i])) : i in [1..#mons] ];
	F1 := BalancedModPolynomials([F1,F2],[m1,q]);
	m1 *:= q;
	q := NextModularPrime(q);
    end while;
    return ModularPolynomialNormalize(F1);
end function;

intrinsic AtkinLehnerModularPolynomial(N::RngIntElt : 
    Database := true, Al := "Modular", InitialPrime := 0) -> RngMPolElt
    {The modular polynomial from the Atkin database.}
    require IsPrime(N : Proof := false) : "Argument 1 must be prime.";
    DBMP := ModularPolynomialDatabase();
    if Database then
	    DBMP := ModularPolynomialDatabase();
	    require <"Atkin",N> in DBMP :  
		"Argument has no corresponding database entry.";
	    return ModularPolynomial(DBMP,"Atkin",N);
    else
        require N mod 12 eq 11 : "Argument N must be 11 mod 12.";
        require Al eq "Modular" : "Parameter \"Al\" must be \"Modular\"";
	q := InitialPrime;
	require q eq 0 or IsPrime(q : Proof := false) :
	    "Parameter \"InitialPrime\" must be prime.";
	return AtkinLehnerModularPolynomialCompute(N : InitialPrime := q);
    end if;
end intrinsic;

intrinsic AtkinLehnerModularFunction(N::RngIntElt,n::RngIntElt : Al := "Modular") -> RngSerLaurElt
    {}
    n := Max(n,20); 
    if Al eq "Integral" then
	return AtkinLehnerModularFunction(N,RationalField(),n);
    end if;
    DBMP := ModularPolynomialDatabase();
    if <"Atkin",N> notin DBMP then
	require N mod 12 eq 11 : "Argument 1 must be 11 mod 12.";
	return AtkinLehnerModularFunctionCompute(N,n);
    end if;
    modulus := 1;
    log_modulus := 0;
    char := PreviousPrime(Floor(2^29.5));
    coeffs := [ Integers() | 1 : i in [1..n] ];
    stable := false;
    tyme := Cputime();
    vprintf ModularPolynomial : "Reading in modular polynomial...";
    Phi := AtkinLehnerModularPolynomial(N);
    vprintf ModularPolynomial : "%o secs\n", Cputime(tyme);
    tyme := Cputime();
    vprintf ModularPolynomial : "Reading in j-invariant series...";
    DBJ := jInvariantDatabase();
    j := jInvariant(DBJ,Integers(),n+20 : Extend := true);
    vprintf ModularPolynomial : "%o secs\n", Cputime(tyme);
    while not stable do
	vprintf ModularPolynomial : "Computing series mod %o\n", char;
	K := FiniteField(char);
	PSK := LaurentSeriesRing(K);
	tyme := Cputime(); 
	u := AtkinLehnerModularFunction(N, K, n :
  	    ModularPolynomial := Phi, jFunctionSeries := j);
	vprintf ModularPolynomial :
           "Total modular computation time = %o\n", Cputime(tyme);
	pcoeffs := ChangeUniverse(Eltseq(u),Integers());
	while #pcoeffs lt n do Append(~pcoeffs,0); end while;
	new_coeffs := [
	    CRT([coeffs[i],pcoeffs[i]],[modulus,char]) : i in [1..n] ];
        modulus *:= char;
	log_modulus +:= Log(char);
	log_current := Log(Max([1,Max(new_coeffs),-Min(new_coeffs)]));
	new_coeffs := [ BalancedMod(c,modulus) : c in new_coeffs ];
	max_good := Max([ i : i in [1..n] | new_coeffs[i] eq coeffs[i] ]);
	if (log_current + 8) lt log_modulus then
	    stable := true;
	    vprintf ModularPolynomial :
 	        "Terminating with %o coefficients stable " *
                "and precision margin of %o\n", max_good,
		RealField(8)!(log_modulus - log_current);
	else 
	    vprintf ModularPolynomial :
                "Continuing with %o coefficients stable " * 
                "and precision margin of %o\n", max_good,
		RealField(8)!(log_modulus - log_current);
	end if;
	coeffs := new_coeffs;
	char := PreviousPrime(char);
    end while;
    m := Valuation(u);
    PS := LaurentSeriesRing(Integers()); t := PS.1;
    return t^m * PS!coeffs + O(t^(n+m));
end intrinsic;

intrinsic AtkinLehnerModularFunction(
    N::RngIntElt,K::Fld,n::RngIntElt : ModularPolynomial := 1, jFunctionSeries := 1) -> RngSerLaurElt
    {}
    PS := LaurentSeriesRing(K); t := PS.1;
    PPS := PolynomialRing(PS); X := PPS.1;
    u1 := PS!1;  
    val := 0;
    prec := n+20;
    tyme := Cputime();
    if ModularPolynomial eq 1 then
	Phi := AtkinLehnerModularPolynomial(N);
    else 
	Phi := ModularPolynomial;
    end if;
    vprintf ModularPolynomial :
        "Atkin modular polynomial time = %o\n", Cputime(tyme);
    m := Degree(Phi,2) div 2;
    tyme := Cputime();
    if jFunctionSeries eq 1 then
	DBJ := jInvariantDatabase();
	j := jInvariant(DBJ,K,prec : Extend := true);
    else
	j := PS!jFunctionSeries;
    end if;
    vprintf ModularPolynomial :
        "j-invariant computation time = %o\n", Cputime(tyme);
    tyme := Cputime();
    /*
    // N.B. This evaluation is way too slow:
    phi1 := Evaluate(Phi,[X*t^-m,j])*t^(m*(N+1));
    */
    phi1 := TwistedEvaluatePolynomial(Phi,j,m);
    vprintf ModularPolynomial :"Series evaluation time = %o\n", Cputime(tyme);
    tyme := Cputime();
    u1 := NewtonLift(phi1,Truncate(u1),prec);
    vprintf ModularPolynomial :
        "Hensel lifting time = %o\n", Cputime(tyme);
    return u1*t^-m + O(t^(n-m));
end intrinsic;

intrinsic ExtendAtkinLehnerModularFunction(N::RngIntElt, f::RngSerElt,
    n::RngIntElt) -> RngSerLaurElt
    {}
    K := BaseRing(Parent(f));
    PS := LaurentSeriesRing(K); t := PS.1;
    PPS := PolynomialRing(PS); X := PPS.1;
    Phi := AtkinLehnerModularPolynomial(N); 
    m := Degree(Phi,2) div 2;
    prec := n+20;
    j := jInvariant(t+O(t^(prec+1)));
    phi1 := Evaluate(Phi,[X*t^-m,j])*t^(m*(N+1));
    u1 := f*t^m;
    val := Valuation(Evaluate(phi1,u1));
    print "prec =", prec;
    print "val =", val;    
    require val gt 0 :
       "Argument 1 must be a root of the Atkin modular polynomial.";
    vprintf ModularPolynomial :
	"Found initial zero of order %o (working precision: %o)\n", val, prec;
    while val lt n do
        u1 := NewtonLift(phi1,Truncate(u1),prec);
        val := Valuation(Evaluate(phi1,u1));
        prec +:= Max((n-val),0)+20; 
        vprintf ModularPolynomial :
	    "Found zero of order %o (working precision: %o)\n", val, prec;
        if val ge prec then break; end if;
        j := jInvariant(t+O(t^(prec+1)));
	phi1 := Evaluate(Phi,[X*t^-m,j])*t^(m*(N+1));
    end while;
    return u1*t^-m + O(t^(n-m));
end intrinsic;

function BalancedMod(a,m)
    t := m div 2;
    a mod:= m;
    if a le t then return a;
    else return a-m;
    end if;
end function;

function BalancedModPolynomials(Polys,Mods)
    P := Universe(Polys);
    m := &*Mods;
    F, G := Explode(Polys);
    Exps := {@ Exponents(mon) : mon in Monomials(F) @} join {@ Exponents(mon) : mon in Monomials(G) @};
    return &+[ BalancedMod(CRT([MonomialCoefficient(F,e),MonomialCoefficient(G,e)],Mods),m) * Monomial(P,e) : e in Exps ];
end function;

function TwistedEvaluatePolynomial(Phi,y,m)
    PS := Parent(y); t := PS.1;
    K := BaseRing(PS);
    PSX := PolynomialRing(PS); X := PSX.1;
    deg1 := Degree(Phi,1);
    deg2 := Degree(Phi,2);
    mons := Monomials(Phi);
    exps := [ Exponents(m) : m in mons ];
    cffs := [ K | MonomialCoefficient(Phi,m) : m in mons ];
    powy := [ Parent(y) | 1 ];
    for i in [1..deg2] do Append(~powy,powy[i] * y); end for;
    return PSX ! [ &+[ PS | cffs[i] * powy[exps[i][2]+1] : 
        i in [1..#exps] | exps[i][1] eq j ] * t^(m*(deg1-j)) : j in [0..deg1] ];
end function;


    
