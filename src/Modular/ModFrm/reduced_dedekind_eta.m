////////////////////////////////////////////////////////////////////////
//                                                                    //
//               REDUCED DEDEKIND ETA MODULAR POLYNOMIALS             //
//                            February 2001                           //
//                             David Kohel                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

forward RDMPLocalCompute, RDMPModularCompute, RDMPIntegralCompute;

////////////////////////////////////////////////////////////////////////

function BalancedMod(a,m)
    t := m div 2;
    a mod:= m;
    if a le t then return a;
    else return a-m;
    end if;
end function;

function RDMPMonomialExponents(r,N)
    t := GCD(N-1,12);
    s := 12 div t;
    // Valuation of f and degree of Phi in J : 
    u := ((N-1)*s) div 12;   
    if r eq 3 then
	I := [ [N+1,0] ] cat [ [i,j] : i in [1..N], j in [0..u] | i + t*j le N and (i - u*j) mod 3 eq 0 and [i,j] ne [1,u] ] cat [ [0,0], [1,u] ];
    else
	I := [ [i,j] : i in [0..N], j in [0..u] | i + t*j le N ] cat [ [N+1,0] ];
    end if;
    return Reverse(I), s, t, u;
end function;

//////////////////////////////////////////////////////////////////////////////
//                        Relation computations                             //
//////////////////////////////////////////////////////////////////////////////

function MonomialRelations(fncs,I,prec)
    PS := Universe(fncs); q := PS.1; oerr := O(q^prec);
    f, j := Explode(fncs);
    p := Max([ n[1] : n in I ]) - 1;
    u := Max([ n[2] : n in I ]);
    tyme := Cputime();
    fs := [ PS!1 ];
    for k in [1..p+1] do
	Append(~fs,fs[k]*f + oerr);
    end for;
    vprint ModularPolynomial : "Function 1 powers time:", Cputime(tyme);
    tyme := Cputime();
    js := [ PS!1 ];
    for k in [1..u] do
	Append(~js,js[k]*j);
    end for;
    vprint ModularPolynomial : "Function 2 powers time:", Cputime(tyme);
    tyme := Cputime();
    S := [ fs[n[1]+1]*js[n[2]+1] + O(q^(u*(p+1)+1)) : n in I ];
    vprint ModularPolynomial : "Power series sequence time:", Cputime(tyme);
    tyme := Cputime();
    V := LinearRelations(S);
    vprint ModularPolynomial : "Linear algebra time:", Cputime(tyme);
    if Dimension(V) eq 0 then
	Phi := ModularPolynomial(ModularPolynomialDatabase(),"Reduced Dedekind eta",p);
	Evaluate(Phi,[f,j]);
	assert false;
    end if;
    return V;
end function;   

////////////////////////////////////////////////////////////////////////
//               Reduced Dedekind Eta Modular Function                //
////////////////////////////////////////////////////////////////////////

function ReducedDedekindEtaFunction(r,N,K,prec)
    // t := GCD(N-1,12); s := 12 div t; u := ((N-1)*s) div 12;
    u := LCM(N-1,12) div 12;
    s := 12 div GCD(N-1,12);
    tyme := Cputime();
    PS := LaurentSeriesRing(K); q := PS.1; oerr := O(q^prec);
    // Memory blowup: num := &*[ 1-q^(r*k*N) + oerr : k in [1..(prec div (r*N))-1] ];
    num := PS!1;
    for k in [1..prec div (r*N)] do
	num -:= q^(r*k*N)*num + oerr;
    end for;
    // Memory blowup: den := &*[ 1-q^(r*k) + oerr : k in [1..(prec div r)] ];
    den := PS!1;
    for k in [1..prec div r] do
	den -:= q^(r*k)*den + oerr;
    end for;
    f := q^u * N^(s div r) * (num/den)^(2*s div r);
    vprint ModularPolynomial : "Eta quotient time:", Cputime(tyme);
    return f;
end function;   

function ReducedjFunction(r,K,prec)
    assert r in {2,3};
    tyme := Cputime();
    PS := LaurentSeriesRing(K); q := PS.1; oerr := O(q^prec);
    PZ := LaurentSeriesRing(IntegerRing());
    PQ := LaurentSeriesRing(RationalField()); z := PQ.1;
    num := PS!PZ!Eisenstein(12 div r,z^r + O(z^prec)) + oerr;
    // Memory blowup: den := &*[ 1-q^(r*k) + oerr : k in [1..(prec div r)] ];
    den := PS!1;
    for k in [1..prec div r] do
	den -:= q^(r*k)*den + oerr;
    end for;
    j := q^-1 * num/den^(24 div r);
    vprint ModularPolynomial : "Reduced j-function series time:", Cputime(tyme);
    return j;
end function;   

////////////////////////////////////////////////////////////////////////
//               Reduced Dedekind Eta Modular Polynomial              //
////////////////////////////////////////////////////////////////////////

intrinsic ReducedDedekindEtaModularPolynomial(r::RngIntElt, N::RngIntElt : 
    Database := false, Al := "Modular", InitialPrime := 0) -> RngMPolElt
    {The reduced Dedekind eta modular polynomial over R relating (eta(q)/eta(N*q))^e
    and j(q)^1/3 where e = 8/GCD(4,N-1), for N prime congruent to 2 mod 3
    (r = 3) or relating (eta(q)/eta(N*q))^e and (j(q)-12^3)^1/2 where
    e = 6/GCD(3,N-1), for N prime congruent to 3 mod 4.}

    require r in {2,3} : "Argument 1 must be 2 or 3.";
    if r eq 2 then
	require N mod 4 eq 3 : "Argument 2 must be congruent to 3 mod 4 when argument 1 is 2.";
    elif r eq 3 then
	require N mod 3 eq 2 : "Argument 2 must be congruent to 2 mod 3 when argument 1 is 3.";
    end if;
    require IsPrime(N) : "Argument 2 must be prime.";
    if Database then
	DBMP := ModularPolynomialDatabase();
	require <"Reduced Dedekind eta",N> in DBMP : "Argument has no corresponding database entry.";
	return ModularPolynomial(DBMP,"Reduced Dedekind eta",N);
    elif Al eq "Modular" then
	char := InitialPrime;
	require char eq 0 or IsPrime(char : Proof := false) :
	    "Parameter \"InitialPrime\" must be prime.";
	return RDMPModularCompute(r,N : InitialPrime := char);
    elif Al eq "Integral" then
	return RDMPIntegralCompute(r,N);
    else
	require false : "Parameter \"Al\" must be \"Modular\" or \"Integral\".";
    end if;
end intrinsic;

intrinsic ReducedDedekindEtaModularPolynomial(r::RngIntElt, N::RngIntElt, R::Rng : 
    Database := false, Al := "Modular", InitialPrime := 0) -> RngMPolElt
    {The reduced Dedekind eta modular polynomial over the ring R relating
    (eta(q)/eta(N*q))^e and j(q)^1/3 where e = 8/GCD(4,N-1), for N prime
    congruent to 2 mod 3.}

    require r in {2,3} : "Argument 1 must be 2 or 3.";
    if r eq 2 then
	require N mod 4 eq 3 : "Argument 2 must be congruent to 3 mod 4 when argument 1 is 2.";
    elif r eq 3 then
	require N mod 3 eq 2 : "Argument 2 must be congruent to 2 mod 3 when argument 1 is 3.";
    end if;
    P2<X,Y> := PolynomialRing(R,2 : Global);
    if Database then
	DBMP := ModularPolynomialDatabase();
	require <"Reduced Dedekind eta",N> in DBMP : "Argument has no corresponding database entry.";
	return ModularPolynomial(DBMP,"Reduced Dedekind eta",N);
    elif Type(R) in {FldFin,RngPadRes} then
	q := #R;
	require q mod N ne 0 : "Argument 1 must be coprime to the characteristic of argument 2.";
	cffs := RDMPLocalCompute(r,N,R);
	mons := RDMPMonomialExponents(r,N);
	return &+[ P2 | cffs[j]*X^mons[j][1]*Y^mons[j][2] : j in [1..#mons] ];
    elif Al eq "Modular" then
	char := InitialPrime;
	require char eq 0 or IsPrime(char : Proof := false) : "Parameter \"InitialPrime\" must be prime.";
	return P2!RDMPModularCompute(r,N : InitialPrime := char);
    elif Al eq "Integral" then
	return P2!RDMPIntegralCompute(r,N);
    else
	require false : "Parameter \"Al\" must be \"Modular\" or \"Integral\".";
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                  Modular Equations Computations                    //
////////////////////////////////////////////////////////////////////////

function RDMPLocalCompute(r,N,FF)
    I, s, t, u := RDMPMonomialExponents(r,N);
    prec := (N+1)*u + N + 32;
    vprint ModularPolynomial : "Modular prime power =", #FF;
    vprint ModularPolynomial : "Degree in f =", N+1;
    vprint ModularPolynomial : "Degree in j =", u;
    vprint ModularPolynomial : "Precision =", prec;
    vprint ModularPolynomial : "Number of terms =", #I;
    P<X,Y> := PolynomialRing(FF,2 : Global);
    tyme := Cputime();
    PS<q> := LaurentSeriesRing(FF);
    f := ReducedDedekindEtaFunction(r,N,FF,prec);
    j := ReducedjFunction(r,FF,prec);
    vprint ModularPolynomial : "Generator series time:", Cputime(tyme);
    V := MonomialRelations([f,j],I,prec);
    vprintf ModularPolynomial :
        "Found solution space of dimension %o and degree %o.\n", Dimension(V), Degree(V);
    error if Dimension(V) ne 1, "Precision error.";
    v := Basis(V)[1];
    i := Index(I,[N+1,0]);
    if v[i] ne 1 then v *:= v[i]^-1; end if;
    return ChangeUniverse(Eltseq(v),IntegerRing());
end function;   

function RDMPModularCompute(r,p : InitialPrime := 0)
    I := RDMPMonomialExponents(r,p);
    rems := [ ]; 
    mods := [ Integers() | ];
    m := 1;
    if InitialPrime ne 0 then
	char := InitialPrime;
	NextModularPrime := NextPrime;
    else
	char := PreviousPrime(Floor(2^23.5));
	NextModularPrime := PreviousPrime;
    end if;
    stable := false;
    zz_coeffs := [ 0 : i in [1..#I] ];
    while not stable do
	if p eq char then
	    char := NextModularPrime(char);
	end if;
	m *:= char;
	tyme := Cputime();
	ff_coeffs := RDMPLocalCompute(r,p,FiniteField(char));
	vprint ModularPolynomial : "Modular computation time:", Cputime(tyme);
	Append(~rems,ff_coeffs);
	Append(~mods,char);
	new_coeffs := [ BalancedMod( CRT(
    	    [ coeffs[i] : coeffs in rems ],mods), m ) : i in [1..#I] ];
	vprintf ModularPolynomial : "(#NonZero, #Zero) = (%o,%o)\n",
 	    #[ I[i] : i in [1..#I] | new_coeffs[i] ne 0 ],	
	    #[ I[i] : i in [1..#I] | new_coeffs[i] eq 0 ];	
        stable := &and[ zz_coeffs[i] eq new_coeffs[i] : i in [1..#I] ];
	zz_coeffs := new_coeffs;
	coeff_size := Max([ Ceiling(Log(10,1+Abs(c))) : c in zz_coeffs ]);
	modulus_size := Ceiling(Log(10,m));
	if coeff_size le modulus_size - 4 then
	    stable := true;
	end if;
	vprintf ModularPolynomial :
	"Modulus size is %o digits.\n", modulus_size;
	vprintf ModularPolynomial :
	"Max coefficient size is %o digits.\n", coeff_size;
	vprintf ModularPolynomial, 2 :
            "Completed %o coefficients, %o remaining.\n", 
	    &+[ Integers() | 1 : c in zz_coeffs |
	            Ceiling(Log(10,1+Abs(c))) le modulus_size - 4 ],
	    &+[ Integers() | 1 : c in zz_coeffs |
	            Ceiling(Log(10,1+Abs(c))) gt modulus_size - 4 ];
        char := NextModularPrime(char);
    end while;
    P2<X,J> := PolynomialRing(IntegerRing(),2 : Global);
    return &+[ zz_coeffs[j]*X^I[j][1]*J^I[j][2] : j in [1..#I] ];
end function;

////////////////////////////////////////////////////////////////////////
//                        Integral Function                           //
////////////////////////////////////////////////////////////////////////

function RDMPIntegralCompute(r,N)
    I, s, t, u := RDMPMonomialExponents(r,N);
    prec := (N+1)*u + N + 32;
    vprint ModularPolynomial : "Level =", N;
    vprint ModularPolynomial : "Working precision =", prec;
    vprint ModularPolynomial : "Number of terms =", #I;
    tyme := Cputime();
    ZZ := IntegerRing();
    f := ReducedDedekindEtaFunction(r,N,ZZ,prec);
    j := ReducedjFunction(r,ZZ,prec);
    vprint ModularPolynomial : "Series computation time:", Cputime(tyme);
    stables := [ Integers() | ];
    zz_coeffs := [ Integers() | ];
    coeffs := MonomialRelations([f,j],I,prec);
    P2 := PolynomialRing(Integers(),2);
    X := P2.1; J := P2.2;
    return &+[ coeffs[j]*X^I[j][1]*J^I[j][2] : j in [1..#I] ];
end function;   

