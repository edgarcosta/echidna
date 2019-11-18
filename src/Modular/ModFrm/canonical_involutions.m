////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         CANONICAL INVOLUTIONS                      //
//                 FOR DEDEKIND ETA MODULAR POLYNOMIALS               //
//                             David Kohel                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

forward DCIModularCompute, DCILocalCompute, DCIIntegralCompute;
forward ACIModularCompute, ACILocalCompute;

function DCIMonomialExponents(N,deg)
    t := GCD(N-1,12);
    s := 12 div t;
    u := ((N-1)*s) div 12;   
    I := &cat[ [ [i,k] : i in [0..(deg*u-N*k+1) div u] ] : k in [0..u-1] ];
    return I, s, t, u;
end function;

function ACIMonomialExponents(N,d2,deg)
    r := d2 div 2;
    I := [ [i,0] : i in [0..(N div r)+deg] ];
    if d2 eq 2 then
	I cat:= [ [i,1] : i in [0..deg] ]; 
	return I;
    end if;
    for k in [1..d2-1] do
	max := ((N*(2-k)) div r) + deg;
	I cat:= [ [i,k] : i in [0..max] ];
    end for;
    return I;
end function;

intrinsic CanonicalInvolution(
    ModelType::MonStgElt, N::RngIntElt : 
    Al := "Modular", ClearDenominator := false) -> FldFunElt
    {}

    require ModelType in {"Atkin","Dedekind eta"} :
        "Argument 1 must be \"Atkin\" or \"Dedekind eta\".";
    require Al in {"Factorization","Integral", "Modular"} :
        "Parameter Al must be \"Factorization\", " *
        "\"Integral\" or \"Modular\".";

    if Al eq "Factorization" then
	DBMP := ModularPolynomialDatabase();
	Phi := ModularPolynomial(DBMP,ModelType,N);
	FF := FunctionField(RationalField());
	x := FF.1;
	PF := PolynomialRing(FF);
	j := PF.1;
	if ClearDenominator then
	    PQ := PolynomialRing(RationalField());
	    disc := Numerator(FF!Discriminant(Evaluate(Phi,[x,j])));
	    fac := Factorization(disc);
	    den := &*[ PQ | f[1]^(f[2] div 2) : f in fac | f[1] ne x ];
	    if GCD(N-1,12) eq 1 then
		den *:= PQ.1^N;
	    else
		den *:= PQ.1^GCD(N-1,12);
	    end if;
	    print "Denominator:";
	    print den;
	    print "Factorization:";
	    print Factorization(den);
	else
	    den := FF!1;
	end if;
	KK<j> := FunctionField(Evaluate(Phi,[x,j]));
	PK<J> := PolynomialRing(KK);
	if ModelType eq "Atkin" then
	    num := Roots(Evaluate(Phi,[x,J/den]) div (J-j*den))[1][1];
	else
	    s := 12 div GCD(N-1,12);
	    num := Roots(Evaluate(Phi,[N^s/x,J/den]))[1][1];
	end if;
	if ClearDenominator then
	    print "Numerator:";
	    print num;
	end if;
	return num, den;
	// return num/den;
    elif Al eq "Modular" and ModelType eq "Dedekind eta" then
	num, den := DCIModularCompute(N);
	DBMP := ModularPolynomialDatabase();
	Phi := ModularPolynomial(DBMP,"Dedekind eta",N);
	FF := FunctionField(RationalField()); x := FF.1;
	PF := PolynomialRing(FF); J := PF.1;
	KK<j> := FunctionField(Evaluate(Phi,[x,J]));
	return Evaluate(num,[x,j]), Evaluate(den,[x,j]);
	// return Evaluate(num,[x,j])/Evaluate(den,[x,j]);
    elif Al eq "Modular" and ModelType eq "Atkin" then
	num, den := ACIModularCompute(N);
	FF := FunctionField(RationalField()); x := FF.1;
	PF := PolynomialRing(FF); J := PF.1;
	// Need to remove common denominators...
	numseq := [ PolynomialRing(Integers())!Numerator(c)
	    : c in Eltseq(Evaluate(num,[x,J])) ];
	d1 := UnivariatePolynomial(den);
	d0 := GCD(numseq cat [d1]);
	vprint ModularPolynomial :
	    "Removing denominator of degree", Degree(d0);
	P2 := Parent(num); X := P2.1; J := P2.2;
	num := &+[ Evaluate(numseq[i] div d0,X)*J^(i-1) : i in [1..#numseq] ];
	den := Evaluate(d1 div d0,X);
	// Now the num and den are coprime.
	J := PF.1; // reset J
	DBMP := ModularPolynomialDatabase();
	Phi := ModularPolynomial(DBMP,"Atkin",N);
	KK<j> := FunctionField(Evaluate(Phi,[x,J]));
	return Evaluate(num,[x,j]), Evaluate(den,[x,j]);
	// return Evaluate(num,[x,j])/Evaluate(den,[x,j]);
    elif Al eq "Integral" then
	require ModelType eq "Dedekind eta" :
	    "Argument 1 must \"Dedekind eta\".";
	num, den := DCIIntegralCompute(N);
	DBMP := ModularPolynomialDatabase();
	Phi := ModularPolynomial(DBMP,"Dedekind eta",N);
	FF := FunctionField(RationalField()); x := FF.1;
	PF := PolynomialRing(FF); J := PF.1;
	KK<j> := FunctionField(Evaluate(Phi,[x,J]));
	FF := FunctionField(RationalField()); x := FF.1;
	return Evaluate(num,[x,j]), Evaluate(den,[x,j]);
	// return Evaluate(num,[x,j])/Evaluate(den,[x,j]);
    end if;
end intrinsic;

function DCIIntegralCompute(N)
    DBMP := ModularPolynomialDatabase();
    Phi := ModularPolynomial(DBMP,"Dedekind eta",N);
    PQ := PolynomialRing(RationalField());
    FF := FunctionField(RationalField());
    x := FF.1;
    PF := PolynomialRing(FF);
    j := PF.1;
    disc := Numerator(FF!Discriminant(Evaluate(Phi,[x,j])));
    fac := Factorization(disc);
    den := &*[ PQ | f[1]^(f[2] div 2) : f in fac | f[1] ne x ];
    if GCD(N-1,12) eq N-1 then
	den *:= PQ.1^N;
    else 
	den *:= PQ.1^GCD(N-1,12);
    end if;
    print "Denominator:";
    print den;
    deg := Degree(den);
    I, s, t, u := DCIMonomialExponents(N,deg);
    prec := deg*u + N + 32;
    vprint ModularPolynomial : "Precision =", prec;
    vprint ModularPolynomial : "Number of terms =", #I;
    tyme := Cputime();
    PS := LaurentSeriesRing(RationalField());
    q := PS.1;
    oerr := O(q^prec);
    f := CanonicalDedekind(PS,N,prec);
    j := jInvariant(q + oerr);
    rel := jInvariant(q^N + oerr) * Evaluate(den,f);
    vprint ModularPolynomial : "Series computation time:", Cputime(tyme);
    d1 := Max([ n[1] : n in I ]);
    d2 := Max([ n[2] : n in I ]);
    tyme := Cputime();
    fs := [ PS!1 ];
    for k in [1..d1] do
	Append(~fs,fs[k]*f + oerr);
    end for;
    vprint ModularPolynomial : "Eta powers time:", Cputime(tyme);
    tyme := Cputime();
    js := [ PS!1 ];
    for k in [1..d2] do
	Append(~js,js[k]*j);
    end for;
    vprint ModularPolynomial : "J-invariant powers time:", Cputime(tyme);
    tyme := Cputime();
    S := [ fs[n[1]+1]*js[n[2]+1] + O(q^prec) : n in I ];
    vprint ModularPolynomial : "Power series sequence time:", Cputime(tyme);
    tyme := Cputime();
    V := LinearRelations([-rel] cat S);
    vprintf ModularPolynomial :
        "Found solution space of dimension %o and degree %o.\n",
        Dimension(V), Degree(V);
    error if Dimension(V) ne 1, "Precision error.";
    vprint ModularPolynomial : "Linear algebra time:", Cputime(tyme);
    c0 := Eltseq(Basis(V)[1]);
    ChangeUniverse(~c0,Integers());
    P2<X,J> := PolynomialRing(Integers(),2);
    return &+[ c0[i+1]*X^I[i][1]*J^I[i][2] : i in [1..#I] ],
        Evaluate(PolynomialRing(Integers())!den,X);
end function;

function DedekindEtaDenominator(N)
    DBMP := ModularPolynomialDatabase();
    Phi := ModularPolynomial(DBMP,"Dedekind eta",N);
    FF := FunctionField(Integers()); x := FF.1;
    PF := PolynomialRing(FF); J := PF.1;
    PZ := PolynomialRing(Integers());
    disc := PZ!Numerator(FF!Discriminant(Evaluate(Phi,[x,J])));
    fac := Factorization(disc);
    den := &*[ PZ | f[1]^(f[2] div 2) : f in fac | f[1] ne x ];
    if GCD(N-1,12) eq N-1 then den *:= PZ.1^N;
    else den *:= PZ.1^GCD(N-1,12);
    end if;
    return den;
end function;

function DCIModularCompute(N)
    den := DedekindEtaDenominator(N);
    deg := Degree(den);
    I, s, t, u := DCIMonomialExponents(N,deg);
    prec := deg*u + N + 32;
    rems := [ ]; 
    mods := [ Integers() | ];
    m := 1;
    char := PreviousPrime(Floor(2^23.5));
    stable := false;
    zz_coeffs := [ 0 : i in [1..#I] ];
    while not stable do
	if N eq char then char := PreviousPrime(char); end if;
	vprint ModularPolynomial : "Modular prime =", char;
	m *:= char;
	tyme := Cputime();
	ff_coeffs := DCILocalCompute(N,den,char);
	vprint ModularPolynomial : "Modular computation time:", Cputime(tyme);
	Append(~rems,ff_coeffs);
	Append(~mods,char);
	new_coeffs := [ BalancedMod( CRT(
    	    [ coeffs[i] : coeffs in rems ],mods), m ) : i in [1..#I] ];
	vprintf ModularPolynomial : "(#NonZero, #Zero) = (%o,%o)\n",
 	    #[ I[i] : i in [1..#I] | new_coeffs[i] ne 0 ],	
	    #[ I[i] : i in [1..#I] | new_coeffs[i] eq 0 ];	
        vprint ModularPolynomial : "Zero exps:";
        vprint ModularPolynomial : 
	    [ I[i] : i in [1..#I] | new_coeffs[i] eq 0 ];	
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
        char := PreviousPrime(char);
    end while;
    P2<X,J> := PolynomialRing(Integers(),2);
    return &+[ zz_coeffs[j]*X^I[j][1]*J^I[j][2] : j in [1..#I] ],
        Evaluate(PolynomialRing(Integers())!den,X);
end function;

function DCILocalCompute(N,den,char)
    K := FiniteField(char);
    deg := Degree(den);
    den := PolynomialRing(K)!den;
    I, s, t, u := DCIMonomialExponents(N,deg);
    prec := deg*u + N + 32;
    vprint ModularPolynomial : "Precision =", prec;
    vprint ModularPolynomial : "Number of terms =", #I;
    vprint ModularPolynomial : "Characteristic =", char;
    tyme := Cputime();
    PS := LaurentSeriesRing(GF(char)); q := PS.1;
    oerr := O(q^prec);
    f := CanonicalDedekind(PS,N,prec);
    j := jInvariant(q + oerr);
    rel := jInvariant(q^N + oerr) * Evaluate(den,f);
    vprint ModularPolynomial : "Generating series time:", Cputime(tyme);

    d1 := Max([ n[1] : n in I ]);
    d2 := Max([ n[2] : n in I ]);
    tyme := Cputime();
    fs := [ PS!1 ];
    for k in [1..d1] do
	Append(~fs,fs[k]*f + oerr);
    end for;
    vprint ModularPolynomial : "Eta powers time:", Cputime(tyme);
    tyme := Cputime();
    js := [ PS!1 ];
    for k in [1..d2] do
	Append(~js,js[k]*j);
    end for;
    vprint ModularPolynomial : "J-invariant powers time:", Cputime(tyme);
    tyme := Cputime();
    S := [ fs[n[1]+1]*js[n[2]+1] + O(q^prec) : n in I ];
    vprint ModularPolynomial : "Full series sequence time:", Cputime(tyme);
    tyme := Cputime();
    V := LinearRelations([-rel] cat S);
    vprintf ModularPolynomial :
        "Found solution space of dimension %o and degree %o.\n",
        Dimension(V), Degree(V);
    error if Dimension(V) ne 1, "Precision error.";
    vprint ModularPolynomial : "Linear algebra time:", Cputime(tyme);
    return ChangeUniverse(Eltseq(Basis(V)[1])[2..Degree(V)],Integers());
end function;   

function AtkinDenominator(N)
    DBMP := ModularPolynomialDatabase();
    Phi := ModularPolynomial(DBMP,"Atkin",N);
    FF := FunctionField(Integers()); x := FF.1;
    PF := PolynomialRing(FF); J := PF.1;
    PZ := PolynomialRing(Integers());
    disc := PZ!Numerator(FF!Discriminant(Evaluate(Phi,[x,J])));
    fac := Factorization(disc);
    if true then
	den := fac[#fac][1];
	val := fac[#fac][2];
	if Degree(den) le 2 then
	    den := PZ!1;
	    vprint ModularPolynomial : "Using denominator 1";
	else 
	    vprint ModularPolynomial : 
	        "Using denominator of degree =", Degree(den);
	    vprint ModularPolynomial : "Valuation:", val;
	end if;
    else 
	den := &*[ PZ | f[1]^(f[2] div 2) : f in fac ];
	vprint ModularPolynomial :
	    "Using denominator of degree:", Degree(den);
    end if;
    return den*PZ.1^8;
end function;

function ACIModularCompute(N)
    DBMP := ModularPolynomialDatabase();
    Phi := ModularPolynomial(DBMP,"Atkin",N);
    den := AtkinDenominator(N);
    deg := Degree(den);
    I := ACIMonomialExponents(N,Degree(Phi,2),deg);
    rems := [ ]; 
    mods := [ Integers() | ];
    m := 1;
    char := PreviousPrime(Floor(2^23.5));
    stable := false;
    zz_coeffs := [ 0 : i in [1..#I] ];
    while not stable do
	if N eq char then char := PreviousPrime(char); end if;
	vprint ModularPolynomial : "Modular prime =", char;
	m *:= char;
	tyme := Cputime();
	ff_coeffs := ACILocalCompute(N,den,char);
	vprint ModularPolynomial : "Modular computation time:", Cputime(tyme);
	Append(~rems,ff_coeffs);
	Append(~mods,char);
	new_coeffs := [ BalancedMod( CRT(
    	    [ coeffs[i] : coeffs in rems ],mods), m ) : i in [1..#I] ];
	vprintf ModularPolynomial : "(#NonZero, #Zero) = (%o,%o)\n",
 	    #[ I[i] : i in [1..#I] | new_coeffs[i] ne 0 ],	
	    #[ I[i] : i in [1..#I] | new_coeffs[i] eq 0 ];	
        vprint ModularPolynomial : "Zero exps:";
        vprint ModularPolynomial : 
	    [ I[i] : i in [1..#I] | new_coeffs[i] eq 0 ];	
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
        char := PreviousPrime(char);
    end while;
    P2<X,J> := PolynomialRing(Integers(),2);
    vprint ModularPolynomial :
        "Returning with denominator of degree", Degree(den);
    return &+[ zz_coeffs[j]*X^I[j][1]*J^I[j][2] : j in [1..#I] ],
           Evaluate(PolynomialRing(Integers())!den,X);
end function;

function AtkinModularSeries(N,q,prec)
    DBMP := ModularPolynomialDatabase();
    Phi := ModularPolynomial(DBMP,"Atkin",N);
    PS := Parent(q);
    PP := PolynomialRing(PS); u := PP.1;
    r := Degree(Phi,2) div 2;
    oerr := O(q^prec);
    j := jInvariant(q + oerr);
    F1 := q^(r*(N+1))*Evaluate(Phi,[q^-r*u,j]);
    vprint ModularPolynomial : "Hensel lifting Atkin series...";
    f1 := NewtonLift(F1,PS!1,prec);
    return q^-r*f1;
end function;

function ACILocalCompute(N,den,char)
    DBMP := ModularPolynomialDatabase();
    Phi := ModularPolynomial(DBMP,"Atkin",N);
    den := PolynomialRing(GF(char))!den;
    deg := Degree(den);
    d2 := Degree(Phi,2);
    I := ACIMonomialExponents(N,d2,deg);
    prec := (N + deg)*d2 + 64;
    vprint ModularPolynomial : "Characteristic =", char;
    vprint ModularPolynomial : "Number of terms =", #I;
    vprint ModularPolynomial : "Precision =", prec;
    tyme := Cputime();
    PS := LaurentSeriesRing(GF(char)); q := PS.1;
    oerr := O(q^prec);
    f := AtkinModularSeries(N,q,prec);
    j := jInvariant(q + oerr);
    rel := jInvariant(q^N + oerr) * Evaluate(den,f);
    vprint ModularPolynomial : "Generating series time:", Cputime(tyme);
    d1 := Max([ n[1] : n in I ]);
    d2 := Max([ n[2] : n in I ]);
    tyme := Cputime();
    fs := [ PS!1 ];
    for k in [1..d1] do
	Append(~fs,fs[k]*f + oerr);
    end for;
    vprint ModularPolynomial : "Atkin series powers time:", Cputime(tyme);
    tyme := Cputime();
    js := [ PS!1 ];
    for k in [1..d2] do
	Append(~js,js[k]*j);
    end for;
    vprint ModularPolynomial : "J-invariant powers time:", Cputime(tyme);
    tyme := Cputime();
    S := [ fs[n[1]+1]*js[n[2]+1] + O(q^prec) : n in I ];
    vprint ModularPolynomial : "Full series sequence time:", Cputime(tyme);
    tyme := Cputime();
    V := LinearRelations([-rel] cat S);
    vprintf ModularPolynomial :
        "Found solution space of dimension %o and degree %o.\n",
            Dimension(V), Degree(V);
    error if Dimension(V) ne 1, "Precision error.";
    vprint ModularPolynomial : "Linear algebra time:", Cputime(tyme);
    return ChangeUniverse(Eltseq(Basis(V)[1])[2..Degree(V)],Integers());
end function;   

