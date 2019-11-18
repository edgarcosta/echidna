////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   CORRESPONDENCES ON MODULAR CURVES                //
//                      Last modified February 2001                   //
//                             David Kohel                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

forward BalancedMod, MCModularCompute, MCComputeRelation;
forward AMCIntegralCompute, DMCIntegralCompute; 

intrinsic ModularCorrespondence(
    ModelType::MonStgElt, N::RngIntElt, p::RngIntElt :
    Al := "Modular", ModularFunction := 0,
    InitialModulus := 0, IncrementModulus := false)
    -> RngMPolElt
    {A polynomial defining the modular correspondence X_0(pN) ->
    X_0(N) x X_0(N) (or on the Atkin-Lehner quotient X_0^+(N).)} 

    require ModelType in {"Atkin","Dedekind eta"} : 
	"Argument 1 must be \"Atkin\" or \"Dedekind eta\".";
    if ModelType eq "Atkin" then
	require N in {2,3,5,7,11,13,17,19,23,29,31,41,47,59,71} : 
	    "Argument 2 must in {2,3,5,7,11,13,17,19,23,29,31,41,47,59,71}.";
    else
	require N in {2,3,4,5,7,9,13,25} : "Argument 2 must in {2,3,4,5,7,9,13,25}.";
    end if;
    require IsPrime(p) : "Argument 3 must be prime.";
    require Al in {"Integral","Modular"} : 
        "Parameter Al must be either \"Integral\" or \"Modular\".";
    if ModelType eq "Dedekind eta" then Al := "Integral"; end if;
    if Al eq "Modular" then
	return MCModularCompute(ModelType,N,p :
	    ModularFunction := ModularFunction,
	    InitialModulus := InitialModulus,
	    IncrementModulus := IncrementModulus);
    elif ModelType eq "Atkin" then
	return AMCIntegralCompute(N,p : ModularFunction := ModularFunction);
    else // ModelType eq "Dedekind eta"
	return DMCIntegralCompute(N,p : ModularFunction := ModularFunction);
    end if;
end intrinsic;

function AMCIntegralCompute(N,p : ModularFunction := 0)
    if N eq p then
	deg := 2*p;
	tot := 3*p-1;
    else
	deg := p+1;
	tot := 2*p;
    end if;
    prec := deg*(deg + 3);
    PS := LaurentSeriesRing(Integers()); q := PS.1;
    if ModularFunction eq 0 then
	DBAS := AtkinModularFunctionDatabase();
	f := AtkinModularFunction(DBAS,N,prec);
    else
	t := Parent(ModularFunction).1;
	f := PS!(ModularFunction + O(t^prec));
    end if;
    g := Evaluate(f+O(q^prec),q^p+O(q^prec)) + O(q^prec);
    PZ := PolynomialRing(Integers(),2 : Global);
    return PZ!AlgebraicRelations([f,g], [deg,deg], tot)[1];
end function;
    
function DMCIntegralCompute(N,p : ModularFunction := 0)
    PS := LaurentSeriesRing(Integers()); q := PS.1;
    prec := p^2+p+1;
    if N eq p then
	prec *:= 2;
    end if;
    if ModularFunction eq 0 then
	f := CanonicalDedekind(PS,N,Max(N+1,prec)) + O(q^prec);
    else
	f := PS!(ModularFunction + O(q^prec));
    end if;
    g := Evaluate(f+O(q^prec),q^p+O(q^prec)) + O(q^prec);
    Sf := [ PS!1 ];
    Sg := [ PS!1 ];
    for i in [1..p+1] do
	Append(~Sf,Sf[i]*f);
	Append(~Sg,Sg[i]*g);
    end for;
    RelSeq := [ PS | ];
    PZ := PolynomialRing(Integers(),2 : Global);
    u1 := PZ.1; u2 := PZ.2;
    mons := [ PZ | ];
    if N ne p then
	Append(~RelSeq,Sf[p+2]+Sg[p+2]);
	Append(~mons,u1^(p+1)+u2^(p+1));
    end if;
    for i in [p..0 by -1] do
	for j in [i..0 by -1] do
	    if i eq j then
		Append(~RelSeq,Sf[i+1]*Sg[i+1]);
		Append(~mons,u1^i*u2^i);
	    elif N eq p then
		Append(~RelSeq,Sf[i+1]*Sg[j+1]);
		Append(~mons,u1^i*u2^j);
		Append(~RelSeq,Sf[j+1]*Sg[i+1]);
		Append(~mons,u1^j*u2^i);
	    else
		Append(~RelSeq,Sf[i+1]*Sg[j+1] + Sf[j+1]*Sg[i+1]);
		Append(~mons,u1^i*u2^j + u1^j*u2^i);
	    end if;
	end for;
    end for;
    V := LinearRelations(RelSeq);
    c := Basis(V)[1];
    if N eq p then
	if c[Index(mons,u1^p)] eq -1 then c *:= -1; end if;
    end if;
    return &+[ c[k]*mons[k] : k in [1..#mons] ];
end function;

function MCMonomialExponents(ModelType,N,p)
    exps := [];
    if N ne p then
	deg := p+1;
	tot := 2*p;
    elif ModelType eq "Atkin" then
	deg := 2*p;
	tot := 3*p - 1;
    end if;
    max := deg - 1;
    exps := [ [deg,0] ] cat
	&cat[ [ [i,j] : j in [i..0 by -1] | i+j le tot ] : i in [max..0 by -1] ];
    return exps;
end function;

function MCLocalCompute(ModelType,N,p,char : ModularFunction := 0)
    assert N ne p or ModelType eq "Atkin";
    I := MCMonomialExponents(ModelType,N,p);
    if ModelType eq "Atkin" then
	prec := deg*(deg + 3) where deg := N eq p select 2*p else p+1;	
    else // ModelType eq "Dedekind eta" 
	prec := p^2+p+1;
    end if;
    vprint ModularPolynomial : "Precision =", prec;
    vprint ModularPolynomial : "Number of terms =", #I;
    tyme := Cputime();
    PS := LaurentSeriesRing(FiniteField(char)); q := PS.1;
    if ModularFunction ne 0 then
	t := Parent(ModularFunction).1;
	f := PS!(ModularFunction + O(t^prec));
    elif ModelType eq "Atkin" then
	DBAS := AtkinModularFunctionDatabase();
	f := PS!AtkinModularFunction(DBAS,N,prec);
    else // ModelType eq "Dedekind eta" 
	f := CanonicalDedekind(PS,N,Max(N+1,prec))+O(q^prec);
    end if;
    g := Evaluate(f+O(q^prec),q^p+O(q^prec)) + O(q^prec);
    vprint ModularPolynomial : "Generator series time:", Cputime(tyme);
    V := MCComputeRelation(ModelType,N,p,f,g,prec);
    vprintf ModularPolynomial :
        "Found solution space of dimension %o and degree %o.\n",
        Dimension(V), Degree(V);
    if Dimension(V) ne 1 then
	print "dim(V) =", Dimension(V);
	print BasisMatrix(V);
	error if Dimension(V) ne 1, "Precision error.";
    end if;
    return ChangeUniverse(Eltseq(Basis(V)[1]),Integers());
end function;   

function MCModularCompute(ModelType,N,p :
    ModularFunction := 0, InitialModulus := 0, IncrementModulus := false)
    assert N ne p or ModelType eq "Atkin";
    I := MCMonomialExponents(ModelType,N,p);
    if ModularFunction eq 0 then
	PS := LaurentSeriesRing(Integers()); q := PS.1;
	if ModelType eq "Atkin" then
	    prec := deg*(deg + 3) where deg := N eq p select 2*p else p+1;	
	    DBAS := AtkinModularFunctionDatabase();
	    ModularFunction := PS!AtkinModularFunction(DBAS,N,prec);
	else // ModelType eq "Dedekind eta" 
	    prec := p^2+p+1;
	    ModularFunction := CanonicalDedekind(PS,N,Max(N+1,prec))+O(q^prec);
	end if;
    end if;
    rems := [ ]; 
    mods := [ Integers() | ];
    m := 1;
    if IncrementModulus then
	char := 2^12;
	NextModulus := NextPrime;
    else
	char := Floor(2^23.5);
	NextModulus := PreviousPrime;
    end if;
    if InitialModulus ne 0 then
	char := InitialModulus;
    end if;
    stable := false;
    zz_coeffs := [ 0 : i in [1..#I] ];
    while not stable do
	char := NextModulus(char);
	while char in {N,p} do
	    char := NextModulus(char);
	end while;
	vprint ModularPolynomial : "Modular prime =", char;
	m *:= char;
	tyme := Cputime();
	ff_coeffs := MCLocalCompute(
	    ModelType,N,p,char : ModularFunction := ModularFunction);
	vprint ModularPolynomial : "Modular computation time:", Cputime(tyme);
	Append(~rems,ff_coeffs);
	Append(~mods,char);
	new_coeffs := [ BalancedMod( CRT(
    	    [ coeffs[i] : coeffs in rems ],mods), m ) : i in [1..#I] ];
	vprintf ModularPolynomial : "(#Nonzero, #Zero) = (%o,%o)\n",
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
    end while;
    PZ := PolynomialRing(Integers(),2 : Global);
    u1 := PZ.1; u2 := PZ.2;
    mons := [ e[1] eq e[2] select u1^e[1]*u2^e[2]
	else u1^e[1]*u2^e[2] + u1^e[2]*u2^e[1] : e in I ];
    return &+[ zz_coeffs[j] * mons[j] : j in [1..#I] ];
end function;

function MCComputeRelation(ModelType,N,p,f,g,prec)
    assert N ne p or ModelType eq "Atkin";
    PS := Parent(f); q := PS.1;
    if N ne p then
	deg := p+1;
    else // ModelType eq "Atkin" then
	deg := 2*p;
    end if;
    oerr := O(q^prec);
    tyme := Cputime();
    fs := [ 1 + oerr ];
    for k in [1..deg] do
	Append(~fs,fs[k]*f + oerr);
    end for;
    vprint ModularPolynomial, 2 : "Series 1 powers time:", Cputime(tyme);
    tyme := Cputime();
    gs := [ 1 + oerr ];
    for k in [1..deg] do
	Append(~gs,gs[k]*g);
    end for;
    vprint ModularPolynomial, 2 : "Series 2 powers time:", Cputime(tyme);
    tyme := Cputime();
    RelSeq := [ PS | ];
    if N ne p then
	max := p;
	tot := 2*p;
    else // ModelType eq "Atkin" then
	max := 2*p - 1;
	tot := 3*p - 1;
   end if;
    Append(~RelSeq,fs[deg+1]+gs[deg+1]);
    for i in [max..0 by -1] do
	for j in [i..0 by -1] do
	    if i+j le tot then
		if i eq j then
		    Append(~RelSeq,fs[i+1]*gs[i+1]);
		else
		    Append(~RelSeq,fs[i+1]*gs[j+1] + fs[j+1]*gs[i+1]);
		end if;
	    end if;
	end for;
    end for;
    vprint ModularPolynomial : "Series sequence time:", Cputime(tyme);
    tyme := Cputime();
    V := LinearRelations(RelSeq);
    vprint ModularPolynomial : "Linear algebra time:", Cputime(tyme);
    return V;
end function;   

function BalancedMod(a,m)
    t := m div 2;
    a mod:= m;
    if a le t then return a;
    else return a-m;
    end if;
end function;
