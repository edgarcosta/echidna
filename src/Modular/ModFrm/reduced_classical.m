////////////////////////////////////////////////////////////////////////
//                                                                    //
//               REDUCED CLASSICAL MODULAR POLYNOMIALS                //
//                          February 2001                             //
//                           David Kohel                              //
//                                                                    //
////////////////////////////////////////////////////////////////////////

forward BalancedMod, RMPLocalRelation;

////////////////////////////////////////////////////////////////////////
//                        Accessory Function                          //
////////////////////////////////////////////////////////////////////////

function Exps(N)
    // Caution: This is purely empirically determined!!!
    if IsPrime(N) then
	if N mod 3 eq 1 then
	    s := 2; 
	    exps := Reverse( Sort(
	        [ [N+1,0] ] cat
	        [ [i,i] : i in [0..N] | i mod 3 eq 1 ] cat 
	        [ [j,i] : i, j in [0..N] |
		    i lt j and (i + N*j) mod 3 eq s ] ) );
	    exps := [ Reverse(n) : n in exps ];
	else
	    s := 0;
	    exps := Reverse( Sort(
	        [ [N+1,0] ] cat
	        [ [i,i] : i in [N..0 by -1] ] cat 
	        [ [j,i] : i, j in [0..N] |
             	    i lt j and (i + N*j) mod 3 eq s ] ) );
	    exps := [ Reverse(n) : n in exps ];
	end if;
    else
        // No idea, but the exponent sequence is definitely too large.
	r := &*[ (p+1)*p^Valuation(N div p,p) : p in PrimeDivisors(N) ];
	exps := [ [0,r] ] cat [ [i,j] : i, j in [0..r-1] | i le j ];
    end if;
    return exps;
end function;

////////////////////////////////////////////////////////////////////////
//                    Reduced Modular Polynomial                      //
////////////////////////////////////////////////////////////////////////

intrinsic ReducedClassicalModularPolynomial(N::RngIntElt : 
    Al := "Integral") -> RngMPolElt 
    {The reduced classical modular polynomial relating j(q)^(1/3)
    and j(q^N)^(1/3).} 
    require N ge 1 : "Argument must be positive.";
    require GCD(N,3) eq 1 : "Argument must be coprime to 3.";
    require Al in {"Integral","Modular"} :
        "Al parameter must be either \"Modular\" or \"Integral\".";
    if Al eq "Modular" then
	mods := [ Integers() | ];
	r := &*[ (p+1)*p^Valuation(N div p,p) : p in PrimeDivisors(N) ]; 
	exps := Exps(N);
	rems := [ ]; 
        prec := Max([ n[1]+N*n[2] : n in exps ]) + N + 1;
        vprint ModularPolynomial : "Level =", N;
        vprint ModularPolynomial : "Working precision =", prec;
	vprint ModularPolynomial : "Number of terms =", #exps;
	m := 1;
        p := PreviousPrime(Floor(2^29));
	stable := false;
	zz_coeffs := [ 1 ] cat [ 0 : i in [2..#exps] ];
        stables := [ 1 ];
	while not stable do
	    while N mod p eq 0 do p := PreviousPrime(p); end while;
	    vprint ModularPolynomial : "Modular prime =", p;
	    m *:= p;
	    tyme := Cputime();
   	    coeffs := RMPLocalRelation(N,p,stables, zz_coeffs);
	    coeffs := ChangeUniverse(coeffs,Integers());
	    Append(~rems,coeffs);
	    Append(~mods,p);
	    new_coeffs := [
               BalancedMod( CRT([ coeffs[i] : coeffs in rems ],mods), m )
	          : i in [1..#exps] ];
	    vprintf ModularPolynomial : "(#NonZero, #Zero) = (%o,%o)\n",
 	        #[ exps[i] : i in [1..#exps] | new_coeffs[i] ne 0 ],	
	        #[ exps[i] : i in [1..#exps] | new_coeffs[i] eq 0 ];	
            stable := &and[ zz_coeffs[i] eq new_coeffs[i] : i in [1..#exps] ];
	    zz_coeffs := new_coeffs;
	    mod_size := Ceiling(Log(10,m));
	    coeff_size := Max([ Ceiling(Log(10,1+Abs(c))) : c in zz_coeffs ]);
	    if coeff_size le mod_size - 4 then stable := true; end if;
	    stables := [ i : i in [1..#zz_coeffs] | 
	        Ceiling(Log(10,1+Abs(zz_coeffs[i]))) le mod_size-8 ];
	    vprintf ModularPolynomial :
  	        "Modulus size is %o digits.\n", mod_size;
	    vprintf ModularPolynomial :
	        "Max coefficient size is %o digits.\n", coeff_size;
	    vprintf ModularPolynomial :
	        "Completed %o coefficients, %o remaining.\n", 
	        &+[ Integers() | 1 : c in zz_coeffs |
	              Ceiling(Log(10,1+Abs(c))) le mod_size - 4 ],
	        &+[ Integers() | 1 : c in zz_coeffs |
	              Ceiling(Log(10,1+Abs(c))) gt mod_size - 4 ];
	    vprint ModularPolynomial :
	        "Modular computation time:", Cputime(tyme);
	    p := PreviousPrime(p);
	end while;
	P2 := PolynomialRing(Integers(),2);
	X := P2.1; Y := P2.2;
	return &+[ zz_coeffs[Index(exps,n)] * (
	    n[1] eq n[2] select X^n[1]*Y^n[2] 
	    else X^n[1]*Y^n[2] + Y^n[1]*X^n[2] ) : n in exps ];
    end if;
    return ReducedClassicalModularPolynomial(N,Integers()); 
end intrinsic;  
 
intrinsic ReducedClassicalModularPolynomial(N::RngIntElt,K::Rng) -> RngMPolElt 
    {The reduced classical modular polynomial over K relating j(q)^(1/3)
    and j(q^N)^(1/3).} 

    require N ge 1 : "Argument must be positive.";
    require GCD(N,3) eq 1 : "Argument must be coprime to 3.";
    P2 := PolynomialRing(K,2);
    X := P2.1; Y := P2.2;
    if N eq 1 then return X-Y; end if;
    r := &*[ (p+1)*p^Valuation(N div p,p) : p in PrimeDivisors(N) ]; 
    exps := Exps(N);
    prec := Max([ n[1]+N*n[2] : n in exps ]) + N + 1;
    vprint ModularPolynomial : "Level =", N;
    vprint ModularPolynomial : "Working precision =", prec;
    vprint ModularPolynomial : "Number of terms =", #exps;
    // Temporary workaround... 
    if IsField(K) then
	PP := PuiseuxSeriesRing(K);
    elif Type(K) eq RngInt then
	PP := PuiseuxSeriesRing(RationalField());
    end if;
    t := PP.1;
    terr := O(t^prec);
    PS := LaurentSeriesRing(K);
    q := PS.1;
    oerr := O(q^prec);
    tyme := Cputime();
    j3 := jInvariant(t^3 + terr);
    P := PolynomialRing(PP);
    T := P.1; 
    j1 := PS!NewtonLift(T^3-j3,1/t,prec) + oerr;
    vprint ModularPolynomial : "Generator j(q), time:", Cputime(tyme);
    tyme := Cputime();
    j2 := Evaluate(j1,q^N + oerr);
    vprintf ModularPolynomial :
    "Generator j(q^%o), time: %o\n", N, Cputime(tyme);
    j1s := [ 1 + oerr ];
    tyme := Cputime();
    for i in [1..r] do
	Append(~j1s,j1s[i]*j1 + oerr);
    end for;
    vprint ModularPolynomial : "Power sequence 1 time:", Cputime(tyme);
    tyme := Cputime();
    j2s := [ 1 + oerr ];
    for i in [1..r] do
	Append(~j2s,j2s[i]*j2 + oerr);
    end for;
    vprint ModularPolynomial : "Power sequence 2 time:", Cputime(tyme);
    tyme := Cputime();
    Series := [
           n[1] eq n[2] select
               j1s[n[1]+1]*j2s[n[2]+1] + O(q)
           else
	       j1s[n[1]+1]*j2s[n[2]+1] + j2s[n[1]+1]*j1s[n[2]+1] + O(q)
       : n in exps ]; 
    vprint ModularPolynomial : "Series computation time:", Cputime(tyme);
    Series := [ f + O(q) : f in Series ];
    tyme := Cputime();
    V := LinearRelations(Series);
    require Dimension(V) ne 0 : "Failed to find a dependency."; 
    require Dimension(V) eq 1 : "Found too many dependencies."; 
    vprint ModularPolynomial : "Linear algebra time:", Cputime(tyme);
    vprintf ModularPolynomial :
        "Found solution space of dimension %o and degree %o.\n",
        Dimension(V), Degree(V);
    coeffs := Eltseq(Basis(V)[1]);
    return &+[ coeffs[Index(exps,n)]*(
               n[1] eq n[2] select X^n[1]*Y^n[2] 
               else X^n[1]*Y^n[2] + Y^n[1]*X^n[2] ) : n in exps ];
end intrinsic;  
 
function RMPLocalRelation(N, p, stables, zz_coeffs )
    K := FiniteField(p);
    r := &*[ (t+1)*t^Valuation(N div t,t) : t in PrimeDivisors(N) ]; 
    exps := Exps(N);
    vals := [ Min(-N*n[1]-n[2],-n[1]-N*n[2]) : n in exps ];
    pivots := Sort(SetToSequence(SequenceToSet(vals)));
    prec := N + 1 - Min(vals);
    vprint ModularPolynomial : "Level =", N;
    vprint ModularPolynomial : "Working precision =", prec;
    vprint ModularPolynomial : "Number of terms =", #exps;
    PP := PuiseuxSeriesRing(K);
    t := PP.1;
    terr := O(t^prec);
    PS := LaurentSeriesRing(K);
    q := PS.1;
    oerr := O(q^prec);
    tyme := Cputime();
    j3 := jInvariant(t^3 + terr);
    P := PolynomialRing(PP);
    T := P.1; 
    j1 := PS!NewtonLift(T^3-j3,1/t,prec) + oerr;
    vprint ModularPolynomial : "Generator j(q), time:", Cputime(tyme);
    tyme := Cputime();
    j2 := Evaluate(j1,q^N + oerr);
    vprintf ModularPolynomial :
        "Generator j(q^%o), time: %o\n", N, Cputime(tyme);
    j1s := [ 1 + oerr ];
    tyme := Cputime();
    for i in [1..r] do
	Append(~j1s,j1s[i]*j1 + oerr);
    end for;
    vprint ModularPolynomial : "Power sequence 1 time:", Cputime(tyme);
    tyme := Cputime();
    j2s := [ 1 + oerr ];
    for i in [1..r] do
	Append(~j2s,j2s[i]*j2 + oerr);
    end for;
    vprint ModularPolynomial : "Power sequence 2 time:", Cputime(tyme);
    tyme := Cputime();
    Series := [ n[1] eq n[2] select j1s[n[1]+1]*j2s[n[2]+1] + O(q)
           else j1s[n[1]+1]*j2s[n[2]+1] +
                j2s[n[1]+1]*j1s[n[2]+1] + O(q) : n in exps ]; 
    vprint ModularPolynomial : "Series computation time:", Cputime(tyme);
    tyme := Cputime();
    if #stables eq 0 then
	oldis := [ 1 ];
	coeffs := [ K | 1 ];
    else
	oldis := stables;
	coeffs := [ K | zz_coeffs[i] : i in stables ];
    end if;
    for n in pivots do
	newis := [ i : i in [1..#vals] | vals[i] eq n and i notin oldis ];
        if #newis ne 0 then
	    oerr := O(q^(n+1));
	    fz := &+[ coeffs[i]*(Series[oldis[i]] + oerr) : i in [1..#oldis] ];
	    S := [ fz ] cat [ Series[i] + oerr : i in newis ]; 
	    V := LinearRelations(S);
	    j := 0;
	    while Dimension(V) eq 0 and #stables gt 0 do
		j +:= 2;
		vprint ModularPolynomial : "Failed to find a dependency.";
		vprint ModularPolynomial : "Pivot =", n;
		vprint ModularPolynomial : "Valuation(fz) =", Valuation(fz);
		vprint ModularPolynomial : "All vals =", [ Valuation(f) : f in S ];
		vprint ModularPolynomial :
 	            "Revising stable indices down from # =", #stables;
		mod_size := Max([
		    Ceiling(Log(10,1+Abs(c))) : c in zz_coeffs ]);
		excls := stables; // (tmp indices)
		stables := [ i : i in [1..#zz_coeffs] | 
		    Ceiling(Log(10,1+Abs(zz_coeffs[i]))) le mod_size-6-j ];
		excls := [ i : i in excls | i notin stables ];
		vprint ModularPolynomial : "...to # =", #stables;
		coeffs := [ coeffs[i] :
		    i in [1..#oldis] | oldis[i] notin excls ];
		oldis := [ oldis[i] :
		    i in [1..#oldis] | oldis[i] notin excls ];  
		newis := [ i : i in [1..#vals] |
		        vals[i] le n and i notin oldis ];  
		fz := &+[ coeffs[i]*(Series[oldis[i]] + oerr) : i in [1..#oldis] ];
		S := [ fz ] cat [ Series[i] + oerr : i in newis ]; 
		V := LinearRelations(S);
		V0 := LinearRelations(Series);
		if Dimension(V) ge 1 then
		    printf "Found relation space of size %o and degree %o",
		    Dimension(V), Degree(V);
		end if;
	    end while;
	    error if Dimension(V) eq 0, "Failed to find a dependency.";
	    error if Dimension(V) gt 1, "Found too many dependencies."; 
	    new_coeffs := Eltseq(Basis(V)[1]);
	    assert new_coeffs[1] eq 1;
	    coeffs cat:= new_coeffs[2..#new_coeffs];
	    oldis cat:= newis;
	end if;
    end for;
    vprint ModularPolynomial : "Linear algebra time:", Cputime(tyme);
    return [ coeffs[Index(oldis,i)] : i in [1..#exps] ];
end function;
 
function BalancedMod(a,m)
   a mod:= m;
   t := m div 2;
   if a le t then return a;
   else return a-m;
   end if;
end function;


