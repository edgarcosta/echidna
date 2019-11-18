//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function IsConsistentH1RandomPrime(H1,DAB,n)
    K := QuarticCMField(DAB);
    O := MaximalOrder(K);
    D := DAB[1];
    while true do
	p := RandomPrime(n);
	while KroneckerSymbol(D,p) ne 1 do
	    p := RandomPrime(n);
	end while;
	prms := Decomposition(O,p);
	if #prms eq 4 then
	    if &and[ IsPrincipal(pp[1]) : pp in prms ] then
		break;
	    end if;
	end if;
    end while;
    _, degs := QuarticCMFieldOrdinaryWeilNumbers(K,p);
    degs_set := SequenceToSet(degs);
    for r in degs_set do
	FF := FiniteField(p,r);
	PF := PolynomialRing(FF);
	rts := Roots(PolynomialRing(FF)!H1);
	if #degs eq 2 and #degs_set eq 1 then
	    if #rts ne Degree(H1) then
		return false, p;
	    elif #rts lt Degree(H1) div 2 then
		return false, p;
	    end if;
	end if;
    end for;
    return true, p;
end function;

function IsValidLIXClassPolyH1(H1,DAB,prec :
    SmoothnessCheck := true, SmoothnessBound := 10^7, LatticeDimension := 0)
    RR := RealField(8);
    if LatticeDimension eq 0 then
	deg := Degree(H1);
    else
	deg := LatticeDimension-1;
    end if;
    short := RR!prec/deg;
    long := 1.33 * short;
    m1 := RR!Log(10,Max([ Abs(c) : c in Eltseq(H1) ])) + 8;
    bool := m1 le short;
    if m1 le long and not bool then
	bool, p := IsConsistentH1RandomPrime(H1,DAB,32);
    end if;
    if not bool then
	if GetVerbose("IgusaInvariant") gt 0 then
	    printf "H1 coefficient size fails: %o > %o\n",  m1, short;
	    print "H1:";
	    print H1;
	end if;
	return false, Min(Ceiling((deg+2)*m1),2*prec);
    end if;
    if not SmoothnessCheck then return true, _; end if;
    lc_facts, lc_unfacts := TrialDivision(LeadingCoefficient(H1),SmoothnessBound);
    lc_primes := [ p[1] : p in lc_facts ] cat lc_unfacts;
    if Max([1] cat lc_primes) gt SmoothnessBound then
	if GetVerbose("IgusaInvariant") gt 0 then
	    print "Leading coefficient factorization fails:";
	    print [ Sprintf("%o^%o",p[1],p[2]) : p in lc_facts] cat [ Sprint(p) : p in lc_unfacts ];
	    print "H1:";
	    print H1;
	end if;
	return false, Floor(1.414*prec);
    end if;
    return true, prec;
end function;

function IsValidLIXClassPolyNi(Ni,prec)
    RR := RealField(16);
    if Ni eq 0 then return false, Floor(1.414*prec); end if;
    Ni_facts, Ni_unfacts := TrialDivision(Ni,10^6);
    Ni_facts := [ p[1] : p in Ni_facts ] cat Ni_unfacts;
    if Max([1] cat Ni_facts) gt 10^8 then
	return false, Floor(1.32*prec);
    end if;
    return true, prec;
end function;

function IsValidLIXClassPolyGi(IgLIX,prec : PrecisionBase := 10, LatticeDimension := 0)
    deg := LatticeDimension eq 0 select Degree(IgLIX[1][1]) else LatticeDimension-1;
    RR := RealField(16);
    short := RR!prec/deg;
    for j in [2..#IgLIX] do
	Gj := IgLIX[j][1]; Nj := IgLIX[j][2];
	mj := RR!Log(PrecisionBase,Max([ Abs(RR!c) : c in Eltseq(Gj) ] cat [Nj])) + 8;
	if mj ge short then
	    vprintf IgusaInvariant : "G%o coefficient size fails: %o > %o\n", j, mj, short;
	    return false, Min(Ceiling((deg+1)*mj),Floor(1.414*prec));
	end if;
	vprintf IgusaInvariant : "G%o coefficient size passes: %o < %o\n", j, mj, short;
    end for;
    return true, prec;
end function;

//////////////////////////////////////////////////////////////////////////////

intrinsic IsConsistentIgusaLIXInvariants(IgLIX::SeqEnum[Tup]) -> BoolElt
    {Given a putative sequence of Igusa LIX CM invariants, verify that the sequence
    is consistent with being a sequence of Igusa LIX CM invariants.}
    H1 := IgLIX[1][1];
    lc_facts, lc_unfacts := TrialDivision(LeadingCoefficient(H1),10^6);
    lc_facts := [ p[1] : p in lc_facts ] cat lc_unfacts;
    if Max([1] cat lc_facts) gt 10^8 then
	return false;
    end if;
    if IgLIX[2][2] eq 0 then return false; end if;
    N2_facts, N2_unfacts := TrialDivision(IgLIX[2][2],10^6);
    N2_facts := [ p[1] : p in N2_facts ] cat N2_unfacts;
    if Max([1] cat N2_facts) gt 10^8 then
	return false;
    end if;
    if IgLIX[3][2] eq 0 then return false; end if;
    N3_facts, N3_unfacts := TrialDivision(IgLIX[3][2],10^6);
    N3_facts := [ p[1] : p in N3_facts ] cat N3_unfacts;
    if Max([1] cat N3_facts) gt 10^8 then
	return false;
    end if;
    return true;
end intrinsic;

intrinsic IsConsistentIgusaLIXInvariants(
    IgLIX::SeqEnum[Tup],DAB::SeqEnum[RngIntElt],p::RngIntElt) -> BoolElt
    {Given a putative sequence of Igusa LIX CM invariants, quartic CM field invariants DAB, 
    and a prime p of good ordinary reduction, verify that the reduction at p  of the Igusa LIX
    invariants is consistent with being CM invariants of the quartic CM field.}

    K := QuarticCMField(DAB);
    weil_nums, degs, units := QuarticCMFieldOrdinaryWeilNumbers(K,p);
    n := #weil_nums;
    require n gt 0 : "Argument 3 must be a prime of good ordinary reduction.";
    for r in degs do
	weil_pols := &cat[ [ MinimalPolynomial(u*weil_nums[i]^(degs[i] div r)) : u in units ] : i in [1..n] | r mod degs[i] eq 0 ];
	vprintf IgusaInvariant : "p^r = %o^%o\n", p, r;
	FF := FiniteField(p,r);
	JJ_seqs := IgusaLIXToIgusaInvariants(IgLIX,FF : ExactDegree := true);
	vprint IgusaInvariant : JJ_seqs;
	JJ_orbs := {@ @};
	for JJ in JJ_seqs do
	    if JJ notin &join JJ_orbs then
		Include(~JJ_orbs,{ [ jj^p^i : jj in JJ ] : i in [0..r-1] });
	    end if;
	end for;
	bool := false;
	for oo in JJ_orbs do
	    JJ := Representative(oo);
	    C := HyperellipticCurveFromIgusaInvariants(JJ);
	    chi := FrobeniusCharacteristicPolynomial(C);
	    if Coefficient(chi,2) mod p eq 0 then
		vprintf IgusaInvariant : "  Frobenius charpoly: %o (%o)\n", chi, "not ordinary";
		continue;
	    else
		bool := chi in weil_pols;
		vprintf IgusaInvariant : "  Frobenius charpoly: %o (%o)\n", chi, bool;
		if not bool then return false; end if;
	    end if;
	end for;
	// there should have been at least one orbit with good ordinary reduction:
	if not bool then return false; end if;
    end for;
    return true;
end intrinsic;

intrinsic IsConsistentIgusaLIXInvariantsInitialPrimes(
    IgLIX::SeqEnum[Tup],DAB::SeqEnum[RngIntElt],n::RngIntElt) -> BoolElt, SeqEnum
    {Given a putative sequence of Igusa LIX CM invariants, quartic
    CM field invariants DAB, and a bound n, verify that the primes of
    good ordinary among the first n primes, are consistent with being
    CM invariants of the quartic CM field.}
    K := QuarticCMField(DAB);
    prms := [ pp[1] : pp in QuarticCMFieldOrdinaryPrimes(K,n) ];
    for p in prms do
	bool := IsConsistentIgusaLIXInvariants(IgLIX,DAB,p);
	if not bool then return false, [ p ]; end if;
    end for;
    return true, prms;
end intrinsic;

function RandomOrdinaryPrime(K,bits)
    assert bits ge 16;
    D, A, B := Explode(QuarticCMFieldInvariants(K));
    ZZ := IntegerRing();
    if QuarticCMFieldType(K) eq [2,2] then
        Dr_seq := [ Discriminant(Ki) : Ki in QuarticCMReflexFields(K) ];
        repeat
            p := RandomPrime(bits : Proof := false);
        until &and[ KroneckerSymbol(Dr,p) eq 1 : Dr in Dr_seq ];
        return p;
    end if;
    Kr := QuarticCMReflexField(K);
    Or := MaximalOrder(Kr);
    Br := [ xr : xr in Basis(Or) ];
    Bound := 2^(bits div 4);
    Ir := [-Bound..Bound];
    repeat
	p := ZZ!Norm(Norm(&+[ Random(Ir)*x : x in Br ]));
    until IsProbablePrime(p);
    return p;
end function;

intrinsic IsConsistentIgusaLIXInvariantsRandomPrime(
    IgLIX::SeqEnum[Tup],DAB::SeqEnum[RngIntElt],n::RngIntElt :
    ReflexField := false, Conductor := []) -> BoolElt, RngIntElt
    {Given a putative sequence of Igusa LIX CM invariants, quartic
    CM field invariants DAB, and a bit bound n, verify that the reduction
    at a random n-bit prime of good ordinary reduction, is consistent
    with being CM invariants of the quartic CM field.}
    K := QuarticCMField(DAB);
    /*
    if QuarticCMFieldType(K) eq [2,2] then
        require Type(ReflexField) ne BoolElt : "A ReflexField must be specified for biquadratic fields.";
    end if;
    */
    O := MaximalOrder(K);
    D := DAB[1];
    N := Conductor eq [] select 1 else Conductor[#Conductor];
    repeat
	p := RandomOrdinaryPrime(K,n);
    until KroneckerSymbol(D,p) eq 1; // and (p - 1) mod N^2 eq 0;
    FF := FiniteField(p);
    P<x> := PolynomialRing(GF(p));
    pi_seq, degs_maximal := QuarticCMFieldOrdinaryWeilNumbers(K,p);
    vprint IgusaInvariant : "Splitting degrees for maximal order:", degs_maximal;
    /* In order to catch nonmaximal orders we need to consider the actual splitting degrees: */
    facs := Factorization(P!IgLIX[1][1]);
    /* We are assuming that n is sufficiently large that there is no ramification: */
    if not &and[ f[2] eq 1 : f in facs ] then
	print "p =", p;
	print "Factorization:";
	print facs;
	if Conductor eq [] then
	    require false : "Argument 3 must be sufficiently large to effectively prescribe ramification.";
	end if;
    end if;
    degs := [ Degree(f[1]) : f in facs ];
    /* If there exists a factor which is not a multiple of a splitting degree
    for the maximal order then we may return false immediately. */
    if not &and[ &or[ r mod deg eq 0 : deg in degs_maximal ] : r in degs ] then
	vprintf IgusaInvariant : "  ...inconsistent degrees %o:\n", degs;
	return false, p;
    end if;
    vprintf IgusaInvariant : "Testing split prime p = %o:\n", p;
    for r in [Min(degs)] do
	vprintf IgusaInvariant : "  ...and degree r = %o:\n", r;
	F_seq := QuarticCMFieldOrdinaryFrobeniusCharpolys(K,p,r);
	N_seq := [ Evaluate(chi,1) : chi in F_seq ];
	vprint IgusaInvariant : "Frobenius charpolys";
	vprint IgusaInvariant : F_seq;
	KK := FiniteField(p,r);
	JJ_seq := IgusaLIXToIgusaInvariants(IgLIX,GF(p,r) : ExactDegree);
        if r eq 1 then
            vprintf IgusaInvariant : "Found %o invariants over FF_%o:\n", #JJ_seq, p;
        else
            vprintf IgusaInvariant : "Found %o invariants over FF_%o^%o:\n", #JJ_seq, p, r;
        end if;
	bool := true;
	if #JJ_seq eq 0 then return false, p; end if;
        for JJ in JJ_seq do
	    C := HyperellipticCurveFromIgusaInvariants(JJ);
	    J := Jacobian(C);
	    bool and:= &or[ N*Random(J) eq J!0 : N in N_seq ];
            vprintf IgusaInvariant : "JJ = %o: %o\n", JJ, bool;
	    if not bool then
		return false, p;
	    end if;
	end for;
    end for;
    return true, p;
end intrinsic;

/*
function IsQuarticCMFieldInvariants(DAB)
    if #DAB ne 3 then
	return false;
    end if;
    D, A, B := Explode(DAB);
    if D le 0 or D mod 4 notin {0,1} then
	return false;
    end if;
    if IsSquare(D) or not IsFundamental(D) then
	return false;
    end if;
    r := A^2-4*B mod D;
    m := A^2-4*B div D;
    if r eq 0 or IsSquare(m) then
	return false;
    end if;
    return true;
end function;

intrinsic GorenLauterPrimes(
    DAB1::SeqEnum[RngIntElt],DAB2::SeqEnum[RngIntElt]) -> SeqEnum
    {}
    require IsQuarticCMFieldInvariants(DAB1) : 
	"Argument 1 must specify quartic CM field invariants.";
    require IsQuarticCMFieldInvariants(DAB2) :  
	"Argument 2 must specify quartic CM field invariants.";
    K1 := QuarticCMField(DAB1); DK1 := Discriminant(K1) div DAB1[1];
    K2 := QuarticCMField(DAB2); DK2 := Discriminant(K2) div DAB2[1];
    e := 1 - (DK1 mod 2)*(DK2 mod 2);
    D := DK1*DK2; M := Isqrt(D);
    prms := [];
    for t in [e..M by 2] do
	printf "t = %o < %o\n", t, M;
	prms cat:= Factorization((D - t) div 4);
	print prms;
    end for;
    return SetToSequence(SequenceToSet([ p[1] : p in prms ]));
end intrinsic;
*/
