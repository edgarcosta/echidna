//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
> FF := GF(2);
> P2<x,y,z> := ProjectiveSpace(FF,2);
> C := Curve(P2, x^5 + y^2*z^3 + y*z^4);
> FrobeniusCharacteristicPolynomial(C);
x^4 + 4
*/

intrinsic '#'(X::Sch) -> RngIntElt // [FldFin]) -> RngIntElt
    {The number of points on X by enumeration of points.}
    // Remark: This is a really stupid algorithm, but # is missing
    // from all but special curve types: CrvCon, CrvEll, CrvHyp.
    // Just to get it working ***without calling zeta function***,
    // I define it here as the enumeration of the rational points.
    require Type(BaseRing(X)) eq FldFin :
	"Argument must be defined over a finite field.";
    return #Ratpoints(X);
end intrinsic;

/*
intrinsic '#'(X::SetPt[FldFin]) -> RngIntElt
    {The number of points on X by enumeration of points.}
    // Remark: This is a really stupid algorithm, but # is missing
    // from all but special curve types: CrvCon, CrvEll, CrvHyp.
    // Just to get it working ***without calling zeta function***,
    // I define it here as the enumeration of the rational points.
    return #Ratpoints(X);
end intrinsic;

intrinsic '#'(X::SetPtHyp[FldFin]) -> RngIntElt
    {The number of points on X by enumeration of points.}
    // Remark: This is a really stupid algorithm, but # is missing
    // from all but special curve types: CrvCon, CrvEll, CrvHyp.
    // Just to get it working ***without calling zeta function***,
    // I define it here as the enumeration of the rational points.
    return #Ratpoints(X);
end intrinsic;
*/

intrinsic FrobeniusCharacteristicPolynomial(C::Crv[FldFin] : Al := "") -> RngUPolElt
    {The characteristic polynomial of Frobenius (of the normalization of C).}
    FF := BaseRing(C); q := #FF;
    if Al eq "" then
	Al := q lt 10^8 select "Enumeration" else "FunctionField";
	if IsSingular(C) then Al := "FunctionField"; end if;
    end if;
    if Al eq "FunctionField" then
	chi := Numerator(ZetaFunction(C));
	return Polynomial(Reverse(Eltseq(chi)));
    elif Al eq "Enumeration" then
	p := Characteristic(FF);
	r := Degree(FF);
	case Genus(C):
	when 0:
	    return Polynomial([1]);
	when 1:
	    t := q + 1 - #C;
	    return Polynomial([q,-t,1]);
	when 2:
	    s1 := q + 1 - #C;
	    if q le 1000 then
		t2 := q^2 + 1 - #BaseExtend(C,FiniteField(q^2));
		s2 := (s1^2 - t2) div 2;
	    else
		// #J = chi(1) = (1 + q^2) - s1*(1 + q) + s2
		J := Jacobian(C);
		s2 := #J - (1 + q^2) + s1*(1 + q);
	    end if;
	    return Polynomial([q^2,-s1*q,s2,-s1,1]);
	when 3:
	    if Type(C) eq CrvHyp then
		// Use #C, N1 = #J(C) and N2 = #J(C') for the quadratic twist C'.
		// #C = q + 1 - s1,
		// N1 = chi(+1) = (1 + q)^3 - s1*(1 + q)^2 + s2*(1 + q) - s3,
		// N2 = chi(-1) = (1 + q)^3 + s1*(1 + q)^2 + s2*(1 + q) + s3.
		s1 := q + 1 - #C;
		N1 := #Jacobian(C);
		N2 := #Jacobian(QuadraticTwist(C));
		M1 := N1 - (1 + q)^3 + s1*(1 + q)^2;
		M2 := N2 - (1 + q)^3 - s1*(1 + q)^2;
		assert (M1 + M2) mod (2 + 2*q) eq 0;
		s2 := (M1 + M2) div (2 + 2*q);
		assert (M1 + M2) mod 2 eq 0;
		s3 := (M2 - M1) div 2;
		assert N1 eq (1 + q)^3 - s1*(1 + q)^2 + s2*(1 + q) - s3;
		assert N2 eq (1 + q)^3 + s1*(1 + q)^2 + s2*(1 + q) + s3;
	    else
		return ReciprocalPolynomial(Numerator(ZetaFunction(C)));
	    end if;
	    x := PolynomialRing(IntegerRing()).1;
	    return (x^2 + q)^3 - s1*(x^2 + q)^2*x + s2*(x^2 + q)*x^2 - s3*x^3;
	else
	    /*
	    g := Genus(C);
	    NumPts := [ Integers() | ];
	    for m in [1..g] do
		Append(~NumPts,#C(FiniteField(p,r*m)));
	    end for;
	    t := PowerSeriesRing(RationalField()).1;
	    f := Exp(&+[ (NumPts[m]-q^m-1)*t^m/m : m in [1..g] ] + O(t^(g+1)));
	    c := ChangeUniverse(Eltseq(f),IntegerRing());
	    c cat:= [ 0 : i in [1..g+1-#c] ];
	    x := PolynomialRing(Integers()).1;
	    return Polynomial([ q^(g-i)*c[i+1] : i in [0..g] ] cat [ c[g+1-i] : i in [1..g] ]);
	    */
	    return ReciprocalPolynomial(Numerator(ZetaFunction(C)));
	end case;
    else
	require false : "Algorithm (= " * Al * ") must be in {\"FunctionField\",\"Enumeration\"}.";
    end if;
end intrinsic;

intrinsic FrobeniusCharacteristicPolynomial(J::JacHyp[FldFin]) -> RngUPolElt
    {The characteristic polynomial of Frobenius.}
    return FrobeniusCharacteristicPolynomial(Curve(J));
end intrinsic;

intrinsic ZetaFunctionSeries(C::Crv[FldFin],n::RngIntElt) -> RngUPolElt
    {The initial section of the zeta funtion, up to degree n, using naive enumeration.}
    K := BaseField(C);
    q := #K;
    p := Characteristic(K);
    r := Degree(K);
    NumPts := [ Integers() | ]; 
    for m in [1..n] do
	Append(~NumPts,#RationalPoints(C,FiniteField(p,r*m)));
    end for;
    PS := PowerSeriesRing(RationalField());
    T := PS.1;
    return Exp(&+[ PS | (NumPts[m]-q^m-1)*T^m/m : m in [1..n] ] + O(T^(n+1)));
end intrinsic;

intrinsic FrobeniusCharacteristicPolynomialTwists(zeta::RngUPolElt[RngInt]) -> SeqEnum
    {The sequence of all twists of a given Frobenius charpoly.}
    zeta_cffs := Coefficients(zeta);
    require Degree(zeta) mod 2 eq 0 : "Argument must have even degree.";
    g := Degree(zeta) div 2;
    bool, p, s := IsPrimePower(zeta_cffs[1]);
    require bool and s mod g eq 0 : "Argument must be a Frobenius charpoly."; 
    r := s div g; q := p^r;
    require &and[ zeta_cffs[i+1] eq q^(g-i)*zeta_cffs[2*g+1-i] : i in [1..g] ] : 
	"Argument must be a Frobenius charpoly #2.";
    require zeta_cffs[g+1] mod p ne 0 :
	"Argument must be an ordinary Frobenius charpoly.";
    PZ := PolynomialRing(Integers()); x := PZ.1;
    zeta_list := [ PZ | ];
    if IsIrreducible(zeta) then
        K := NumberField(zeta);
        return QuarticCMFieldOrdinaryFrobeniusCharpolys(K,p,r);
    else
        // When constructing this list we should consider when
        // the quadratic CM field has discriminant -3, -4.
        fac := Factorization(zeta);
        assert &and[ Degree(fac[i][1]) eq 2 : i in [1..#fac] ];
        chi_seq := { };
        for ff in fac do
            chi := ff[1];
	    if chi in chi_seq then
		continue; // e.g. chi2(x) = chi1(ux)
	    end if;
	    chi_seq_i := [ chi ];
            D := Discriminant(chi);
            if IsSquare(-3*D) then
                K<pi> := NumberField(chi);
                bool, u := HasRoot(Polynomial([K|1,1,1])); assert bool;
                Append(~chi_seq_i,MinimalPolynomial(u*pi));
                Append(~chi_seq_i,MinimalPolynomial(u^2*pi));
            elif IsSquare(-4*D) then
                K<pi> := NumberField(chi);
                bool, u := HasRoot(Polynomial([K|1,0,1])); assert bool;
                Append(~chi_seq_i,MinimalPolynomial(u*pi));
            end if;
            // Extend chi_seq by the negations...
            chi_seq join:= &join[ { chi, Evaluate(chi,-x) } : chi in chi_seq_i ];
	end for;
        zeta_list := { xi1 * xi2 : xi1, xi2 in chi_seq };
    end if;
    return Sort(SetToSequence(zeta_list));
end intrinsic;

