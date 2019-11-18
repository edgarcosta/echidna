//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//         Copyright (C) 2008 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic pNonmaximalEndomorphismOrders(chi::RngUPolElt,l::RngIntElt) -> SeqEnum
    {Given the minimal polynomial of Frobenius, return the sequence
    of orders between Z[\pi,\bar\pi] and O_K which are closed under
    complex conjugation and p-maximal at all primes p \ne l.}

    q2g := Coefficient(chi,0); 
    K<pi> := NumberField(chi);
    cc := ComplexConjugation(K);
    bool, p := IsPrimePower(q2g);
    require bool : "Argument 1 must be a Weil polynomial.";
    g := Valuation(q2g,p) div 2;
    q := p^g;
    OK := MaximalOrder(K);
    cond := FrobeniusVerschiebungConductorAbelianInvariants(chi);
    prms := PrimeDivisors(cond[#cond]);
    O := sub< OK | pi, q/pi >; //assert q/pi eq cc(pi);
    for p in prms do
	if p eq l then continue; end if;
	B := Basis(pMaximalOrder(O,p));
	O := sub< OK | Basis(O) cat B cat [ cc(x) : x in B ] >;
    end for;
    return O;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic FrobeniusConductorAbelianInvariants(J::JacHyp[FldFin]) -> SeqEnum[RngInt]
    {The abelian invariants of the group O_K/Z[\pi].}
    chi :=  FrobeniusCharacteristicPolynomial(J);
    return FrobeniusConductorAbelianInvariants(chi);
end intrinsic;

intrinsic FrobeniusVerschiebungConductorAbelianInvariants(J::JacHyp[FldFin]) -> SeqEnum[RngInt]
    {The abelian invariants of the group O_K/Z[\pi,\bar\pi].}
    chi :=  FrobeniusCharacteristicPolynomial(J);
    return FrobeniusVerschiebungConductorAbelianInvariants(chi);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic FrobeniusVerschiebungRealSubringConductorAbelianInvariants(J::JacHyp[FldFin]) -> SeqEnum[RngInt]
    {The abelian invariants of the group O_F/(Z[\pi,\bar\pi] \cup O_F) where F is the totally real subfield of K.}
    chi :=  FrobeniusCharacteristicPolynomial(J);
    return FrobeniusVerschiebungRealSubringConductorAbelianInvariants(chi);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

/*
intrinsic ConductorAbelianInvariants(J::JacHyp[FldFin],l::RngIntElt) -> SeqEnum[RngInt]
    {}
    FF := BaseField(J);
    require Type(FF) eq FldFin :
	"Argument must be defined over a finite field.";
    require IsPrime(l) : "Argument 2 must be prime.";
    g := Dimension(J);
    q := #FF;
    p := Characteristic(FF);
    chi := FrobeniusCharacteristicPolynomial(J);
    K<pi> := NumberField(chi);
    O := MaximalOrder(K);
    R := EquationOrder(K);
    n := (Valuation(Discriminant(R),l) div 2);
    S := sub< O | pi >;
    M := Matrix(Integers(),[ Eltseq(O!x) : x in Basis(S) ]);
    deg := Degree(chi);
    A := FreeAbelianGroup(deg);
    B, m := quo< A | [ A!Eltseq(M[i]) : i in [1..deg] ] >;
    gens := [ g : g in Generators(B) ];
    ords := [ Order(g) : g in gens ];
    fncs := [ ords[i]*K!O!Eltseq(gens[i]@@m) : i in [1..#gens] ];
    fncs := [ PolynomialRing(Integers()) | 
	ChangeUniverse(Eltseq(f),Integers()) : f in fncs ];
    exp := Exponent(B);
    print "fncs:", fncs;
    if l eq p then
	for k in [1..Valuation(exp,l)] do
	    print "  k =", k;
	    LL, s := MaximalOrderTorsionSplittingField(chi,l,k);
	    print "  Splitting degree:", Degree(LL);
	    JL := BaseChange(J,LL);
	    Gl, ii := TorsionSubgroup(JL,l^k);
	    Jl := [ ii(g) : g in Generators(Gl) ];
	    for i in [1..#gens] do
		if ords[i] mod l^k eq 0 then
		    zero := true;
		    // print fncs[i];
		    for P in Jl do
			Q := FrobeniusApplication(fncs[i],P,FF);
			if Q ne JL!0 then
			    zero := false;
			    // print "Nonzero image, breaking...";
			    break P;
			end if;
		    end for;
		    if zero then
			// print "Extending endomorphism ring...";
			S := sub< O | Evaluate(fncs[i],pi)/l^k, Basis(S) >;
		    end if;
		end if;
	    end for;
	end for;
    elif l ne p then
	for k in [1..Valuation(exp,l)] do
	    print "  k =", k;
	    LL, s := MaximalOrderTorsionSplittingField(chi,l,k);
	    vprint EndomorphismRing : "  Splitting degree:", Degree(LL);
	    JL := BaseChange(J,LL);
	    Gl, ii := TorsionSubgroup(JL,l^k);
	    Jl := [ ii(g) : g in Generators(Gl) ];
	    if #Jl ne 2*g then
		printf "%o^%o torsion is not full, breaking\n", l, k;
		break k;
	    end if;
	    for i in [1..#gens] do
		if ords[i] mod l^k eq 0 then
		    zero := true;
		    print fncs[i];
		    for P in Jl do
			Q := FrobeniusApplication(fncs[i],P,FF);
			if Q ne JL!0 then
			    zero := false;
			    // print "Nonzero image, breaking...";
			    break P;
			end if;
		    end for;
		    if zero then
			// print "Extending endomorphism ring...";
			S := sub< O | Evaluate(fncs[i],pi)/l^k, Basis(S) >;
		    end if;
		end if;
	    end for;
	end for;
    end if;
    S := sub< O | Basis(S) cat [ l^n*x : x in Basis(O) ] >;
    M := Matrix(Integers(),[ Eltseq(O!x) : x in Basis(S) ]);
    deg := Degree(chi);
    A := FreeAbelianGroup(deg);
    B, m := quo< A | [ A!Eltseq(M[i]) : i in [1..deg] ] >;
    return AbelianInvariants(B);
end intrinsic;
*/

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic FrobeniusConductorAbelianInvariants(chi::RngUPolElt[RngInt]) -> SeqEnum[RngInt]
    {The abelian invariants of the group O_K/Z[\pi].}
    n := Degree(chi);
    _, q := IsPower(Integers()!Coefficient(chi,0),n div 2);
    K<pi> := NumberField(chi);
    O := MaximalOrder(K);
    R := sub< O | pi >;
    M := Matrix(Integers(),[ Eltseq(O!x) : x in Basis(R) ]);
    A := FreeAbelianGroup(n);
    B := quo< A | [ A!Eltseq(M[i]) : i in [1..n] ] >;
    return AbelianInvariants(B);
end intrinsic;

intrinsic FrobeniusVerschiebungConductorAbelianInvariants(chi::RngUPolElt[RngInt] :
    TorsionSubgroup := 1,
    TorsionSubgroupTwist := 1,
    TorsionSubgroupExtensionDegree := 1) -> SeqEnum[RngInt]
    {The abelian invariants of the group O_K/Z[\pi,\bar\pi].}
    n := Degree(chi);
    ell := TorsionSubgroup;
    twst := TorsionSubgroupTwist;
    deg := TorsionSubgroupExtensionDegree;
    require Type(ell) eq RngIntElt and ell gt 0 :
	"Parameter \"TorsionSubgroup\" must be a positive integer.";
    require Type(twst) eq RngIntElt and twst in {1,-1}:
	"Parameter \"TorsionSubgroupTwist\" must be an integer in {1,-1}.";
    require Type(deg) eq RngIntElt and deg gt 0:
	"Parameter \"TorsionSubgroupExtensionDegree\" must be a positive integer.";
    _, q := IsPower(Integers()!Coefficient(chi,0),n div 2);
    K<pi> := NumberField(chi);
    O := MaximalOrder(K);
    if ell eq 1 then
	R := sub< O | pi, q/pi >;
    else
	if twst eq 1 then
	    R := sub< O | pi, q/pi, (pi^deg-1)/ell >;
	elif twst eq -1 then
	    R := sub< O | pi, q/pi, ((q/pi)^deg-1)/ell >;
	end if;
    end if;
    M := Matrix(Integers(),[ Eltseq(O!x) : x in Basis(R) ]);
    A := FreeAbelianGroup(n);
    B := quo< A | [ A!Eltseq(M[i]) : i in [1..n] ] >;
    return AbelianInvariants(B);
end intrinsic;

intrinsic FrobeniusVerschiebungRealSubringConductorAbelianInvariants(chi::RngUPolElt[RngInt]) -> SeqEnum[RngInt]
    {The abelian invariants of the group O_F/(Z[\pi,\bar\pi] \cup O_F) where F is the totally real subfield of K.}
    deg := Degree(chi);
    g := deg div 2;
    bool, q := IsPower(Coefficient(chi,0),g);
    require IsIrreducible(chi) and deg mod 2 eq 0 and bool : "Argument must be a Weil polynomial.";
    s := [ (-1)^(deg-i)*Coefficient(chi,2*g-i) : i in [1..g] ];
    require &and[ (-1)^i*s[i]*q^(g-i) eq Coefficient(chi,i) : i in [1..g] ] : "Argument must be a Weil polynomial.";
    require IsIrreducible(chi) : "Argument must be an irreducible Weil polynomial.";
    if Degree(chi) eq 4 then
	return [ Isqrt(D2 div FundamentalDiscriminant(D2)) ] where D2 := s[1]^2 - 4*s[2] + 8*q;
    end if;
    require false : "Not implemented for g > 2.";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

