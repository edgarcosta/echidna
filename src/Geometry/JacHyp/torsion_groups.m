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

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic TorsionSubgroup(G::GrpAb,n) -> GrpAb, Map
    {The subgroup of n-torsion elements of G.}
    gens := [ g : g in Generators(G) ];
    ords := [ Order(g) : g in gens ];
    return sub< G | [ (ords[i] div GCD(n,ords[i]))*gens[i] : i in [1..#ords] ] >;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic MaximalOrderTorsionSplittingField(J::JacHyp[FldFin],l::RngIntElt) -> FldFin, RngIntElt
    {The field over which the l-torsion subgroup splits completely for an
    abelian variety with the same Frobenius charpoly and maximal endomorphism ring.}
    require IsPrime(l) : "Argument 2 must be prime.";
    zeta :=  FrobeniusCharacteristicPolynomial(J);
    return MaximalOrderTorsionSplittingField(zeta,l,1);
end intrinsic;

intrinsic MaximalOrderTorsionSplittingField(J::JacHyp[FldFin],l::RngIntElt,n::RngIntElt) -> FldFin, RngIntElt
    {The field over which the l^n-torsion subgroup splits completely for an
    abelian variety with the same Frobenius charpoly and maximal endomorphism ring.}
    zeta :=  FrobeniusCharacteristicPolynomial(J);
    return MaximalOrderTorsionSplittingField(zeta,l,n);
end intrinsic;

function SylowOrder(P,p,n);
    // Given a point P on a Jacobian, a prime p, and an exponent n,
    // return the order of P (= p^k for some k).
    Z := Parent(P)!0;
    if P eq Z then return 1; end if;
    k := 0;
    while k lt n do
	k +:= 1;
	P *:= p;
	if P eq Z then
	    return p^k;
	end if;
    end while;
    return p^n;
end function;

function IntegerToIntegerBaseSequence(k,m,r)
    // Create a bijection [0..m^r-1] -> (Z/mZ)^r.
    if m eq 1 then
	return [ 0 : i in [1..r] ];
    end if;
    I := IntegerToSequence(k,m);
    while #I lt r do
	I cat:= [0];
    end while;
    return I;
end function;

function IntegerBaseSequenceToInteger(I,m,r)
    // Create a bijection (Z/mZ)^r -> [0..m^r-1].
    return &+[ I[i]*m^(i-1) : i in [1..r] ];
end function;

function pTorsionRelation(p,gens,Q)
    /*
    Find a relation vector for the p-torsion element Q in terms of 
    the p-torsion elements gens, or return the zero vector if none
    exists.  Assumes that gens admit no relations.

    TODO: Make use of the Weil pairing when the p-rank is large.
    TODO: For small p improve the baby-step algorithm; in particular
    for p = 2 the baby steps are the full set of p^#gens elements.
    */
    if #gens eq 0 then
	return Vector([0]);
    end if;
    J := Universe(gens);
    assert p*Q eq J!0;
    assert &and[ p*P eq J!0 : P in gens ];
    r := #gens;
    vprintf EndomorphismRing : "  Finding %o-torsion relation in group of rank: %o\n", p, r;
    /*
    tyme := Cputime();
    print "  Weil pairings (not using):";
    for i in [1..r] do
	print "    ", WeilPairing(gens[i],Q,p);
    end for;
    print "  Weil pairing time:", Cputime(tyme);
    */
    // Set up the BabySteps...
    BabySteps := {@ J | @};
    m0 := Isqrt(p);
    m1 := Ceiling(p/m0);
    gen_pows := [ [ Universe(gens)!0 ] : i in [1..r] ];
    for i in [1..m0] do
	for j in [1..r] do
	    Append(~gen_pows[j],gen_pows[j][i] + gens[j]);
	end for;
    end for;
    for k in [0..m0^r-1] do
	k0 := IntegerToIntegerBaseSequence(k,m0,r);
	Include(~BabySteps,&+[ J | gen_pows[i][k0[i]+1] : i in [1..r] ]);
    end for;
    if #BabySteps ne m0^r then
	// Dump debugging information:
	FF<t> := BaseRing(J);
	PF<x> := PolynomialRing(FF);
	print "Defining polynomials of curve:";
	print HyperellipticPolynomials(Curve(J));
	print "#BabySteps:", #BabySteps;
	print "m0^r:", m0^r;
	printf "(m0,r) = (%o,%o)\n", m0, r;
	print "Generators:"; gens;
	if #BabySteps lt 32 then
	    print BabySteps;
	end if;
	assert #BabySteps eq m0^r;
    end if;
    assert &and[
	&+[ J | a0[i] * gens[i] : i in [1..r] ] eq BabySteps[k0+1]
	where a0 := IntegerToIntegerBaseSequence(k0,m0,r) : k0 in [0..m0^r-1] ];
    gens_m0 := [ gen_pows[j][m0+1] : j in [1..r] ]; 
    for k in [0..m1^r-1] do
	a1 := IntegerToIntegerBaseSequence(k,m1,r+1);
	// This is silly, but let's get it working before optimizing the additions:
	k0 := Index(BabySteps,Q + &+[ a1[i] * gens_m0[i] : i in [1..r] ]);
	if k0 ne 0 then break; end if;
    end for;
    if k0 eq 0 then
	aa := [ 0 : i in [1..r+1] ];
    else
	a0 := IntegerToIntegerBaseSequence(k0-1,m0,r) cat [-1];
	assert &+[ a0[i] * gens[i] : i in [1..r] ] eq BabySteps[k0];
	assert &+[ a0[i] * gens[i] : i in [1..r] ] eq Q + &+[ a1[i] * gens_m0[i] : i in [1..r] ];
	assert &+[ (a0[i] - m0*a1[i]) * gens[i] : i in [1..r] ] eq Q;
	aa := [ (-a0[i] + m0*a1[i]) mod p : i in [1..r+1] ];
    end if;
    vprintf EndomorphismRing, 2 : "    %o-torsion relation vector: %o\n", p, aa;
    assert &+[ aa[i] * gens[i] : i in [1..r] ] eq  -aa[r+1]*Q;
    return Vector(aa);
end function;

function SylowSubgroupReduction(p,genords1,genords2)
    /*
    Given a prime p, and tuples genords1 & 2 such that
         genords1 = <gens1, ords1>,
         genords2 = <gens2, ords2>,
    where gens1 and gens2 are sequences of p-power-torsion generators, with
    orders given by ords1 and ords2.  We assume that gens1 are independent
    (i.e. AbelianGroup(ords1) gives the group structure they generate),
    determine the group generated by gens1 and gens2.
    */ 
    gens1 := genords1[1]; ords1 := genords1[2];
    if #gens1 eq 0 then
	return genords2;
    end if;
    gens2 := genords2[1]; ords2 := genords2[2];
    if #gens2 gt 1 then
	Q := gens2[1]; q := ords2[1];
	genords1 := SylowSubgroupReduction(p,genords1,<Q,q>);
	genords2 := <gens2[[2..#gens2]],ords2[[2..#gens2]]>;
	return SylowSubgroupReduction(p,genords1,genords2);
    end if;
    if ords2[1] eq 1 then
	return genords1;
    end if;
    J := Universe(gens2);
    Z := J!0;
    r1 := #gens1; 
    gens := gens1 cat gens2;
    ords := ords1 cat ords2;
    p_gens1 := [ (ords[i] div p)*gens[i] : i in [1..r1] ];
    Q := gens2[1];
    q := ords2[1];
    n2 := Valuation(q,p); 
    assert q*Q eq Z and (q div p)*Q ne Z;
    if GetVerbose("EndomorphismRing") ge 2 then
	print "Sylow reduction prime:", p;
	print "Sylow reduction in group with abelian invariants:", ords1;
	print "                     ...merging element of order:", ords2[1];
	print "Group p-rank:", r1;
	print "Valuation of new element:", n2;
    end if;
    kj := 0;
    aj := Vector([ 0 : i in [1..r1] ] cat [1]);
    vals := [ Valuation(ords[i],p) : i in [1..r1+1] ];
    while kj lt n2 do
	kj +:= 1;
	R1 := p^(n2-kj) * &+[ J | aj[i] * gens[i] : i in [1..r1+1] | aj[i] ne 0 ];
	if GetVerbose("EndomorphismRing") ge 2 then
	    printf "k = %o <= %o\n", kj, n2;
	    print "  Order valuations:", vals;
	    print "  Relations vector:", aj;
	end if;
	if R1 eq Z then
	    continue;
	end if;
	assert p*R1 eq Z;
	Ij := [ i : i in [1..r1] | vals[i]+kj gt n2 ];
	bj := pTorsionRelation(p,p_gens1[Ij],R1);
	if bj[#Ij+1] eq 0 then
	    assert bj eq 0;
	    aj *:= p;
	    continue;
	else
	    assert bj[#Ij+1] eq 1;
	    for i in [1..#Ij] do
		aj[Ij[i]] +:= p^(vals[Ij[i]]-n2+kj-1)*bj[i];
	    end for;
	end if;
	if GetVerbose("EndomorphismRing") ge 2 then
	    printf "  Found new relation for %o^%o*Q: %o\n", p, kj, Eltseq(aj);
	    assert p^(n2-kj) * &+[ J | aj[i] * gens[i] : i in [1..r1+1] | aj[i] ne 0 ] eq Z;
	end if;
    end while;
    if &and[ aj[i] eq 0 : i in [1..r1] ] then
	vprint EndomorphismRing, 2 : "  No group relations with new element.";
	i := Index(vals,n2);
	gens0 := Insert(gens1,i,gens2[1]);
	ords0 := Insert(ords1,i,ords2[1]);
    else
	G := AbelianGroup(ords);
	Q, m := quo< G | G!Eltseq(aj) >;
	B := [ Eltseq(Q.i@@m) : i in [1..Ngens(Q)] ]; 
	gens0 := [ &+[ c[i] * gens1[i] : i in [1..r1] ] + c[r1+1]*gens2[1] : c in B ];
	ords0 := [ Order(Q.i) : i in [1..Ngens(Q)] ];
	assert ords0 eq AbelianInvariants(Q);
    end if;
    vprint EndomorphismRing, 2 : "  Found abelian invariants after Sylow reduction", ords0;
    assert #gens0 le 2*Dimension(J);
    return <gens0, ords0>;
end function;

function SylowSubgroupKnownGroupOrder(J,p,group_order)
    n := Valuation(group_order,p);
    R := p^n;
    N := group_order div R; 
    G := AbelianGroup([]);
    gens := [ J | ];
    ords := [ IntegerRing() | ];
    genords := <gens,ords>;
    repeat
	P := N * Random(J);
	q := SylowOrder(P,p,n);
	if q ne 1 then
	    genords := SylowSubgroupReduction(p,genords,<[P],[q]>);
	end if;
    until &*genords[2] eq R;
    gens := genords[1];
    ords := genords[2];
    G := AbelianGroup(ords);
    return G, map< G->J | x :-> &+[ c[i]*gens[i] : i in [1..#gens] ] where c := Eltseq(x) >;
end function;

intrinsic TorsionSubgroup(J::JacHyp[FldFin],m::RngIntElt) -> GrpAb, Map
    {The m-torsion subgroup of J.}
    FF := BaseField(J);
    bool, p, r := IsPrimePower(m);
    if bool then
	G, psi := SylowSubgroupKnownGroupOrder(J,p,#J);
    else
	G, psi := AbelianGroup(J);
    end if;
    ords := [ GCD(Order(G.i),m) : i in [1..Ngens(G)] ];
    pnts := [ psi((Order(G.i) div ords[i])*G.i) : i in [1..Ngens(G)] ];
    A := AbelianGroup(ords);
    phi := map< A->J | x:->&+[ c[i]*pnts[i] : i in [1..#ords] ] where c := Eltseq(x) >;
    return A, phi;
end intrinsic;

