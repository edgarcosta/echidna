//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                       NONFUNDAMENTAL KERNEL GROUPS                       //
//                          David Kohel, 1999-2000                          //
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

/*
DRK (02/2008): Fixed group structure for p = 2, 3
*/

// intrinsics: ClassGroup, FundamentalKernel, // RingClassUnitGroup 

declare verbose QuadraticForms, 1;

import "abelian_groups.m" : GeneratedSubgroup;

forward RingClassMap; 
forward RingClassLocalUnitGroup, RingClass2LocalUnitGroup, RingClass3LocalUnitGroup;
forward RingClassGlobalUnit, CyclotomicUnitMod, SquareRoot3Lift; 
forward RamifiedModlog, SplitModlog, InertModlog;
forward RamifiedMod2log, SplitMod2log, InertMod2log;
forward CyclotomicMod2log, CyclotomicMod3log;
forward Modquo, Modlog;

IntNorm := func< x | Integers()!Norm(x) >;
IntTrace := func< x | Integers()!Trace(x) >;

function FundamentalClassGroup(Q)
    // Overwrite the built-in magma function which is broken (e.g. for D = -151188).
    D := Discriminant(Q); // assert IsFundamental(D);
    O := MaximalOrder(QuadraticField(D));
    G, m := ClassGroup(O : Al := "Relations");
    gens := [ QuadraticForm(m(G.i)) : i in [1..Ngens(G)] ];
    m := map< G->Q | x:-> &*[ Q | gens[i]^c[i] : i in [1..Ngens(G)] ] where c := Eltseq(x) >;
    return G, m;
end function;

intrinsic ClassGroupInvariants(D::RngIntElt) -> SeqEnum
    {The sequence of invariants of the abelian class group of the quadratic order of discriminant D.}
    require not IsSquare(D) and D mod 4 in {0,1} :
	"Argument must be congruent to 0 or 1 mod 4.";
    return AbelianInvariants(ClassGroup(QuadraticForms(D)));
end intrinsic;

intrinsic ClassGroupInvariants(Q::QuadBin) -> SeqEnum
    {The sequence of invariants of the abelian class group of Q.}
    return AbelianInvariants(ClassGroup(Q));
end intrinsic;

intrinsic ClassGroup(D::RngIntElt) -> SeqEnum
    {The abelian class group of the quadratic order of discriminant D.}
    require not IsSquare(D) and D mod 4 in {0,1} :
	"Argument must be congruent to 0 or 1 mod 4.";
    return ClassGroup(QuadraticForms(D));
end intrinsic;

intrinsic ClassGroup(Q::QuadBin : 
    FactorBasisBound := 0.1, ProofBound := 6.0, ExtraRelations := 1) -> GrpAb, Map
    {The abelian class group of Q, followed by the isomorphism to Q.}
    require ISA(Type(FactorBasisBound), FldReElt) :
        "FactorBasisBound must be a FldReElt";
    require ISA(Type(ProofBound), FldReElt) :
        "ProofBound must be a FldReElt";
    require ISA(Type(ExtraRelations), RngIntElt) :
        "ExtraRelations must be a RngIntElt";
    
    pi := FundamentalQuotient(Q);
    G, g := FundamentalClassGroup(Codomain(pi));
    H, h := FundamentalKernel(Q);
    m := #H;
    n := #G;
    t := GCD(m,n);
    if t eq 1 then
	E,_,_,p1,p2 := DirectSum(H,G);
	gens := [ h(p1(E.i))*(g(p2(m*E.i))@@pi)^m : i in [1..Ngens(E)] ];
        return E, hom< E->Q | x :-> &*[ Q | gens[i]^c[i] : i in [1..Ngens(E)] ] where c is Eltseq(x) >;
    end if;
    m0 := t;
    m1 := m div t;
    n0 := t;
    n1 := n div t;
    t := GCD(m0,m1);
    while t ne 1 do
        m0 *:= t;
        m1 div:= t;
        t := GCD(m0,m1);
    end while;
    t := GCD(n0,n1);
    while t ne 1 do
        n0 *:= t;
        n1 div:= t;
        t := GCD(n0,n1);
    end while;
    // First compute the coprime parts.
    G1 := sub< G | [ n0*G.i : i in [1..Ngens(G)] ] >;
    ggens1 := [ (g(G!G1.j)@@pi)^((n*m) div n1) : j in [1..Ngens(G1)] ];
    g1 := hom< G1->Q | x :-> &*[ Q | ggens1[j]^c[j] : j in [1..Ngens(G1)] ] where c := Eltseq(x) >;
    H1 := sub< H | [ m0*H.i : i in [1..Ngens(H)] ] >;
    hgens1 := [ h(H!H1.j) : j in [1..Ngens(H1)] ];
    h1 := hom< H1->Q | x :-> &*[ Q | hgens1[j]^c[j] : j in [1..Ngens(H1)] ] where c := Eltseq(x) >;
    E1,_,_,p1,p2 := DirectSum(H1,G1);
    egens1 := [ h1(p1(E1.i))*g1(p2(E1.i)) : i in [1..Ngens(E1)] ];
    e1 := hom< E1->Q | x :-> &*[ Q | egens1[i]^c[i] : i in [1..Ngens(E1)] ] where c is Eltseq(x) >;
    // Now compute the possibly nontrivial group extension.
    G2 := sub< G | [ n1*G.i : i in [1..Ngens(G)] ] >;
    ggens2 := [ Q | (g(G!G2.j)@@pi)^m1 : j in [1..Ngens(G2)] ];
    H2 := sub< H | [ m1*H.i : i in [1..Ngens(H)] ] >;
    hgens2 := [ Q | h(H!H2.j) : j in [1..Ngens(H2)] ];
    E2, e2 := GeneratedSubgroup(ggens2 cat hgens2,m0*n0);
    // And put them together.
    E,_,_,p1,p2 := DirectSum(E1,E2);
    egens := [ e1(p1(E.i))*e2(p2(E.i)) : i in [1..Ngens(E)] ];
    e := hom< E->Q | x :-> &*[ Q | egens[i]^c[i] : i in [1..Ngens(E)] ]
        where c := Eltseq(x) >;
    return E, e;
end intrinsic;

intrinsic PicardGroup(R::RngQuad :
    Al := "Relations",
    FactorBasisBound := 0.1,
    ProofBound := 6.0,
    ExtraRelations := 1) -> GrpAb, Map
    {The class group G of R and a map from G to the ideal group of R.}
    
    require ISA(Type(FactorBasisBound), FldReElt) :
        "FactorBasisBound must be a FldReElt";
    require ISA(Type(ProofBound), FldReElt) :
        "ProofBound must be a FldReElt";
    require ISA(Type(ExtraRelations), RngIntElt) :
        "ExtraRelations must be a RngIntElt";
    G, m := ClassGroup(QuadraticForms(Discriminant(R)) :
	Al := Al,
	FactorBasisBound := FactorBasisBound,
        ProofBound := ProofBound,
        ExtraRelations := ExtraRelations); 
    return G, map< G->PowerIdeal(R) | g :-> Ideal(m(g))>;
end intrinsic;

function MultiplicativeOrder(x,Q,S)
    ZZ := IntegerRing();
    R := Parent(x);
    y := x;
    i := 1;
    m := Generator(Q meet ZZ);
    while true do
	if y in S then
	    return i;
	end if;
	y := R![ ZZ!c mod m : c in Eltseq((x*y) mod Q) ];
	i +:= 1; 
    end while;
end function;

intrinsic FundamentalKernel(Q::QuadBin) -> GrpAb, Map
    {The kernel of the fundamental quotient of Q.}
    D := Discriminant(Q); 
    m := Conductor(Q);
    P := PolynomialRing(Integers());
    DK := D div m^2;
    t := DK mod 2;
    n := (t - DK) div 4;
    R := MaximalOrder(NumberField(P.1^2-t*P.1 + n));
    G, f := RingClassUnitGroup(R,m);
    h := RingClassMap(R,m);
    gens := [ Q | h(f(G.i)) : i in [1..Ngens(G)] ];
    if GetVerbose("QuadraticForms") ge 1 then
	print "G_ORDS:", [ MultiplicativeOrder(f(G.i),ideal< R | m >,
	    { i : i in [1..m] | GCD(i,m) eq 1 }) : i in [1..Ngens(G)] ];
	print "Q_ORDS:", [ Order(s) : s in gens ];
    end if;
    u := hom< G->Q | x :-> &*[ Q | gens[i]^c[i] : i in [1..Ngens(G)] ]  where c := Eltseq(x) >;
    return G, u;
end intrinsic;

intrinsic RingClassUnitGroup(R::RngOrd,m::RngIntElt) -> GrpAb, Map
    {The unit group (R/mR)^*/R^*(ZZ/mZZ)^* mapping to the kernel of the
    ideal class group of the quadratic maximal order R from the ideal
    class group of the order of conductor m.}
    grps := [ ];
    maps := [ ];
    elts := [ ];
    u := RingClassGlobalUnit(R);
    fact := Factorization(m);
    for p in fact do
        if p[1] eq 2 then
	    Gp, fp, xp := RingClass2LocalUnitGroup(R,p[2],u);
        elif p[1] eq 3 then
	    Gp, fp, xp := RingClass3LocalUnitGroup(R,p[2],u);
        else
	    Gp, fp, xp := RingClassLocalUnitGroup(R,p[1]^p[2],u);
        end if;
	if GetVerbose("QuadraticForms") ge 1 then 
	    printf "fp(xp)*u^-1 = %o in ZZ/%oZZ^*\n", [ Integers()!c mod p[1]^p[2] : c in Eltseq(fp(xp)*u^-1) ], p[1]^p[2];
	end if;
	maps cat:= [fp]; 
        Append(~grps,Gp); 
        Append(~elts,Eltseq(xp)); 
    end for;
    if GetVerbose("QuadraticForms") ge 1 then 
	print "GRP_INVS:"; [ [ Order(G.i) : i in [1..Ngens(G)] ] : G in grps ];
	print "GRP_ELTS:"; elts;
	print "GRP_ORDS:"; [ Order(grps[i]!elts[i]) : i in [1..#grps] ];
    end if;
    exps := &cat[ [ Order(Gp.i) : i in [1..Ngens(Gp)] ] : Gp in grps ]; 
    G := AbelianGroup(exps);
    Q := ideal< R | m >;
    gens := [ R | ];
    one := [ R | 1 : i in [1..#fact] ];
    mods := [ ideal< R | p[1]^p[2] > : p in fact ]; 
    for j in [1..#fact] do
	Gp := grps[j];
        fp := maps[j];
        for i in [1..Ngens(Gp)] do
	    crtgen := one; 
            crtgen[j] := fp(Gp.i);
            Append(~gens,CRT(crtgen,mods));
        end for;
    end for;
    u0 := G!&cat(elts);
    H, pi := quo< G | u0 >;
    hgens := [ &*[ Modexp(gens[k],c[k],m) : k in [1..Ngens(G)] ] mod Q where c := Eltseq(H.j@@pi) : j in [1..Ngens(H)] ];
    if GetVerbose("QuadraticForms") ge 1 then 
	print "G:", [ Order(G.i) : i in [1..Ngens(G)] ];
	print "u:", Eltseq(u0);
	print "c:"; Matrix([ Eltseq(H.j@@pi) : j in [1..Ngens(H)] ]); 
	print "H_INVS:"; [ Order(H.i) : i in [1..Ngens(H)] ];
	print "H_ORDS:"; [ MultiplicativeOrder(hgens[i],Q,{ i * u^j : i in [1..m], j in [0..5] | GCD(i,m) eq 1 }) : i in [1..Ngens(H)] ];
    end if;
    f := map< H->R | x:-> &*[ Modexp(hgens[j],c[j],m) : j in [1..Ngens(H)] ] mod Q where c := Eltseq(x) >;
    return H, f;
end intrinsic;

function RingClassMap(R,m)
    // The map to the kernel of the class group of conductor 
    // m from R, inducing a homormophism from (R/mR)^*.}
    Q := QuadraticForms(m^2*Discriminant(R));
    w := Basis(R)[2];
    t := IntTrace(w);
    n := IntNorm(w);
    return map< R -> Q | x :-> Reduction(Q![ 
    X[1,1]^2 + t*X[1,1]*X[1,2] + n*X[1,2]^2, 
        t*X[1,1]*X[2,2] + 2*n*X[1,2]*X[2,2], n*X[2,2]^2 
        where X := EchelonForm( RMatrixSpace(Integers(),3,2) ! 
        &cat[ Eltseq(x), [ m, 0 ], [ 0, m ] ] ) ]) >;
end function;

function RingClassLocalUnitGroup(R,q,e)
    // Construct the p-part of the unit group of (R/q)^* mod <-1>.
    _, p, r := IsPrimePower(q); assert p ge 5;
    D := Discriminant(R);
    Q := ideal< R | q >;
    case KroneckerSymbol(D,p):
    when 0:
        P := Factorization(ideal<R|p>)[1][1];
	/*
	if p eq 3 and r gt 1 and D mod 9 eq 6 then
            G := AbelianGroup([p,p^(r-1)]);
            U :=  [  CyclotomicUnitMod(3,P,r), 1 + 3*UniformizingElement(P) ];
            f := map< G->R | x:-> &*[ Modexp(U[i],Eltseq(x)[i],p^r) : i in [1,2] ] mod Q >; 
            x := CyclotomicMod3log(f,e,P,r);
            return G, f, x;
        else
            G := AbelianGroup([p^r]);
        end if;
        */
	G := AbelianGroup([p^r]);
        u := 1 + UniformizingElement(P);
        f := map< G->R | x:-> Modexp(u,Eltseq(x)[1],p^r) >; 
        x := RamifiedModlog(f,e,P,r);
	if GetVerbose("QuadraticForms") ge 1 then 
	    unit := (f(-x)*e) mod Q;
	    print "f(-x)*e) mod Q:", unit;
	    assert Eltseq(unit)[2] eq 0;
	end if;
        return G, f, x;
    when 1:
        F := Factorization(ideal<R|p>);
        P1 := F[1,1]; P2 := F[2,1]; 
        u := CyclotomicUnitMod(p-1,P1,r);
        U := [ CRT([R|u,1],[P1^r,P2^r]) ];
        if r eq 1 then
            u1 := CRT([R|u,1],[P1^r,P2^r]);
            G := AbelianGroup([p-1]);
            f := map< G->R | x:-> Modexp(u1,Eltseq(x)[1],p^r) >; 
        else
            U := [ CRT([R|u,1],[P1^r,P2^r]), CRT([R!1+p,1],[P1^r,P2^r]) ];  
            G := AbelianGroup([p-1,p^(r-1)]);
            f := map< G->R | x:-> &*[ Modexp(U[i],Eltseq(x)[i],p^r) : i in [1,2] ] mod Q >; 
        end if;
        x := SplitModlog(f,e,P1,P2,r);
	if GetVerbose("QuadraticForms") ge 1 then 
	    print "f(-x)*e) mod P1^r:", (f(-x)*e) mod P1^r;
	    print "f(-x)*e) mod P2^r:", (f(-x)*e) mod P2^r;
	    assert Eltseq((f(-x)*e) mod Q)[2] eq 0;
	end if;
        return G, f, x;
    else // -1:
        P := ideal< R | p >;
        U := [ CyclotomicUnitMod(p^2-1,P,r) ];
        if r gt 1 then
            G := AbelianGroup([p+1,p^(r-1)]);
            U cat:= [ 1 + p*R![0,1] ];
        else 
            G := AbelianGroup([p+1]);
        end if;
        f := map< G->R | x:-> &*[ Modexp(U[i],Eltseq(x)[i],p^r) 
            : i in [1..Ngens(G)] ] mod Q >; 
        x := InertModlog(f,e,p,r);
	if GetVerbose("QuadraticForms") ge 1 then 
	    unit := (f(-x)*e) mod Q;
	    print "f(-x)*e mod Q =", unit;
	    assert Eltseq(unit)[2] eq 0;
	end if;
        return G, f, x;
    end case;
end function;

function RingClass2LocalUnitGroup(R,r,e)
    /*
    INPUT:

       R: A maximal order R in a quadratic field
       r: a positive integer
       e: a global unit generating R^* / <-1>

    OUTPUT: The p-part of the unit group of

        (R/(p^r))^* mod <-1,e>.

    where p = 2.

    The group structure depends only on the square class of DK.

    0) if DK == 0 mod 4, then 

        a. DK == 0 mod 8:

           R_p^* = \mu_2 x (1+4)^{Z_p} x (1+\pi)^{Z_p} 
    
        b. DK == 4 mod 8:

           1) DK == 12 mod 32 (== -20 mod 32):

              R_p^* = \mu_2 x (1+4)^{Z_p} x (1+\pi)^{Z_p}
    
           2) DK == 28 mod 32 (== -4 mod 32):

              R_p^* = \mu_4 x 1+p\piR_p = \mu_4 x (1+4)^{Z_p} x (1+p\pi)^{Z_p}

       N.B. R_p^* = 1+\piR_p in all cases.

    +) if DK == 1 mod 8 (== -7 mod 8), then

       R_p^* = (\mu_2 x 1+pZ_p)^2 = (<-1> x (1+p)^{Z_p})^2

    -) if DK == 5 mod 8 (== -3 mod 8), then
        
       R_p^* = \mu_3 x (1+ p R_p)) = <-1, \zeta_3> x (1+4)^{Z_p} x (1+up)^{Z_p}

    Below we are interested in generators for (R/(p^r))^* / Z/(p^r)^* <e>.
    */
    p := 2;
    D := Discriminant(R);
    Q := ideal< R | 2^r >;
    case KroneckerSymbol(D,p):
    when 0:
        P := Factorization(ideal<R|p>)[1][1];
	if r gt 1 and D mod 32 eq 12 then
	    G := AbelianGroup([p,p^(r-1)]);
	    s := R!NumberField(R).1;
	    s := SquareRoot3Lift(s,p,r);
	    u := 2 + s;
            U :=  [ s, u ];
	    f := map< G->R | x :-> &*[ Modexp(U[i],Eltseq(x)[i],p^r) : i in [1,2] ] mod Q >;
	    x := CyclotomicMod2log(f,e,r);
        elif r gt 1 and D mod 32 eq 28 then
            G := AbelianGroup([p,p^(r-1)]);
            u := 1 + 2*UniformizingElement(P);
            i := CyclotomicUnitMod(4,P,r);
            U :=  [ i, u ];
            f := map< G->R | x :-> &*[ Modexp(U[i],Eltseq(x)[i],p^r) : i in [1,2] ] mod Q >; 
            x := CyclotomicMod2log(f,e,r);
	else // D mod 8 eq 0 or r small
	    G := AbelianGroup([p^r]);
	    u := 1 + UniformizingElement(P);
	    f := hom< G->R | x :-> Modexp(u,Eltseq(x)[1],p^r) >;
	    x := RamifiedMod2log(f,e,r);
        end if;
	if GetVerbose("QuadraticForms") ge 1 then 
	    unit := (f(-x)*e) mod Q;
	    print "f(-x)*e) mod Q:", unit;
	    assert Eltseq(unit)[2] eq 0;
	end if;
	return G, f, x;
    when 1:
        if r eq 1 then
            G := AbelianGroup([]);
            f := map< G->R | x:-> R!1 >; 
            x := G!0;
        elif r eq 2 then
            fact := Factorization(ideal<R|p>);
            P1 := fact[1,1]; P2 := fact[2,1];
            u := CRT([R|-1,1],[P1^2,P2^2]);
            G := AbelianGroup([2]);
            f := map< G->R | x :-> Modexp(u,Eltseq(x)[1],p^2) mod Q >;
            x := SplitMod2log(f,e,P1,P2,r);
        else
            fact := Factorization(ideal<R|p>);
            P1 := fact[1,1]; P2 := fact[2,1];
            u1 := CRT([R|-1,1],[P1^r,P2^r]);
            u2 := CRT([R|1+4,1],[P1^r,P2^r]);
            G := AbelianGroup([2,2^(r-2)]);
            f := map< G->R | x :-> (Modexp(u1,c[1],p^r) mod Q) *
                (Modexp(u2,c[2],p^r) mod Q) where c := Eltseq(x) >;
            x := SplitMod2log(f,e,P1,P2,r);
        end if;
	if GetVerbose("QuadraticForms") ge 1 then 
	    unit := (f(-x)*e) mod Q;
	    print "f(-x)*e) mod Q:", unit;
	    assert Eltseq(unit)[2] eq 0;
	end if;
        return G, f, x;
    else // -1:
        P := ideal< R | p >;
        w := CyclotomicUnitMod(3,P,r);
        if r eq 1 then
            G := AbelianGroup([3]);
            U := [ w ];
        elif r eq 2 then
            G := AbelianGroup([3,2]);
            U := [ w, 1 + 2*w ];
        else
            G := AbelianGroup([3,2,2^(r-2)]);
            U := [ w, 1 + 2*w, 1 + 4*w ];
        end if;
        f := map< G->R | x:-> &*[ Modexp(U[i],c[i],p^r) :
            i in [1..Ngens(G)] ] mod Q where c := Eltseq(x) >;
        x := InertMod2log(f,e,r);
	if GetVerbose("QuadraticForms") ge 1 then 
	    unit := (f(-x)*e) mod Q;
	    print "f(-x)*e) mod Q:", unit;
	    assert Eltseq(unit)[2] eq 0;
	end if;
        return G, f, x;
    end case;
end function;

function RingClass3LocalUnitGroup(R,r,e)
    /*
    INPUT:

       R: A maximal order R in a quadratic field
       r: a positive integer
       e: a global unit generating R^* / <-1>

    OUTPUT: The p-part of the unit group of

        (R/(p^r))^* mod <-1,e>.

    where p = 3.

    The group structure depends only on the square class of DK.

    0) if DK == 0 mod 3, then

        a. DK == +3 (R^*)^2 (iff DK mod 9 = 3):

            R_p^* = \mu_2 x (1+\piR_p) = <-1> x (1+\pi)^{Z_p} x (1+p)^{Z_p}
    
        b. DK == -3 (R^*)^2 (iff DK mod 9 = 6):

            R_p^* = \mu_6 x 1+pR_p = \mu_6 x (1+p)^{Z_p} x (1+p\pi)^{Z_p}
    
    +) if DK == 1 mod 3, then

       R_p^* = (\mu_2 x 1+pZ_p)^2 = (<-1> x (1+p)^{Z_p})^2

    -) if DK == 2 mod 3, then
        
       R_p^* = \mu_8 x (1+pR_p) = <\zeta_8> x (1+p)^{Z_p} x (1+up)^{Z_p}

    Below we are interested in generators for (R/(p^r))^* / Z/(p^r)^* <e>.
    */
    p := 3;
    D := Discriminant(R);
    Q := ideal< R | p^r >;
    chi := KroneckerSymbol(D,3);
    case chi:
    when 0:
        P := Factorization(ideal<R|p>)[1][1];
        pi := UniformizingElement(P);
        if D mod 9 eq 3 then
            // R = Z_3[sqrt(3)]
            G := AbelianGroup([p^r]);
            u := 1 + UniformizingElement(P);
            f := map< G->R | x:-> Modexp(u,Eltseq(x)[1],p^r) >; 
            x := RamifiedModlog(f,e,P,r);
            return G, f, x;
        else
            // if D == -3 mod 9 then 
            //     R = Z_3[(1+sqrt(-3))/2]
            // and there exists a cyclotomic unit.
	    w := CyclotomicUnitMod(3,P,2*r);
            if r eq 1 then
                G := AbelianGroup([p]);
                f := map< G->R | x :-> Modexp(w,Eltseq(x)[1],p^r) >;
            else
                G := AbelianGroup([p,p^(r-1)]);
                U :=  [ w, 1 + 3*pi ];
                f := map< G->R | x :-> &*[ Modexp(U[i],Eltseq(x)[i],p^r) : i in [1,2] ] mod Q >; 
            end if;
            x := CyclotomicMod3log(f,e,P,r);
            return G, f, x;
        end if;
    when 1:
        F := Factorization(ideal<R|p>);
        P1 := F[1,1]; P2 := F[2,1]; 
        u := CyclotomicUnitMod(p-1,P1,r);
        U := [ CRT([R|u,1],[P1^r,P2^r]) ];
        if r eq 1 then
            u1 := CRT([R|u,1],[P1^r,P2^r]);
            G := AbelianGroup([p-1]);
            f := map< G->R | x:-> Modexp(u1,Eltseq(x)[1],p^r) >; 
        else
            U := [ CRT([R|u,1],[P1^r,P2^r]), CRT([R!1+p,1],[P1^r,P2^r]) ];  
            G := AbelianGroup([p-1,p^(r-1)]);
            f := map< G->R | x:-> &*[ Modexp(U[i],Eltseq(x)[i],p^r) : i in [1,2] ] mod Q >; 
        end if;
        x := SplitModlog(f,e,P1,P2,r);
        return G, f, x;
    when -1:
        P := ideal< R | p >;
        U := [ CyclotomicUnitMod(p^2-1,P,r) ];
        if r gt 1 then
            G := AbelianGroup([p+1,p^(r-1)]);
            U cat:= [ 1 + p*R![0,1] ];
        else 
            G := AbelianGroup([p+1]);
        end if;
        f := map< G->R | x:-> &*[ Modexp(U[i],Eltseq(x)[i],p^r) 
            : i in [1..Ngens(G)] ] mod Q >; 
        x := InertModlog(f,e,p,r);
        return G, f, x;
    end case;
end function;

function RingClassGlobalUnit(R)
    // A generator of the global cyclic group R^*/<-1>.
    D := Discriminant(R);
    if D lt 0 then
        if D in {-3,-4} then
            return R![0,1];      
        end if;
        return R!1;
    else
        U, m := UnitGroup(R);
        return m(U.2);
    end if;
end function;

function SquareRoot3Lift(s,p,r)
    ZZ := IntegerRing();
    R := Parent(s);
    q := p^r; assert p eq 2;
    Q := ideal< R | q >;
    fx := s^2-3;
    vx := Min([ Valuation(ZZ!c,p) : c in Eltseq(fx) ]);
    while vx lt r do
	s -:= (R!(fx/2)*Modinv(s,q)) mod Q;
	fx := s^2-3;
	vx := Min([ Valuation(ZZ!c,2) : c in Eltseq(fx) ]);
    end while;
    return s;
end function;

function CyclotomicUnitMod(t,P,r)
    // A P-adic t-th root of unity, computed modulo P^r.
    R := Order(P);
    if t eq 1 then
        return R!1;
    elif t eq 2 then
	return R!-1;
    end if;
    p := IntNorm(P); // P is split or ramified so p is prime
    if t eq 3 and p eq 3 then
	// We want to construct a 3rd root of unity, with minimal polynomial
        //   x^2 + x + 1 mod 3, 
        // for which it suffices to find an element with trace -1 (== 2 mod 3).  
        // 
        // Note that disc(R) == -3 mod up to squares in (R/p^rR)^* which is
        // characterized by disc(R) mod 9 eq 6, and the norm is determined
        // by the Tr(z0)^2-4*Nr(z0) == 0 mod 3.
        z0 := R![0,1];
        case IntTrace(z0) mod 3:
        when 0:
            z0 +:= 1;
        when 1:
            z0 -:= 1;
        end case;
        if r le 1 then
            return z0;
        end if;   
    elif t eq 4 and p eq 2 then
        // We want to construct a 4th root of unity, with minimal polynomial
        //   x^2 + 1 mod 4, 
        // for which it suffices to find an element with trace 0.
        // 
        // Note that disc(R) == -4 mod 32 up to squares in (R/p^rR)^* which is
        // characterized by disc(R) mod 8 eq 4; the trace is == 0 mod 2 by the
        // condition that Tr(z0)^2-4*Nr(z0) == 28 mod 32, and once Tr(z0) = 0,
        // then Nr(z0) == 1 mod 4.
        R := Order(P); // assert Discriminant(R) mod 16 eq 12;
        z0 := R![0,1];
        z0 -:= (IntTrace(z0)) div 2;
        if r le 2 then
            return z0;
        end if;   
    else
        FF, proj := ResidueClassField(P);
        z0 := (PrimitiveElement(FF)^((#FF - 1) div t))@@proj;
    end if;
    Q := P^r;
    q := p^r;
    while true do;
        a0 := Modexp(z0,t-1,q) mod Q;
        c0 := (a0*z0-1) mod Q;
        if c0 eq 0 then break; end if; 
        z0 +:= -Modquo(c0,t*a0,Q);
    end while;
    return z0;
end function;

function SplitModlog(f,e,P1,P2,r)
    // The discrete log pullback of a unit with respect to then
    // isomorphism f: G -> (R/p^r)^*/(ZZ/p^r)^*, where (p) = P1*P2.
    // Since G is cyclic of order \phi(p^r) = (p-1)*p^(r-1), it 
    // suffices to determine the discrete logarithm n of e1/e2 with 
    // respect to u1/u2 where ei are the images of e mod Pi and
    // the ui are the images of a generator mod Pi.  Then u^n == e
    // modulo (ZZ/p^r)^*.  Note that for r > 1, G is given by two
    // generators, f(G) = <u,1+p>, so we carry out the DL with
    // respect to u mod p and then 1+p.
    G := Domain(f);
    R := Codomain(f);
    F, pi1 := ResidueClassField(P1);
    F, pi2 := ResidueClassField(P2);
    u0 := f(G.1);
    n0 := Log(pi1(u0)/pi2(u0),pi1(e)/pi2(e));
    if r eq 1 then
        return G![n0];
    end if;
    v0 := f([-n0,0]); 
    c1 := Eltseq((v0*e) mod P1^r);
    c2 := Eltseq((v0*e) mod P2^r);
    p := #F;
    ZZ := Integers(); 
    a1 := ZZ!c1[1]*Modinv(ZZ!c2[1],p^r) mod p^r;
    n1 := Modlog(1+p,a1,p^r);
    return G![n0,n1];
end function;

function InertModlog(f,e,p,r)
    // The discrete log pullback of the unit e with respect 
    // to the isomorphism f: G -> (R/P^r)^*/(Z/pZ)^*, with
    // (p) prime.
    
    G := Domain(f);
    u0 := f(G.1);
    F, pi := ResidueClassField(ideal< Codomain(f) | p >);
    n0 := Log(pi(u0),pi(e));
    if r eq 1 then
        return G![n0];
    end if;
    n1 := 0;
    u1 := f(G.2);
    V := RSpace(GF(p),2);
    MatF := MatrixAlgebra(GF(p),2);
    e1 := e*Modinv(Modexp(u0,n0,p^r),p^r);
    ZZ := Integers();
    e1 *:= ZZ!Eltseq(e1)[1];
    for i in [1..r-1] do
        v0 := V![ (ZZ!x) div p^i : x in Eltseq(e1-1) ];
        M := MatF!( [ (ZZ!x) div p^i : x in Eltseq(u1-1) ] cat [ 1, 0 ] );
        v1 := v0*M^-1;  
        m1 := ZZ!v1[1];
        m2 := ZZ!v1[2];
        n1 +:= m1*p^(i-1);
        if i eq r-1 then break i; end if;
        e1 *:= Modinv(Modexp(u1,m1,p^r),p^r);
        e1 *:= Modinv(Modexp(1+p^i,m2,p^r),p^r);
        u1 := Modexp(u1,p,p^r); 
    end for;
    return G![n0,n1];
end function;

function RamifiedModlog(f,e,P,r)
    // The discrete log pullback of the unit e with respect to 
    // the isomorphism f: G -> (R/P^r)^*, with (p) = P^2.

    if Valuation(e-1,P) ge r then
        return Domain(f)!0;
    end if;
    
    ZZ := Integers();
    G := Domain(f);
    
    n1 := 0;
    u1 := f(G.1);
    e1 := (e mod P)*e;
    p := IntNorm(P);
    for i in [1..r] do
        e1 *:= Modinv(ZZ!Eltseq(e1 mod P^(2*i-1))[1],p^i);
        m1 := ZZ!Eltseq(Modquo(e1-1,u1-1,P))[1] mod p;
        n1 +:= m1*p^(i-1);
        if i eq r then break i; end if;
        e1 *:= Modinv(Modexp(u1,m1,p^r),p^r);
        u1 := Modexp(u1,p,p^r);
    end for;
    return G![n1];
end function;

function SplitMod2log(f,e,P1,P2,r)
    // The discrete log pullback of a unit with respect to
    // the isomorphism f: G -> (R/p^r)^*, where (p) = P1*P2.
    
    ZZ := Integers();
    G := Domain(f);
    if r eq 1 then
        return G!0;
    end if;
    R := Codomain(f);
    c1 := Eltseq(e mod P1^r);
    c2 := Eltseq(e mod P2^r);
    assert c1[2] eq 0 and c2[2] eq 0; 
    a1 := (ZZ!c1[1]*Modinv(ZZ!c2[1],2^r)) mod 2^r;
    n1 := 0;
    if a1 mod 4 eq 3 then
        a1 := (-a1 mod 2^r);
        n1 := 1;
    end if;
    if r eq 2 then return G![n1]; end if;
    return G![n1,Modlog(1+4,a1,2^r)];
end function;

function InertMod2log(f,e,r)
    // The discrete log pullback of the unit e with respect
    // to the isomorphism f: G -> (R/2^rR)^*/(Z/2^rZ)^*.
    
    G := Domain(f);
    R := Codomain(f);
    F, pi := ResidueClassField(ideal< R | 2 >);
    u0 := f(G.1);
    n0 := Log(pi(u0),pi(e));
    if r eq 1 then return G![n0]; end if;
    ZZ := Integers();
    u1 := f(G.2);
    e1 := e*Modinv(Modexp(u0,n0,2^r),2^r);
    e1 *:= ZZ!Eltseq(e1)[1];
    t0 := (ZZ!Eltseq(e1)[2] div 2) mod 2;
    n1 := t0 eq 1 select 1 else 0;
    if r eq 2 then
        return G![n0,n1];
    end if;
    n2 := 0;
    u2 := f(G.3);
    for i in [1..r-2] do
        t0 := (ZZ!Eltseq(e1)[2] div 2^(i+1)) mod 2;
	if t0 ne 0 then
            n2 +:= 2^(i-1);
            if i eq r-2 then break i; end if;
            e1 *:= Modinv(u2,2^r);
            e1 *:= Modinv(ZZ!Eltseq(e1)[1],2^r);
        end if;
        u2 := Modexp(u2,2,2^r);
    end for;
    return G![n0,n1,n2];
end function;

function RamifiedMod2log(f,e,r)
    // The discrete log pullback of the unit e with respect to 
    // the isomorphism f: G -> (R/P^r)^*/(Z/p^rZ)^*, with (p) = P^2.
    
    ZZ := Integers();
    G := Domain(f);
    n1 := ZZ!Eltseq(e)[2] mod 2;
    if r eq 1 then return G![n1]; end if; 
    u1 := f(G.1);
    e1 := Modexp(e*Modinv(Modexp(u1,n1,2^r),2^r),1,2^r);
    for i in [2..r] do
        u1 := Modexp(u1,2,2^r);
        m1 := ZZ!Eltseq(e1)[2] mod 2^i;
        n1 +:= m1;
        e1 *:= Modinv(Modexp(u1,m1 div 2^(i-1),2^r),2^r);
    end for;
    return G![n1];
end function;

function CyclotomicMod2log(f,e,r)
    // The discrete log pullback of the unit e with respect 
    // to the isomorphism f: G -> (R/2^r)^*, with (2) = P^2, 
    // in a ring with 4th roots of unity.
    
    ZZ := Integers();
    p := 2;
    G := Domain(f);
    if e eq 1 then
        return G!0;
    end if;
    u0 := f(G.1);
    n0 := ZZ!Eltseq(e)[2] mod 2;
    e1 := e*Modexp(u0,n0,2^r);
    n1 := 0;
    u1 := f(G.2);
    for i in [2..r] do
        m1 := ZZ!Eltseq(e1)[2] mod 2^i;
        n1 +:= m1;
        e1 *:= Modexp(u1,m1 div 2^(i-1),2^r);
        if i eq r then break i; end if;
        u1 := Modexp(u1,2,2^r);
    end for;
    return G![n0,n1];
end function;

function CyclotomicMod3log(f,e,P,r)
    // The discrete log pullback of the unit e with respect 
    // to the isomorphism f: G -> (R/3^r)^*, with (3) = P^2, 
    // in a ring with 3rd roots of unity.
    
    ZZ := Integers();
    p := 3;
    G := Domain(f);
    u0 := f(G.1);
    e1 := (e mod P)*e;
    n0 := ZZ!Eltseq(Modquo(e1-1,u0-1,P))[1] mod p;
    if Ngens(G) eq 1 then
        return G![n0];
    end if;
    u1 := f(G.2);
    e1 *:= Modinv(Modexp(u0,n0,p^r),p^r);
    n1 := 0;
    for i in [2..r] do
        e1 *:= Modinv(ZZ!Eltseq(e1 mod P^(2*i-1))[1],p^i);
        m1 := ZZ!Eltseq(Modquo(e1-1,u1-1,P))[1] mod p;
        n1 +:= m1*p^(i-1);
        if i eq r then break i; end if;
        e1 *:= Modinv(Modexp(u1,m1,p^r),p^r);
        u1 := Modexp(u1,p,p^r);
    end for;
    return G![n0,n1];
end function;

function Modquo(x,y,Q)
    if y eq 0 then
        "Error: Argument 2 must not be zero";
        assert false;
    end if;
    if not IsPrime(Q) then
        fact := Factorization(Q);
        if #fact gt 1 then
            ppows := [ fact[i][1]^fact[i][2] : i in [1..#fact] ];
            return CRT( [ Modquo(x,y,Qi) : Qi in ppows ], ppows );
        end if; 
        P := fact[1][1];
    else 
        P := Q;
    end if;
    ZZ := Integers();
    _, p := IsPrimePower(IntNorm(P));
    if x eq 0 then
        return Parent(x)!0;
    end if;
    e1 := Valuation(y,P);
    if e1 eq 0 then
        return x*Modinv(y,Q) mod Q;  
    end if;
    error if e1 gt Valuation(x,P),
        "Error: Valuation of argument 2 must not exceed that of argument 1";
    z := x*(IntTrace(y)-y);
    n := IntNorm(y);
    return Parent(x)!
        [ Modinv(n div p^e1,p)*(ZZ!a div p^e1) : a in Eltseq(z) ] mod Q;
end function;

function Modlog(b,a,m)
    // The modular logarithm n of a = b^n mod m, or -1 
    // if no n exists.  Modulus m must be a prime power.
    
    yes, p, e := IsPrimePower(m);   
    error if not yes, "Error: Argument 3 must be a prime power";
    error if not b mod p ne 0, 
        "Error: Argument 1 must be coprime to argument 3";
    error if not a mod p ne 0, 
        "Error: Argument 2 must be coprime to argument 3";
    if p eq 2 then
        if e eq 1 then
            return 0;
        elif e eq 2 then
            if a mod 4 eq 1 then
                return 0;
            elif (a mod 4) eq (b mod 4) then
                return 1; 
            else
                return -1; 
            end if;
        elif (a mod 8 ne 1) and 
            ((a*Modinv(b,8) mod 8) mod m) ne 1 then
            return -1; 
        end if;
    end if;
    a0 := GF(p)!a;
    b0 := GF(p)!b;
    n0 := Log(b0,a0);
    if n0 eq -1 then 
        return -1;
    end if;
    a1 := Modexp(a,p-1,p^e);
    b1 := Modexp(b,p-1,p^e);
    if b1 eq 1 then
        if a1 eq 1 then
            return n0;
        end if;
        return -1;
    end if;
    r := 1;
    d := 0;
    n1 := 0; 
    while r+d lt e do
        br := Modexp(b1,p^(r-1),p^(r+d+1));
        cr := a1*Modexp(b1,-n1,p^(r+d+1)) mod p^(r+d+1);
        sr := (br-1) div p^(r+d);         
        tr := (cr-1) div p^(r+d);         
        while sr eq 0 do
            if tr eq 0 then
                d +:= 1; 
                br := Modexp(b1,p^(r-1),p^(r+d+1));
                cr := a1*Modexp(b1,-n1,p^(r+d+1)) mod p^(r+d+1);
                sr := (br-1) div p^(r+d);         
                tr := (cr-1) div p^(r+d);         
            else 
                return -1; 
            end if;
        end while;
        nr := tr*Modinv(sr,p) mod p;
        n1 +:= p^(r-1)*nr;
        r +:= 1;
    end while;
    return CRT([n0,n1],[p-1,p^(e-2+(p mod 2))]);
end function;

