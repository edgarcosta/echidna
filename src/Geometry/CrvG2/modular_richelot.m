////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           David Kohel                              //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare verbose Richelot, 2;

////////////////////////////////////////////////////////////////////////

/*
intrinsic Evaluate(f::FldFunRatMElt,x::[RngElt]) -> RngElt
    {}
    num := Evaluate(Numerator(f),x);
    den := Evaluate(Denominator(f),x);
    assert den ne 0;
    return num/den;
end intrinsic;
*/

intrinsic HyperellipticCurveFromRosenhainInvariants(tt::[FldElt]) -> CrvHyp
    {The hyperelliptic curve y^2 = x(x-1)(x-t0)(x-t1)(x-t2) from
    the sequence [t0,t1,t2].}
    require 0 notin tt and 1 notin tt and #tt eq 3 :
	"Argument must consist of three elements distinct from 0, 1.";
    require &and[ tt[i] ne tt[j] : i, j in [1..3] | i lt j ] : 
	"Argument must consist of three distinct elements.";
    x := PolynomialRing(Universe(tt)).1;
    return HyperellipticCurve(x*(x-1)*&*[ x-t : t in tt ]);
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic RichelotPolynomials(GG::[RngElt]) -> SeqEnum
    {Given a sequence of three polynomials (of degree 2), determining
    a genus 2 curve with (Z/2Z)^2-torsion subgroup, returns the
    sequence of three polynomials determining the Richelot curve with
    (2,2)-isogenous Jacobian.}
    require #GG eq 3 :
	"Argument must be a sequence of three polynomials."; 
    G1,G2,G3 := Explode(GG);
    if Type(G1) eq RngUPolElt then
	G1p := Derivative(G1); 
	G2p := Derivative(G2);
	G3p := Derivative(G3);
	CC := [ Eltseq(G) : G in GG ];
    elif Type(G1) eq RngMPolElt then
	G1p := Derivative(G1,1); 
	G2p := Derivative(G2,1);
	G3p := Derivative(G3,1);
	CC := [ Eltseq(UnivariatePolynomial(G)) : G in GG ];
    else
	require false : 
	    "Argument must be a sequence of three polynomials."; 
    end if;
    H1 := G2p*G3 - G2*G3p;
    H2 := G3p*G1 - G3*G1p;
    H3 := G1p*G2 - G1*G2p;
    for i in [1..3] do
	while #CC[i] lt 3 do CC[i] cat:= [0]; end while; 
    end for;
    DD := Determinant(Matrix(CC));
    return [H1, H2, H3], DD;
end intrinsic;

intrinsic ModularRichelotPolynomials(tt::[RngElt]) -> SeqEnum
    {}
    require #tt eq 3 :
	"Argument must be a sequence of three ring elements.";
    P := PolynomialRing(Universe(tt)); x := P.1;
    t0, t1, t2 := Explode(tt);
    G0 := x*(x-t0);
    G1 := (x-1)*(x-t1);
    G2 := (x-t2);
    return RichelotPolynomials([G0,G1,G2]);
end intrinsic;

intrinsic RichelotTransformation(ww::SeqEnum[SeqEnum[RngElt]]) -> SeqEnum
    {Given a sequence of sequences [[u0,v0],[u1,v1],[u2,v2]] of 
    roots of polynomials G0, G1, G2, returns the Rosenhain modular 
    invariants obtained by sending (u0,u1,u2) to (0,1,oo).}
    require #ww eq 3 and &and[ #rts le 2 : rts in ww ]
	and &+[ #rts : rts in ww ] ge 5 :
	"Argument must consist of three sequences of length 1 or 2.";
    r0, r1, r2 := Explode(ww);
    case [#r0,#r1,#r2]:
    when [2,2,2]:
	v0 := r0[1]; w0 := r0[2];
	v1 := r1[1]; w1 := r1[2];
	v2 := r2[1]; w2 := r2[2];
	// Send v0 -> 0, v1 -> 1, v2 -> oo
	u0 := ((w0-v0)*(v1-v2))/((w0-v2)*(v1-v0));
	u1 := ((w1-v0)*(v1-v2))/((w1-v2)*(v1-v0));
	u2 := ((w2-v0)*(v1-v2))/((w2-v2)*(v1-v0));
	return [u0,u1,u2];
    when [1,2,2]:
	w0 := r0[1];
	v1 := r1[1]; w1 := r1[2];
	v2 := r2[1]; w2 := r2[2];
	// Send oo -> 0, v1 -> 1, v2 -> oo
	u0 := (v1-v2)/(w0-v2);
	u1 := (v1-v2)/(w1-v2);
	u2 := (v1-v2)/(w2-v2);
	return [u0,u1,u2];
    when [2,1,2]:
	v0 := r0[1]; w0 := r0[2];
	w1 := r1[1];
	v2 := r2[1]; w2 := r2[2];
	// Send v0 -> 0, oo -> 1, v2 -> oo
	u0 := (w0-v0)/(w0-v2);
	u1 := (w1-v0)/(w1-v2);
	u2 := (w2-v0)/(w2-v2);
	return [u0,u1,u2];
    when [2,2,1]:
	v0 := r0[1]; w0 := r0[2];
	v1 := r1[1]; w1 := r1[2];
	w2 := r2[1];
	// Send v0 -> 0, v1 -> 1, oo -> oo
	u0 := (w0-v0)/(v1-v0);
	u1 := (w1-v0)/(v1-v0);
	u2 := (w2-v0)/(v1-v0);
	return [u0,u1,u2];
    end case;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic ModularRichelotRepresentatives(tt::[RngElt]) -> SeqEnum
    {The Rosenhain modular invariants of all 15 Richelot isogenies 
    from the domain curve y^2 = x(x-1)(x-t0)(x-t1)(x-t2), where 
    tt = [t0,t1,t2].}
    require #tt eq 3 and #SequenceToSet(tt) eq 3 : 
	"Argument must be a sequence of three distinct ring elements.";
    require 0 notin tt and 1 notin tt :
	"Argument must not contain 0 or 1."; 
    t0, t1, t2 := Explode(tt);
    P := PolynomialRing(Universe(tt)); x := P.1;
    RichelotTriples := [
	// Six arbitrary permutations:
	[ [0,t0], [1,t1], [t2] ], // BAD @ (t0,t1,t2) [dual]
	[ [0,t1], [1,t2], [t0] ], 
	[ [0,t2], [1,t0], [t1] ], 
	[ [0,t0], [1,t2], [t1] ], // BAD @ t0
	[ [0,t2], [1,t1], [t0] ], // BAD @ t1
	[ [0,t1], [1,t0], [t2] ], // BAD @ t2
	// Three cyclic permutations:
	[ [0,t0], [1], [t1,t2] ], // BAD @ t0
	[ [0,t1], [1], [t2,t0] ], 
	[ [0,t2], [1], [t0,t1] ],
	// Three cyclic permutations:
	[ [1,t0], [0], [t1,t2] ],
	[ [1,t1], [0], [t2,t0] ], // BAD @ t1
	[ [1,t2], [0], [t0,t1] ],
	// Three cyclic permutations:
	[ [t0], [0,1], [t1,t2] ],
	[ [t1], [0,1], [t2,t0] ],
	[ [t2], [0,1], [t0,t1] ] // BAD @ t2 
	];
    return [ RichelotTransformation(rts) : rts in RichelotTriples ];
end intrinsic;

intrinsic ModularRichelotComplementaryRepresentatives(tt::[RngElt])
    -> SeqEnum
    {The Rosenhain modular invariants of all 8 Richelot isogenies
    from the domain curve y^2 = x(x-1)(x-t0)(x-t1)(x-t2), where
    tt = [t0,t1,t2], which determine isogenies with kernel trivially
    meeting that of the (2,2)-isogeny determined by tt.}
    require #tt eq 3 and #SequenceToSet(tt) eq 3 : 
	"Argument must be a sequence of three distinct ring elements.";
    require 0 notin tt and 1 notin tt :
	"Argument must not contain 0 or 1."; 
    t0, t1, t2 := Explode(tt);
    RichelotTriples := [
	// Two good:
	[ [0,t1], [1,t2], [t0] ], 
	[ [0,t2], [1,t0], [t1] ], 
	// Two good:
	[ [0,t1], [1], [t2,t0] ], 
	[ [0,t2], [1], [t0,t1] ],
	// Two good:
	[ [1,t0], [0], [t1,t2] ],
	[ [1,t2], [0], [t0,t1] ],
	// Two good:
	[ [t0], [0,1], [t1,t2] ],
	[ [t1], [0,1], [t2,t0] ]
	];
    return [ RichelotTransformation(rts) : rts in RichelotTriples ];
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic ModularRichelotDual(tt::SeqEnum[RngElt]) -> SeqEnum
    {The dual Rosenhain modular invariants of the Richelot codomain
    curve, or error if they do not split over the base ring.}
    require #tt eq 3 :
	"Argument must consist of triple of Rosenhain invariants.";
    t0, t1, t2 := Explode(tt);
    x := PolynomialRing(Universe(tt)).1;
    GG := [ x*(x-t0), (x-1)*(x-t1), x-t2 ];
    HH := RichelotPolynomials(GG); 
    if GCD(HH) eq 1 then
	rts := [ [ rt[1] : rt in Roots(H) ] : H in HH ];
	require &+[ #rr : rr in rts ] in {5,6} : 
	    "Codomain must have split Rosenhain invariants.";
	return RichelotTransformation(rts); 
    end if;
    if GetVerbose("Richelot") ge 1 then
	print "GG:", GG; "HH:", HH; "GCD:", GCD(HH);
    end if;
    require false : "Invalid input (perhaps a nonsimple Jacobian?)";
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic ExistsModularRichelotTransformation(tt::[RngElt],uu::[RngElt])
    -> SeqEnum, SeqEnum, GrpPermElt
    {}
    // tt = (t0,t1,t2) Rosenhain invariants 
    // uu = (u0,u1,u2) Richelot Rosenhain invariants
    HH := ModularRichelotPolynomials(tt);
    r0 := [ rt[1] : rt in Roots(HH[1]) ];
    r1 := [ rt[1] : rt in Roots(HH[2]) ];
    r2 := [ rt[1] : rt in Roots(HH[3]) ];
    nrts := [#r0,#r1,#r2];
    if 1 in nrts then
	require false : "Argument 1 must be nonsingular.";
    elif 0 in nrts then
	return false;
    else
	assert nrts eq [2,2,2];
    end if;
    t0, t1, t2 := Explode(tt); 
    y0 := r0[1]; y1 := r1[1]; y2 := r2[1]; 
    yy := [y0,y1,y2,2*t2-y0,2*t2-y1,-2*t1/(t0-t1-1)-y2];
    success := false;
    for g in Sym(6) do
	v0, v1, v2, w0, w1, w2 := Explode([ yy[i^g] : i in [1..6] ]);
	// Send v0 -> 0, v1 -> 1, v2 -> oo
	u0 := ((w0-v0)*(v1-v2))/((w0-v2)*(v1-v0));
	u1 := ((w1-v0)*(v1-v2))/((w1-v2)*(v1-v0));
	u2 := ((w2-v0)*(v1-v2))/((w2-v2)*(v1-v0));
	if [u0,u1,u2] eq uu then
	    g0 := g;
	    success := true;
	    break g;
	end if;
    end for;
    if not success then return success, _, _, _; end if;
    F<T0,T1,T2,Y0,Y1,Y2,S0,S1,S2> := PolynomialRing(Integers(),9);
    YY := [Y0,Y1,Y2,2*T2-Y0,2*T2-Y1,-2*T1/(T0-T1-1)-Y2];
    v0, v1, v2, w0, w1, w2 := Explode([ YY[i^g0] : i in [1..6] ]);
    s0 := ((w0-v0)*(v1-v2))/((w0-v2)*(v1-v0));
    s1 := ((w1-v0)*(v1-v2))/((w1-v2)*(v1-v0));
    s2 := ((w2-v0)*(v1-v2))/((w2-v2)*(v1-v0));
    Psi := [Numerator(S0-s0),Numerator(S1-s1),Numerator(S2-s2)];
    return success, Psi, yy[[1..3]], g0;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic HasModularRichelotIsogenyExtension(tt::[RngElt])
    -> BoolElt, SeqEnum
    {True if and only if the codomain curve has split Rosenhain model,
    and if so, returns the sequence of quadratic polynomial roots.} 
    require #tt eq 3 :
	"Argument must be a sequence of three ring elements.";
    HH := ModularRichelotPolynomials(tt);
    rts := [ [ r[1] : r in Roots(H) ] : H in HH ];
    if &+[ #rr : rr in rts ] in {5,6} then
	return true, rts;
    end if;
    return false, _;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic ModularRichelotIsogenyExtensions(tt::[RngElt]) -> SeqEnum
    {The sequence of splitting Rosenhain modular invariants
    of isogegnies from the codomain curve determined by tt.}
    require 0 notin tt and 1 notin tt : 
	"Argument must not contain 0 or 1."; 
    require #tt eq 3 and #SequenceToSet(tt) eq 3 : 
	"Argument must be a sequence of three distinct ring elements.";
    HH := ModularRichelotPolynomials(tt);
    rts := [ [ r[1] : r in Roots(H) ] : H in HH ];
    if &+[ #rr : rr in rts ] notin {5,6} then 
	return [ Parent(tt) | ];
    end if; 
    uu := RichelotTransformation(rts);
    return ModularRichelotRepresentatives(uu);
end intrinsic;

intrinsic ModularRichelotIsogenyGoodExtensions(tt::[RngElt]) -> SeqEnum
    {The sequence of Rosenhain invariants of 'good' isogegnies 
    extending the codomain curve determined by tt, i.e. with 
    composition kernel Z/4ZxZ/4Z.} 

    require #tt eq 3 and #SequenceToSet(tt) eq 3 : 
	"Argument must be a sequence of three distinct ring elements.";
    require 0 notin tt and 1 notin tt :
	"Argument must not contain 0 or 1."; 
    HH := ModularRichelotPolynomials(tt);
    rts := [ [ r[1] : r in Roots(H) ] : H in HH ];
    if &+[ #rr : rr in rts ] notin {5,6} then 
	return [ Parent(tt) | ];
    end if; 
    uu := RichelotTransformation(rts);
    return ModularRichelotComplementaryRepresentatives(uu);
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic RosenhainOrbit(tt::[RngElt]) -> SetEnum
    {The orbit of Rosenhain modular invariants determining the same
    Richelot isogeny, up to isomorphism.  The implied group action
    is of the subgroup G = <(1,4)(2,5)(3,6),(1,2,3)(4,5,6)> of Sym(6),
    under the action on [0,1,oo,t0,t1,t2] (renormalised to the form
    [0,1,oo,u0,u1,u2]).} 

    require #tt eq 3 : "Argument must be a sequence of three elements.";
    FF := Universe(tt);
    P1 := ProjectiveSpace(FF,1);
    t0, t1, t2 := Explode(tt);
    We := [ P1(FF) | [0,1], [1,1], [1,0] ];
    Ws := We cat [ P1 | [t0,1], [t1,1], [t2,1] ];
    G := sub< Sym(6) | [4,2,3,1,5,6], [2,1,3,5,4,6], [2,3,1,5,6,4] >;
    m1 := TranslationOfSimplex(P1,We)^-1;
    Orbit := {@ @};
    for g in G do
	Wg := [ Ws[i^g] : i in [1..6] ];
	m2 := TranslationOfSimplex(P1,Wg[[1..3]]);
	assert [ (P@@m2)@@m1 : P in Wg[[1..3]] ] eq We;
	Include(~Orbit,[ ((P@@m2)@@m1)[1] : P in Wg[[4..6]] ]);
    end for;
    return Orbit;
end intrinsic;

intrinsic RosenhainOrbit(tt::[RngElt],G::GrpPerm) -> SetEnum
    {The orbit of Rosenhain modular invariants tt = [t0,t1,t2], for
    a subgroup of Sym(6), under the action on [0,1,oo,t0,t1,t2].} 
    require #tt eq 3 : "Argument must be a sequence of three elements.";
    require G subset Sym(6) : "Argument 2 must be a subgroup of Sym(6).";
    FF := Universe(tt);
    P1 := ProjectiveSpace(FF,1);
    t0, t1, t2 := Explode(tt);
    We := [ P1(FF) | [0,1], [1,1], [1,0] ];
    Ws := We cat [ P1 | [t0,1], [t1,1], [t2,1] ];
    m1 := TranslationOfSimplex(P1,We)^-1;
    Orbit := {@ @};
    for g in G do
	Wg := [ Ws[i^g] : i in [1..6] ];
	m2 := TranslationOfSimplex(P1,Wg[[1..3]]);
	assert [ (P@@m2)@@m1 : P in Wg[[1..3]] ] eq We;
	Include(~Orbit,[ ((P@@m2)@@m1)[1] : P in Wg[[4..6]] ]);
    end for;
    return Orbit;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic RosenhainImage(tt::[RngElt],g::GrpPermElt) -> SetEnum
    {Given tt = [t0,t1,t2], returns the image Rosenhain modular
    invariant [u0,u1,u2] under the action of g in Sym(6) on
    [0,1,oo,t0,t1,t2] (renormalised to the form [0,1,oo,u0,u1,u2]).} 
    require #tt eq 3 : "Argument must be a sequence of three elements.";
    require g in Sym(6) : "Argument 2 must be an element of Sym(6).";
    FF := Universe(tt);
    if not IsExact(FF) then
	FF := FunctionField(IntegerRing(),3);
	uu := RosenhainImage([FF.i : i in [1..3]],g);  
	return [ Evaluate(ui,tt) : ui in uu ];
    end if;
    P1 := ProjectiveSpace(FF,1);
    t0, t1, t2 := Explode(tt);
    We := [ P1(FF) | [0,1], [1,1], [1,0] ];
    Ws := We cat [ P1 | [t0,1], [t1,1], [t2,1] ];
    m1 := TranslationOfSimplex(P1,We)^-1;
    Wg := [ Ws[i^g] : i in [1..6] ];
    m2 := TranslationOfSimplex(P1,Wg[[1..3]]);
    assert [ (P@@m2)@@m1 : P in Wg[[1..3]] ] eq We;
    return [ ((P@@m2)@@m1)[1] : P in Wg[[4..6]] ];
end intrinsic;

////////////////////////////////////////////////////////////////////////

/*

QQ := FiniteField(3);
QQ := RationalField();
P6<T0,T1,T2,U1,V2,W0> := PolynomialRing(QQ,6);
HH := RichelotPolynomials([T0,T1,T2]);
V0 := 2*T2 - V2;
U2 := 2*T2 - U1; 
W1 := -2*T1/(T0 - T1 - 1) - W0;
TT := [T0,T1,T2];
UU := ModularRichelotTransformation([[U1,U2],[V0,V2],[W0,W1]]);
II := ideal< P6 | 
  [ Evaluate(HH[i],P6.(i+3)) : i in [1..3] ] cat
  [ Numerator(TT[i]-UU[i]) : i in [1..3] ] >;
P3<t0,t1,t2> := PolynomialRing(QQ,3);
JJ := ideal< P3 | 
  [ Evaluate(f,[t0,t1,t2,0,0,0]) :
  f in Basis(EliminationIdeal(II,{T0,T1,T2})) ] >;
for D in [t0,t1,t2,t0-1,t1-1,t2-1,t0-t1,t1-t2] do
  for i in [1..2] do 
    JJ := ColonIdeal(JJ,ideal< P3 | Basis(JJ) cat [D] >);
  end for;
end for;

F<t0,t1,t2> := FunctionField(Integers(),3);
tt := [t0,t1,t2];
HH := RichelotPolynomials(tt);
P3<U,V,W> := PolynomialRing(F,3);
R3<u1,v2,w0> := quo< P3 |
   [ Evaluate(HH[i],P3.i) : i in [1..3] ] >;
u2 := 2*t2 - u1;
w1 := -2*t1/(t0 - t1 - 1) - w0;
v0 := 2*t2 - v2;
ss := RichelotTransformation([u1,u2,v0,v2,w0,w1]);

K<w0> := quo< PF | PF!HH[3] > where PF := PolynomialRing(F);
L<u1> := quo< PK | PK!HH[1] > where PK := PolynomialRing(K);
M<v2> := quo< PL | PL!HH[2] > where PL := PolynomialRing(L);
u1 := M!u1;
u2 := M!(2*t2 - u1);
w0 := M!w0;
w1 := M!(-w0 - 2*t1/(t0 - t1 - 1));
v0 := M!(2*t2-v2);

ss := RichelotTransformation([u1,u2,v0,v2,w0,w1]);
rr := [ ss[i]-tt[i] : i in [1..3] ];
PreimageRing(M)!rr[1]
*/
