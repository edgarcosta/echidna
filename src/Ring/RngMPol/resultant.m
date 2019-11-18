//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Extended Resultants and Effective Hilbert Nullstellensatz               //
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare verbose Nullstellensatz, 1;

function CoefficientsInVariable(F,i)
    X := Parent(F).i; 
    m := Degree(F,i);
    cffs := Coefficients(F);
    mons := Monomials(F);
    cffs_seq := [ P!0 : i in [0..m] ] where P := Parent(F);
    for k in [1..#cffs] do
	c := cffs[k];
	m := mons[k];
	j := Degree(m,i);
	cffs_seq[j+1] +:= c*(m div X^j);
    end for;
    return cffs_seq;
end function;

intrinsic SylvesterMatrix(F::RngMPolElt,G::RngMPolElt,i::RngIntElt)
    -> AlgMatElt
    {}
    P := Parent(F);
    Z := P.i;
    n := Rank(P);
    require Parent(F) eq Parent(G) :
	"Arguments 2 and 3 must be elements of the same ring.";
    require 1 le i and i le n :
	"Argument 3 must be a positive integer no greater " *
	"than the rank of the parent polynomial ring.";
    cffs_F := CoefficientsInVariable(F,i);
    cffs_G := CoefficientsInVariable(G,i);
    if false then
	// Magma has its own Sylvester matrix for univariate polynomials,
	// but it expresses the matrix in the reverted basis x^n,...,x,1,
	// rather than 1,x,...,x^n,[...].
	return SylvesterMatrix(Q!cffs_F,Q!cffs_G)
	    where Q := PolynomialRing(P);
    end if;
    degF := #cffs_F-1; degG := #cffs_G-1;
    M := RMatrixSpace(P,degF+degG,degF+degG)!0;
    for j in [1..degF+1], k in [1..degG+1] do
	if k le degG then
	    M[k,j+k-1] := cffs_F[j];
	end if;
	if j le degF then
	    M[degG+j,j+k-1] := cffs_G[k];
	end if;
    end for;
    return M;
end intrinsic;

intrinsic ExtendedResultant(F::RngMPolElt,G::RngMPolElt,i::RngIntElt)
    -> RngMPolElt
    {Given polynomials f and g, returns the resultant R = Res(f,g,i)
    and polynomials A and B such that R = A*f + B*g.}
    P := Parent(F);
    n := Rank(P);
    require P eq Parent(G) :
	"Arguments 2 and 3 must be elements of the same ring.";
    require 1 le i and i le n :
	"Argument 3 must be a positive integer no greater " *
	"than the rank of the parent polynomial ring.";
    degF := Degree(F,i);
    if degF eq 0 then
	return F, P!1, P!0;
    end if;
    degG := Degree(G,i);
    if degG eq 0 then
	return G, P!0, P!1;
    end if;
    M := SylvesterMatrix(F,G,i);
    // This determinant is just way too expensive: 
    // H := Determinant(M);
    H := Resultant(F,G,i);
    v := RSpace(P,Ncols(M))!([H] cat [0 : i in [1..Ncols(M)-1]]);
    bool, u := IsConsistent(M,v); assert bool;
    Z := P.i;
    A := P!0; B := P!0;
    for j in [1..degG] do
	A +:= u[j]*Z^(j-1);
    end for;
    for k in [1..degF] do
	B +:= u[k+degG]*Z^(k-1);
    end for;
    return H, A, B;
end intrinsic;

intrinsic EffectiveHilbertNullstellensatz(
    S::[RngMPolElt],i::RngIntElt : EliminationOrder := [])
    -> RngMPolElt, RngMPolElt, RngMPolElt
    {}
    Assertions := true;
    P := Universe(S);
    n := Rank(P);
    require n eq 3 :
	"At the moment I only permit rank three polynomial rings --DRK.";
    require #S eq 3 :
	"At the moment I only permit sequences of length three --DRK.";
    require i in [1..3] : 
	"At the moment I only permit in {1,2,3} --DRK.";
    F, G, H := Explode(S);
    if #EliminationOrder eq 0 then
	j, k := Explode([ s : s in [1..n] | s ne i ]);
    else
	j, k := Explode([ s : s in EliminationOrder | s ne i ]);
    end if;
    GCD_FGH := P!1;
    GCD_FG := GCD(F,G);
    if GCD_FG ne 1 then
	F div:= GCD_FG; G div:= GCD_FG;
    end if;
    Res_FG_j, AFG_j, BFG_j := ExtendedResultant(F,G,j);
    if GCD_FG ne 1 then
	GCD_FGH *:= GCD_FG;
    end if;
    vprint Nullstellensatz : "GCD_FG =", GCD_FG;
    vprint Nullstellensatz : "AFG_j =", AFG_j;
    vprint Nullstellensatz : "BFG_j =", BFG_j;
    GCD_GH := GCD(G,H);
    if GCD_GH ne 1 then
	G div:= GCD_GH; H div:= GCD_GH;
    end if;
    Res_GH_j, AGH_j, BGH_j := ExtendedResultant(G,H,j);
    if GCD_GH ne 1 then
	GCD_FGH *:= GCD_GH;
    end if;
    vprint Nullstellensatz : "GCD_GH =", GCD_GH;
    vprint Nullstellensatz : "AGH_j =", AGH_j;
    vprint Nullstellensatz : "BGH_j =", BGH_j;
    if Assertions then
	assert Res_FG_j eq (AFG_j*F + BFG_j*G);
	assert Res_GH_j eq (AGH_j*G + BGH_j*H);
    end if;
    GCD_j := GCD(Res_FG_j,Res_GH_j);
    vprint Nullstellensatz : "GCD_j =", GCD_j;
    if GCD_j ne 1 then
	Res_FG_j div:= GCD_j;
	Res_GH_j div:= GCD_j;
    end if;
    Res_FGH_jk, AFGH_jk, BFGH_jk := ExtendedResultant(Res_FG_j,Res_GH_j,k);
    if GCD_j ne 1 then
	GCD_FGH *:= GCD_j;
    end if;
    vprint Nullstellensatz : "AFGH_jk =", AFGH_jk;
    vprint Nullstellensatz : "BFGH_jk =", BFGH_jk;
    if Assertions then
	assert Res_FGH_jk eq (AFGH_jk*Res_FG_j + BFGH_jk*Res_GH_j);
    end if;
    return Res_FGH_jk,
	[ AFGH_jk*AFG_j, AFGH_jk*BFG_j + BFGH_jk*AGH_j,	BFGH_jk*BGH_j ], GCD_FGH;
end intrinsic;
