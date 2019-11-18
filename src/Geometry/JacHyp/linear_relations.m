//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//         Copyright (C) 2009 David Kohel <kohel@iml.univ-mrs.fr>           //
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

function DLogPrimePower(z,u,l,r)
    // INPUT: elements z and u in a finite field, such that |<z>| = l^r and u in <z>.
    // OUTPUT: a such that u = z^a.
    K := Parent(u);
    p := Characteristic(K);
    s := Order(p,l);
    F := FiniteField(p,s); Embed(F,K);
    error if l gt 10^6,
	"Local function DLogPrimePower was never meant to be used for large (> 10^6) primes";
    zz := [z];
    uu := [u];
    for i in [1..r-1] do
	Append(~zz,zz[i]^l);
	Append(~uu,uu[i]^l);
    end for;
    assert zz[#zz]^l eq 1; 
    assert uu[#uu]^l eq 1;
    zl := F!(zz[#zz]); assert zl ne 1;
    ul := F!(uu[#uu]);
    a0 := Log(zl,ul);
    for i in [1..r-1] do
	// INPUT: assert uu[r-i+1] eq zz[r-i+1]^a0;
	ul := F!(uu[r-i] * zz[r-i]^-a0);
	a0 +:= l^i*Log(zl,ul);
	// OUTPUT: assert uu[r-i] eq zz[r-i]^a0;
    end for;
    assert u eq z^a0;
    return a0;
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic LinearRelation(Q::JacHypPt,S::SeqEnum[JacHypPt],R::RngIntRes :
    WeilPairingMatrix := 0) -> ModTupRngElt
    {Given an N-torsion point Q and a basis of the N-torsion (this could be
    relaxed to a subgroup containing Q), and R = Z/NZ, returns a relation v
    of coefficients expressing Q in terms of S.  If N is a power of the
    characteristic then we assume that the Jacobian is ordinary.}
    J := Parent(Q);
    require J eq Universe(S) :
	"Argument 1 must have the same parent as the universe of argument 2.";
    K := BaseField(J);
    require Type(K) eq FldFin :
	"Arguments must be points on a Jacobian over a finite field.";
    N := Modulus(R);
    require N*Q eq J!0 : 
	"Argument 1 must be an N-torsion element for the modulus N of argument 3.";
    require &and[ N*P eq J!0 : P in S ] :
	"Argument 2 must be a sequence of N-torsion elements for the modulus N of argument 3.";
    bool, p, r := IsPrimePower(N);
    require bool : "Arguments must be of prime power order.";
    // We use the Weil pairing to reduce the problem to the
    // discrete logarithm problem in the base field. 
    q := #K;
    z := PrimitiveElement(K)^((q-1) div N);
    if WeilPairingMatrix ne 0 then
	U := WeilPairingMatrix;
    else
	U := Matrix([ [ R!0 : i in [1..#S] ] : j in [1..#S] ]);
	for i in [1..#S] do
	    P := S[i];
	    U[i,i] := R!0;
	    for j in [i+1..#S] do
		Q := S[j];
		u := WeilPairing(P,Q,N);
		U[i,j] := R!DLogPrimePower(z,u,p,r);
		U[j,i] := -U[i,j];
	    end for;
	end for;
    end if;
    y_exp := [ WeilPairing(Q,P,N) : P in S ];
    y := Vector([ R!DLogPrimePower(z,u,p,r) : u in y_exp ]);
    bool, x := IsConsistent(U,y);
    require bool : "Argument 1 must be a linear combination of elements in argument 2.";
    return x;
end intrinsic;
