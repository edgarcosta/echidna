//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                 ORTHOGONAL DECOMPOSITION OF LATTICES                     //
//                              David Kohel                                 //
//                     Original version April 2000                          //
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

// DRK (June 2009): Fixed orthogonal decomposition when successive minima
// do not generate the lattice by a routine for re-merging components.

/*
// This lattice has only one component, but the successive minima generate a 
// sublattice which decomposes as a (proper) orthogonal sum of three lattices.

L := LatticeWithGram([
    [ 18, -9, 9, 9, 9, -9, 9, 9, 9, 9, -9, -9, 9, 9, 9, -9, -9, -9 ],
    [ -9, 18, 0, 0, -9, 9, -9, -9, -9, -9, 9, 9, -9, 0, -9, 9, 9, 9 ],
    [ 9, 0, 18, 9, 9, -9, 0, 9, 9, 9, -9, -9, 9, 0, 9, -9, -9, -9 ],
    [ 9, 0, 9, 18, 9, 0, 0, 9, 9, 9, 0, 0, 9, 9, 9, 0, 0, 0 ],
    [ 9, -9, 9, 9, 24, -12, 0, 12, 12, 15, -12, -3, 15, 0, 12, -6, -6, -6 ],
    [ -9, 9, -9, 0, -12, 24, -9, -6, -6, -3, 15, 6, -12, 0, -6, 12, 12, 12 ],
    [ 9, -9, 0, 0, 0, -9, 18, 0, 0, 0, -9, -9, 0, 9, 0, -9, -9, -9 ],
    [ 9, -9, 9, 9, 12, -6, 0, 24, 6, 12, -6, -6, 12, 0, 15, -3, -12, -12 ],
    [ 9, -9, 9, 9, 12, -6, 0, 6, 24, 12, -6, -6, 12, 0, 15, -12, -3, -3 ],
    [ 9, -9, 9, 9, 15, -3, 0, 12, 12, 24, -12, -12, 6, 0, 12, -6, -6, -6 ],
    [ -9, 9, -9, 0, -12, 15, -9, -6, -6, -12, 24, 15, -3, 0, -6, 12, 12, 12 ],
    [ -9, 9, -9, 0, -3, 6, -9, -6, -6, -12, 15, 24, -3, 0, -6, 12, 12, 12 ],
    [ 9, -9, 9, 9, 15, -12, 0, 12, 12, 6, -3, -3, 24, 0, 12, -6, -6, -6 ],
    [ 9, 0, 0, 9, 0, 0, 9, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0 ],
    [ 9, -9, 9, 9, 12, -6, 0, 15, 15, 12, -6, -6, 12, 0, 24, -12, -12, -3 ],
    [ -9, 9, -9, 0, -6, 12, -9, -3, -12, -6, 12, 12, -6, 0, -12, 24, 15, 6 ],
    [ -9, 9, -9, 0, -6, 12, -9, -12, -3, -6, 12, 12, -6, 0, -12, 15, 24, 15 ],
    [ -9, 9, -9, 0, -6, 12, -9, -12, -3, -6, 12, 12, -6, 0, -3, 6, 15, 24 ]
]);
assert #OrthogonalDecomposition(L) eq 1;
*/


function MergeLattices(L,sublats,v)
    /*
    Definition. Given a lattice L in V, a vector v in V, the lattice L
    is said to intrinsically meet v if there does not exist u in L such
    that u+v is orthogonal to L.

    Given a sequence of lattices sublats = [L1,...,Ln], and an element v
    with nontrivial image in L/&+subats, determines the subset S of
    lattices which intrinsically meet v.  The return value for this
    function is the sequence consisting of lattices in sublats with do not
    intrinsically meet v together with the sum of the lattices which
    do not intrinsically meet v.
    */
    QQ := RationalField();
    ZZ := IntegerRing();
    merge := [];
    olats := [];
    for N in sublats do
	n := Rank(N);
	V := VectorSpace(QQ,n);
	Mat := MatrixAlgebra(QQ,n);
	B := Mat!GramMatrix(N);
	b := V![ InnerProduct(u,v) : u in Basis(N) ];
	bool, a := IsConsistent(B,b);
	if bool and &and[ c in ZZ : c in Eltseq(a) ] then
	    // N does not intrinsically meet v
	    Append(~olats,N);
	else
	    // N intrinsically meets v so gets merged.
	    Append(~merge,N);
	end if;
    end for;
    Append(~olats,&+merge);
    return olats;
end function;

intrinsic OrthogonalDecomposition(L::Lat) -> SeqEnum
    {The sequence of orthogonal components.}
    _, B := SuccessiveMinima(L);
    comps := [ ];
    repeat 
	C := [ B[1] ];
	Exclude(~B,B[1]);
	repeat
	    n := #C;
	    C1 := &cat[ [ v : v in B | InnerProduct(u,v) ne 0 ] : u in C ]; 
	    for u in C1 do
		Exclude(~B,u);
	    end for;
	    C cat:= C1;  
	until n eq #C;
	Append(~comps,C);
    until #B eq 0;
    comps := [ Saturation(sub< L | B >,L) : B in comps ];
    // Now we need to determine if these 'components' are really orthogonal:
    M := &+comps;
    A, m := L/M;
    if #A eq 0 then
	return comps;
    else
	for x in Generators(A) do
	    v := x@@m;
	    comps := MergeLattices(L,comps,v);
	end for;
    end if;
    return comps;
end intrinsic;

intrinsic IsSaturated(N::Lat,L::Lat) -> BoolElt
    {Returns true for (N,L) if N equals the intersection of N \otimes \QQ with L.}
    require N subset L and Type(BaseRing(N)) eq RngInt:
	"Arugment 1 must be an integral sublattice of argument 2.";
    return #TorsionSubgroup(L/N) eq 1;
end intrinsic;

intrinsic Saturation(N::Lat,L::Lat) -> BoolElt
    {Returns true for (N,L) if N equals the intersection of N \otimes \QQ with L.}
    require N subset L and Type(BaseRing(N)) eq RngInt:
	"Arugment 1 must be an integral sublattice of argument 2.";
    n := Exponent(TorsionSubgroup(L/N));
    return L meet (1/n)*N;
end intrinsic;
