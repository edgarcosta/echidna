//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Linear relations (over the integers) among p-adic elements and vectors  //
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

intrinsic LinearRelations(S::[RngPadResElt] : 
    LLLReduction := true, MaxRelations := 0, Scale := false) -> ModTupRng
    {The linear relation space OVER THE INTEGERS of a sequence of p-adic quotient ring elements.}
    R := Universe(S);
    p := ResidueCharacteristic(R);
    q := p^Precision(R);
    n := #S;
    vprintf pAdicRelations :
	"Setting up matrix of size %o x %o\n", n, 1;
    ZZ := Integers();
    V := RSpace(ZZ,n);
    M := Matrix(ZZ,1,[ ZZ!a : a in S ] cat [ q ]);
    B := BasisMatrix(Kernel(M));
    if Scale then
	s1 := q; n0 := Nrows(B); m0 := Ncols(B);  
	B := HorizontalJoin(
	    s1*Submatrix(B,1,1,n0,n), Submatrix(B,1,n+1,n0,m0-n));
    end if;
    vprintf pAdicRelations :
	"        ...kernel of size %o x %o\n", Nrows(B), Ncols(B);
    if LLLReduction then
	N := LLL(B);
	if MaxRelations ne 0 and Nrows(N) gt MaxRelations then
	    N := Submatrix(N,1,1,MaxRelations,Ncols(N));
	end if;
    elif MaxRelations eq 0 then
	N := ShortestVectorsMatrix(Lattice(B));
    else
	N := ShortestVectorsMatrix(Lattice(B) : Max := MaxRelations);
    end if;
    B := [ V | V!Eltseq(N[i])[[1..n]] : i in [1..Rank(N)] ]; 
    r := Rank(N);
    if Scale then
	B := [ V |
	    V![ c div s1 : c in Eltseq(N[i])[[1..n]] ] : i in [1..r] ];
    else
	B := [ V | V!Eltseq(N[i])[[1..n]] : i in [1..Rank(N)] ]; 
    end if;
    return RSpaceWithBasis(B);
end intrinsic;

intrinsic LinearRelations(S::[RngPadResExtElt] : 
    LLLReduction := true, MaxRelations := 0, Scale := false) -> ModTupRng
    {The linear relation space OVER THE INTEGERS of a sequence of p-adic quotient ring extension elements.}
    Scale := true;
    Q := Universe(S);
    R := BaseRing(Q);
    p := ResidueCharacteristic(R);
    q := p^Precision(R);
    n := #S;
    d := Degree(Q);
    vprintf pAdicRelations :
	"Setting up matrix of size %o x %o\n", n, d;
    ZZ := Integers();
    V := RSpace(ZZ,n);
    I := IdentityMatrix(ZZ,d);
    M := VerticalJoin(Matrix(ZZ,[ Eltseq(a) : a in S ]),q*I);
    B := BasisMatrix(Kernel(M));
    if Scale then
	s1 := q; n0 := Nrows(B); m0 := Ncols(B);
	s1 := 1;
	B := HorizontalJoin(
	    s1*Submatrix(B,1,1,n0,n), Submatrix(B,1,n+1,n0,m0-n));
    end if;
    vprintf pAdicRelations :
	"        ...kernel of size %o x %o\n", Nrows(B), Ncols(B);
    if LLLReduction then
	N := LLL(B);
	if MaxRelations ne 0 and Nrows(N) gt MaxRelations then
	    N := Submatrix(N,1,1,MaxRelations,Ncols(N));
	end if;
    elif MaxRelations eq 0 then
	N := ShortestVectorsMatrix(Lattice(B));
    else
	N := ShortestVectorsMatrix(Lattice(B) : Max := MaxRelations);
    end if;
    r := Rank(N);
    if Scale then
	x := Ncols(N);
	y := Nrows(N);
	if GetVerbose("pAdicRelations") ge 2 then
	    avg_valid := &+[ Log(2,1+Abs(c div s1)) : c in Eltseq(N[1])[[1..n]] ]/n;
	    max_valid := Max([ Log(2,1+Abs(c div s1)) : c in Eltseq(N[1])[[1..n]] ]);
	    avg_extra := &+[ Log(2,1+Abs(c div s1)) : c in Eltseq(N[1])[[n+1..x]] ]/(x-n);
	    max_extra := Max([ Log(2,1+Abs(c div s1)) : c in Eltseq(N[1])[[n+1..x]] ]);
	    min_randm := Min([ Log(2,1+Abs(c div s1)) : c in Eltseq(N[y]) ]);
	    avg_randm := &+[ Log(2,1+Abs(c div s1)) : c in Eltseq(N[y]) ]/x;
	    max_randm := Max([ Log(2,1+Abs(c div s1)) : c in Eltseq(N[y]) ]);
	    print "Avg valid relations:", avg_valid;
	    print "Max valid relations:", max_valid;
	    print "Avg extraneous part:", avg_extra;
	    print "Max extraneous part:", max_extra;
	    print "Min random relation:", min_randm;
	    print "Avg random relation:", avg_randm;
	    print "Max random relation:", max_randm;
	    printf "Total bits: %o (1:%o)\n", Log(2,q), Log(2,q)/avg_randm;
	end if;
	B := [ V |
	    V![ c div s1 : c in Eltseq(N[i])[[1..n]] ] : i in [1..r] ];
    else
	B := [ V | V!Eltseq(N[i])[[1..n]] : i in [1..r] ]; 
    end if;
    return RSpaceWithBasis(B);
end intrinsic;

////////////////////////////////////////////////////////////////////////
// Relations (over ZZ) for p-adic extension elements
////////////////////////////////////////////////////////////////////////

intrinsic LinearRelations(S::[ModTupRngElt[RngPadRes]] : 
    LLLReduction := true, MaxRelations := 0, Scale := false) -> ModTupRng
    {The linear relation space OVER THE INTEGERS of a sequence of vectors over a p-adic quotient ring.}
    Scale := true;
    Q := Universe(S);
    R := BaseRing(Q);
    p := ResidueCharacteristic(R);
    q := p^Precision(R);
    n := #S;
    d := Degree(Q);
    vprintf pAdicRelations :
	"Setting up matrix of size %o x %o\n", n, d;
    ZZ := Integers();
    V := RSpace(ZZ,n);
    I := IdentityMatrix(ZZ,d);
    M := VerticalJoin(Matrix(ZZ,[ Eltseq(a) : a in S ]),q*I);
    B := BasisMatrix(Kernel(M));
    if Scale then
	s1 := q; n0 := Nrows(B); m0 := Ncols(B);
	s1 := 1;
	B := HorizontalJoin(
	    s1*Submatrix(B,1,1,n0,n), Submatrix(B,1,n+1,n0,m0-n));
    end if;
    vprintf pAdicRelations :
	"        ...kernel of size %o x %o\n", Nrows(B), Ncols(B);
    if LLLReduction then
	N := LLL(B);
	if MaxRelations ne 0 and Nrows(N) gt MaxRelations then
	    N := Submatrix(N,1,1,MaxRelations,Ncols(N));
	end if;
    elif MaxRelations eq 0 then
	N := ShortestVectorsMatrix(Lattice(B));
    else
	N := ShortestVectorsMatrix(Lattice(B) : Max := MaxRelations);
    end if;
    r := Rank(N);
    if Scale then
	x := Ncols(N);
	y := Nrows(N);
	if GetVerbose("pAdicRelations") ge 2 then
	    avg_valid := &+[ Log(2,1+Abs(c div s1)) : c in Eltseq(N[1])[[1..n]] ]/n;
	    max_valid := Max([ Log(2,1+Abs(c div s1)) : c in Eltseq(N[1])[[1..n]] ]);
	    avg_extra := &+[ Log(2,1+Abs(c div s1)) : c in Eltseq(N[1])[[n+1..x]] ]/(x-n);
	    max_extra := Max([ Log(2,1+Abs(c div s1)) : c in Eltseq(N[1])[[n+1..x]] ]);
	    min_randm := Min([ Log(2,1+Abs(c div s1)) : c in Eltseq(N[y]) ]);
	    avg_randm := &+[ Log(2,1+Abs(c div s1)) : c in Eltseq(N[y]) ]/x;
	    max_randm := Max([ Log(2,1+Abs(c div s1)) : c in Eltseq(N[y]) ]);
	    print "Avg valid relations:", avg_valid;
	    print "Max valid relations:", max_valid;
	    print "Avg extraneous part:", avg_extra;
	    print "Max extraneous part:", max_extra;
	    print "Min random relation:", min_randm;
	    print "Avg random relation:", avg_randm;
	    print "Max random relation:", max_randm;
	    printf "Total bits: %o (1:%o)\n", Log(2,q), Log(2,q)/avg_randm;
	end if;
	B := [ V |
	    V![ c div s1 : c in Eltseq(N[i])[[1..n]] ] : i in [1..r] ];
    else
	B := [ V | V!Eltseq(N[i])[[1..n]] : i in [1..r] ]; 
    end if;
    return RSpaceWithBasis(B);
end intrinsic;
