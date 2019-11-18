////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic StructureConstants(A::AlgAss) -> BoolElt
    {}
    I := [1..Dimension(A)];
    return &cat[ Eltseq(BasisProduct(A,i,j)) : i, j in I ];
end intrinsic;

intrinsic StructureConstants(A::AlgAss,i::RngIntElt,j::RngIntElt)
    -> BoolElt
    {}
    I := [1..Dimension(A)];
    require i in I and j in I : "Arguments 2 and 3 must be in", I; 
    return Eltseq(BasisProduct(A,i,j));
end intrinsic;

intrinsic StructureConstants(A::AlgGrp) -> BoolElt
    {}
    return &cat[ Eltseq(A.i*A.j) : i, j in [1..Dimension(A)] ];
end intrinsic;

intrinsic StructureConstants(A::AlgGrpSub) -> BoolElt
    {}
    return &cat[ Coordinates(A,A.i*A.j) : i, j in [1..Dimension(A)] ];
end intrinsic;

intrinsic StructureConstants(A::AlgMat) -> BoolElt
    {}
    return StructureConstants(AssociativeAlgebra(A));
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic LeftStructureConstants(A::AlgAss,i::RngIntElt) -> BoolElt
    {}
    I := [1..Dimension(A)];
    require i in I : "Argument 2 must be in", I; 
    return &cat[ Eltseq(BasisProduct(A,i,j)) : j in I ];
end intrinsic;

intrinsic RightStructureConstants(A::AlgAss,j::RngIntElt) -> BoolElt
    {}
    I := [1..Dimension(A)];
    require j in I : "Argument 2 must be in", I; 
    return &cat[ Eltseq(BasisProduct(A,i,j)) : i in I ];
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic LeftMultiplicationMatrix(A::AlgAss,i::RngIntElt) -> BoolElt
    {}
    I := [1..Dimension(A)];
    require i in I : "Argument 2 must be in", I; 
    return Matrix([ Eltseq(BasisProduct(A,i,j)) : j in I ]);
end intrinsic;

intrinsic RightMultiplicationMatrix(A::AlgAss,j::RngIntElt) -> BoolElt
    {}
    I := [1..Dimension(A)];
    require j in I : "Argument 2 must be in", I; 
    return Matrix([ Eltseq(BasisProduct(A,i,j)) : i in I ]);
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic StructureConstants(B::[AlgAssElt]) -> BoolElt
    {}
    M := Matrix([ Eltseq(x) : x in B ]);
    consts := [ BaseRing(Universe(B)) | ];
    for x, y in B do
	bool, c := IsConsistent(M,Vector(Eltseq(x*y)));
	require bool :
	    "Argument must form a closed generator sequence.";
	consts cat:= Eltseq(c);
    end for;
    return consts;
end intrinsic;

intrinsic LeftMultiplicationMatrix(x::AlgAssElt)
    -> BoolElt
    {}
    A := Parent(x);
    v := Eltseq(x);
    I := [ i : i in [1..Dimension(A)] | v[i] ne 0 ];
    return &+[ v[i] * LeftMultiplicationMatrix(A,i) : i in I ];
end intrinsic;

intrinsic RightMultiplicationMatrix(x::AlgAssElt)
    -> BoolElt
    {}
    A := Parent(x);
    v := Eltseq(x);
    J := [ j : j in [1..Dimension(A)] | v[j] ne 0 ];
    return &+[ v[j] * RightMultiplicationMatrix(A,j) : j in J ];
end intrinsic;

////////////////////////////////////////////////////////////////////////
