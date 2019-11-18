////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   ASSOCIATIVE ALGEBRA CONSTRUCTORS                 //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic BaseChange(A::AlgAss,K::Rng) -> AlgAss
    {}
    return ChangeRing(A,K); 
end intrinsic;

intrinsic BaseChange(A::AlgGrp,K::Rng) -> AlgGrp
    {}
    return ChangeRing(A,K); 
end intrinsic;

intrinsic BaseChange(A::AlgMat,K::Rng) -> AlgMat
    {}
    return ChangeRing(A,K); 
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic PermutationMatrix(A::AlgMat,g::GrpPermElt) -> AlgMatElt
    {}
    require Degree(A) eq Degree(Parent(g)) :
	"Argument 1 and parent of argument 2 must have equal degrees.";
    M := A!0;
    for i in [1..Degree(Parent(g))] do
	M[i,i^g] := 1;
    end for;
    return M;
end intrinsic;

intrinsic AssociativeAlgebra(A::AlgGrp) -> AlgAss
    {}
    return Algebra(A);
end intrinsic;

intrinsic AssociativeAlgebra(A::AlgGrpSub) -> AlgAss
    {}
    B, m := Algebra(GroupAlgebra(A));
    return sub< B | [ m(x) : x in Generators(A) ] >;
end intrinsic;

intrinsic AssociativeAlgebra(A::AlgMat) -> AlgAss
    {}
    return Algebra(A);
end intrinsic;

intrinsic AssociativeAlgebra(R::Rng,G::GrpPerm) -> AlgAss
    {}
    return Algebra(MatrixAlgebra(R,G));
end intrinsic;

intrinsic MatrixAlgebra(R::Rng,G::GrpPerm) -> AlgAss
    {}
    A := MatrixAlgebra(R,Degree(G));
    gens := [ PermutationMatrix(A,g) : g in GeneratorsSequence(G) ];
    return sub< A | gens >;
end intrinsic;

