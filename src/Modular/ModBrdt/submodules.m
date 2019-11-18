////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     Submodule Constructors                         //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Submodule(B::[ModBrdtElt]) -> ModBrdt
    {}
    M := Universe(B);
    X := sub< M`Module | [ x`Element : x in B ] >;
    if X eq M`Module then return M; end if;
    N := New(ModBrdt);
    N`AmbientModule := AmbientModule(M);
    N`Module := X;
    N`IsFull := N`Module cmpeq AmbientModule(M)`Module;
    N`RamifiedPrimes := M`RamifiedPrimes;
    N`Conductor := M`Conductor;
    N`FullLevelIndex := M`FullLevelIndex;
    N`BaseRing := M`BaseRing;
    N`HeckePrecision := 0;
    N`HeckePrimes := [ Integers() | ];
    N`HeckeOperators := [ Mat | ]
	where Mat := MatrixAlgebra(N`BaseRing,Dimension(N`Module));
    // Set some decomposition data in case it doesn't get set later.
    if assigned M`DecompositionIdeal then
	N`DecompositionIdeal := M`DecompositionIdeal;
    else
	print "Warning: DecompositionIdeal not assigned.";
	M`DecompositionIdeal := {@ @};
	N`DecompositionIdeal := {@ @};
    end if;
    return N;
end intrinsic;

intrinsic NewSubspace(M::ModBrdt,p::RngIntElt) -> ModBrdt
    {}
    m := Conductor(M);
    require p gt 1 : "Argument 2 must be greater than 1.";
    require m mod p eq 0 :
	"Argument 2 must divide conductor of argument 1.";
    if not M`IsFull then
	return M meet NewSubspace(M`AmbientModule,p);
    end if;
    if not assigned M`ConductorPrimes then
	M`ConductorPrimes := PrimeDivisors(m);
    end if;
    if not assigned M`DegeneracyIndices then
	M`DegeneracyIndices := [];
    end if;
    N := M;
    k := Index(M`ConductorPrimes,p);
    if IsDefined(M`DegeneracyIndices,k) then
	h := Dimension(M);
	for S in M`DegeneracyIndices[k] do
	    Pi := RMatrixSpace(BaseRing(M),h,#S)!0;
	    for j in [1..#S] do
		for i in S[j] do
		    Pi[i,j] := 1;
		end for;
	    end for;
	    N := Kernel(Pi,N);
	end for;
    else
	degen_indxs := [];
	B := QuaternionOrder(M);
	for A in SuperOrders(B,p) do
	    Pi, degen_indxsA := LeftIdealClassDegeneracies(A,B);
	    Append(~degen_indxs,degen_indxsA);
	    N := Kernel(Pi,N);
	end for;
	M`DegeneracyIndices[k] := degen_indxs;
    end if;
    return N;
end intrinsic;

intrinsic NewSubspace(M::ModBrdt) -> ModBrdt
    {The new cuspidal subspace of M.}
    if Conductor(M) eq 1 then
	return CuspidalSubspace(M);
    end if;
    prms := PrimeDivisors(Conductor(M));
    return &meet[ NewSubspace(M,p) : p in prms ];
end intrinsic;

intrinsic OldSubspace(M::ModBrdt,p::RngIntElt) -> ModBrdt
    {}
    m := Conductor(M);
    require p gt 1 : "Argument 2 must be greater than 1.";
    require m mod p eq 0 :
	"Argument 2 must divide conductor of argument 1.";
    return OrthogonalComplement(NewSubspace(M,p));
end intrinsic;

intrinsic OldSubspace(M::ModBrdt) -> ModBrdt
    {}
    prms := PrimeDivisors(Conductor(M));
    return Saturation(&+[ OldSubspace(M,p) : p in prms ]);
end intrinsic;

