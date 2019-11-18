////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   Brandt Module Recomposition                      //
//                           David Kohel                              //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic '+'(M::ModBrdt,N::ModBrdt) -> ModBrdt
    {}
    if IsAmbientSpace(M) then return M; end if;
    if IsAmbientSpace(N) then return N; end if;
    require AmbientModule(M) eq AmbientModule(N) :
	"Arguments must lie in the same ambient module.";
    S := New(ModBrdt);
    S`AmbientModule := AmbientModule(M);
    S`Module := M`Module + N`Module;
    S`IsFull := S`Module eq (S`AmbientModule)`Module;
    S`RamifiedPrimes := M`RamifiedPrimes;
    S`Conductor := M`Conductor;
    S`FullLevelIndex := M`FullLevelIndex;
    S`BaseRing := M`BaseRing;
    S`HeckePrecision := 0;
    S`HeckePrimes := [ Integers() | ];
    S`HeckeOperators := [ Mat | ]
        where Mat := MatrixAlgebra(S`BaseRing,Dimension(S`Module));
    S`DecompositionIdeal := {@ @};
    return S;
end intrinsic;

intrinsic Saturation(M::ModBrdt) -> ModBrdt
    {}
    V := Saturation(M`Module);
    // Hack around a bug in Saturation for modules 
    // with specified inner product matrices...
    U := AmbientModule(M)`Module;
    V := sub< U | [ U!v : v in Basis(V) ] >;
    // End Hack.
    if M`Module eq V then return M; end if;
    N := New(ModBrdt);
    N`AmbientModule := AmbientModule(M);
    N`Module := V;
    N`IsFull := N`Module eq (M`AmbientModule)`Module;
    N`RamifiedPrimes := M`RamifiedPrimes;
    N`Conductor := M`Conductor;
    N`FullLevelIndex := M`FullLevelIndex;
    N`BaseRing := M`BaseRing;
    N`HeckePrecision := 0;
    N`HeckePrimes := [ Integers() | ];
    N`HeckeOperators := [ Mat | ]
        where Mat := MatrixAlgebra(N`BaseRing,Dimension(N`Module));
    if assigned M`DecompositionIdeal then
	N`DecompositionIdeal := M`DecompositionIdeal;
    else
	N`DecompositionIdeal := {@ @};
    end if;
    return N;
end intrinsic;
