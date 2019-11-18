////////////////////////////////////////////////////////////////////////
//                         Associated Spaces                          //
////////////////////////////////////////////////////////////////////////

BRANDT_MESG :=
    "(try creating the supersingular module with " *
    "the Brandt parameter set to true instead)";

////////////////////////////////////////////////////////////////////////
//          Ambient Space, Module, Basis, and Coordinates             //
////////////////////////////////////////////////////////////////////////

intrinsic RSpace(M::ModSS) -> ModTupRng, Map
    {}
    // Should put the inner product structure on this...
    if not assigned M`rspace then
	assert IsAmbientSpace(M);
	W := DiagonalMatrix(MonodromyWeights(M));
	M`rspace := RSpace(Integers(),Dimension(M),W);
    end if;
    V := M`rspace;
    return V, hom<V -> M | x :-> M!x,  x :-> V!Eltseq(x)>;
end intrinsic;

intrinsic AmbientSpace(M::ModSS) -> BoolElt
    {}
    if not assigned M`ambient_space then
	return M;
    end if;
    return M`ambient_space;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//           Associated Modules of Brandt and Modular Symbols         //
////////////////////////////////////////////////////////////////////////

intrinsic BrandtModule(M::ModSS) -> ModBrdt
    {}
    require IsAmbientSpace(M) : "Argument 1 must be an ambient space.";
    if not assigned M`brandt_module then
	M`brandt_module := BrandtModule(Prime(M),AuxiliaryLevel(M));
    end if;
    return M`brandt_module;
end intrinsic;

intrinsic ModularSymbols(M::ModSS : Proof := true) -> ModSym
    {}
    return ModularSymbols(M, 0 : Proof := Proof);
end intrinsic;

intrinsic ModularSymbols(M::ModSS, sign::RngIntElt : Proof := true) -> ModSym
    {} 
    require sign in {-1,0,1} : "Argument 2 must be -1, 0, or 1.";
    if not assigned M`modular_symbols or 
	Type(M`modular_symbols[sign+2]) eq BoolElt then
	if not assigned M`modular_symbols then
	    M`modular_symbols := [* false, false, false *];
	end if;       
	N := AuxiliaryLevel(M);
	p := Prime(M);
	if IsAmbientSpace(M) then
	    modsym := NewSubspace(ModularSymbols(N*p, 2, sign),p);
	    M`modular_symbols[sign+2] := modsym;
	else
	    modsym := ModularSymbols(AmbientSpace(M),sign);
	    p := 2;
	    if UsesMestre(M) and N mod p eq 0 then
		p := 3;
	    end if;
	    factor := sign eq 0 select 2 else 1;
	    while Dimension(EisensteinSubspace(modsym)) + 
		(Dimension(CuspidalSubspace(modsym)) div 2) 
		    gt Dimension(M) and
		    (UsesBrandt(M) or (UsesMestre(M) and p le 3 and N mod p ne 0)) do
		    
		    fp := CharacteristicPolynomial(HeckeOperator(M,p) : 
		    Al := "Modular", Proof := Proof);
		modsym := Kernel([<p, fp>], modsym);
		p := NextPrime(p);
	    end while;
	    if Dimension(EisensteinSubspace(modsym)) + 
		(Dimension(CuspidalSubspace(modsym)) div 2) 
		gt Dimension(M) then
		error "Unable to compute corresponding modular symbols space "*
		    BRANDT_MESG;
	    end if;
	    M`modular_symbols[sign+2] := modsym;
	end if;
    end if;
    return M`modular_symbols[sign+2];
end intrinsic;

