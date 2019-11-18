////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          Modular Symbols                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic AmbientCuspidalModularSymbols(M::ModBrdt) -> ModSym
    {}
    A := AmbientModule(M);
    if not assigned A`CuspidalModularSymbols then
	MS := CuspidalSubspace(ModularSymbols(Level(M)));
	for p in PrimeDivisors(Discriminant(M)) do
	    MS := NewSubspace(MS,p);
	end for;
	A`CuspidalModularSymbols := MS;
    end if;
    return A`CuspidalModularSymbols;
end intrinsic;
    
intrinsic ModularSymbols(M::ModBrdt) -> ModSym
    {}
    require IsCuspidal(M) : "Argument must be cuspidal.";
    if assigned M`ModularSymbols then
	return M`ModularSymbols;
    end if;
    MS := AmbientCuspidalModularSymbols(M);
    if M eq CuspidalSubspace(AmbientSpace(M)) then
	return MS;
    end if;
    p := 2; 
    N := Level(M);
    while Dimension(MS) gt 2*Dimension(M) do
	while N mod p eq 0 do
	    p := NextPrime(p);
	end while;
	f := MinimalPolynomial(HeckeOperator(M,p));
	MS := Kernel([<p,f>],MS);
	p := NextPrime(p);
    end while;
    M`ModularSymbols := MS;
    return MS;
end intrinsic;


