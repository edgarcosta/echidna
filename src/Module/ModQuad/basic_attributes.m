////////////////////////////////////////////////////////////////////////
//                                                                    //
//              BASIC ATTRIBUTES OF LATTICES AND GENERA               //
//                           David R. Kohel                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

ZZ := Integers();
QQ := Rationals();

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

intrinsic Content(L::Lat) -> RngIntElt
    {The content of the lattice L.}
    require IsExact(L) : "Argument must be an exact lattice";
    S := Eltseq(GramMatrix(L));
    if Type(Universe(S)) eq FldRat then
	num := GCD([Numerator(x) : x in S ]); 
	den := LCM([ Denominator(x) : x in S ]);
	return num/den;
    end if;
    return GCD(S);
end intrinsic;

intrinsic Content(G::SymGen) -> RngIntElt
    {}
    S := Eltseq(GramMatrix(Representative(G)));
    if Type(Universe(S)) eq FldRat then
	num := GCD([Numerator(x) : x in S ]); 
	den := LCM([ Denominator(x) : x in S ]);
	return num/den;
    end if;
    return GCD(S);
end intrinsic;

intrinsic Content(G::SymGenLoc) -> RngIntElt
    {The content of the genus G.}
    p := Prime(G);
    S := Eltseq(GramMatrix(Representative(G)));
    return p^Min([ Valuation(c,p) : c in S | c ne 0 ]);
end intrinsic;

intrinsic Dual(L::Lat) -> Lat
    {The dual of the lattice L.}
    require IsExact(L) : "Argument must be an exact lattice";
    return InternalDualUnscaled(L);
end intrinsic;

intrinsic Dual(G::SymGen) -> SymGen
    {The dual of the genus G.}
    L := Representative(G);
    return Genus(InternalDualUnscaled(L));
end intrinsic;

intrinsic Level(L::Lat) -> RngIntElt
    {}
    require IsIntegral(L) :
	"Argument must be an exact integral lattice";
    c := Content(L);
    if c ne 1 then L := ScaledLattice(L,1/c); end if;
    if IsOdd(L) then L := ScaledLattice(L,2); end if;
    M := Dual(L);
    if IsOdd(M) then c *:= 2; end if;
    return c*Exponent(quo< M | L >);
end intrinsic;

intrinsic Level(G::SymGen) -> RngIntElt
    {The level of the lattice L.}
    L := Representative(G);
    require IsIntegral(L) : "Argument must be an exact lattice";
    return Level(L);
end intrinsic;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

