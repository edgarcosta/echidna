////////////////////////////////////////////////////////////////////////
//                                                                    //
//           COMMON FUNCTIONS FOR LOCAL GENUS COMPUTATIONS            //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

ZZ := Integers();
QQ := Rationals();

////////////////////////////////////////////////////////////////////////
//            GENERIC LATTICE OR ZZ-MODULE CONSTRUCTOR                //
////////////////////////////////////////////////////////////////////////

function RLattice(TYPE,M);
    // PRE: Given TYPE in {Lat,ModTupRng,ModTupFld}, and a
    // symmetric matrix M.
    // POST: Returns a lattice (preferable) or a module, depending 
    // on TYPE and whether M is definite or indefinite.
    if TYPE eq Lat or IsPositiveDefinite(M) then
	return LatticeWithGram(M);
    end if;
    n := Degree(Parent(M));
    bool, M := IsCoercible(MatrixAlgebra(ZZ,n),M);
    if bool then
	return RSpace(ZZ,n,M);
    else
	return RSpace(QQ,n,M);
    end if;
end function;

////////////////////////////////////////////////////////////////////////
//                CONTENT OF ZZ-MODULE OR LATTICE                     //
////////////////////////////////////////////////////////////////////////

function LatticeContent(M)
    S := Eltseq(GramMatrix(M));
    if Type(Universe(S)) eq FldRat then
	num := GCD([ Numerator(c) : c in S ]);
	den := LCM([ Denominator(c) : c in S ]);
	return num/den;
    end if;
    return GCD(S);
end function;

////////////////////////////////////////////////////////////////////////
//        p-ADIC RING AND FIELD REPRESENTATIVES MOD SQUARES           //
////////////////////////////////////////////////////////////////////////

function UnitSquareClass(u,p)
    // PRE: u is an integer or rational and p is prime 
    // POST: Returns the smallest positive integer or 
    // rational in the same square class as u.
    e := Valuation(u,p);
    q := e eq 0 select 1 else p^e;
    if Type(u) eq FldRatElt then
	u /:= q;
	u := Numerator(u)*Denominator(u);
    else
	u div:= q;
    end if;
    if p eq 2 then
	return (u mod 8)*q; 
    elif KroneckerSymbol(u,p) eq 1 then
	return q;
    end if;
    c := 2;
    while KroneckerSymbol(c,p) eq 1 do
	c := NextPrime(c);
    end while;
    return c*q;
end function;


function FieldSquareClass(u,p)
    // PRE: u is an integer or rational and p is prime 
    // POST: Returns the smallest positive integer or 
    // rational in the same square class as u.
    e := Valuation(u,p); 
    r := p^(e mod 2);
    if Type(u) eq FldRatElt then
	u /:= p^e;
	u := Numerator(u)*Denominator(u);
    else
	u div:= p^e;
    end if;
    if p eq 2 then
	return (u mod 8)*r;
    elif KroneckerSymbol(u,p) eq 1 then
	return r;
    end if;
    c := 2;
    while KroneckerSymbol(c,p) eq 1 do
	c := NextPrime(c);
    end while;
    return c*r;
end function;

