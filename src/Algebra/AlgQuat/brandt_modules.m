//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//             Brandt Modules of Quaternion Ideal Classes                   //
//  Copyright (C) 2000 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                           Accessory Functions                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function NormGramsGroupoid(G);
    auto_nums := [ Integers() | ];
    norm_grams := [ MatrixAlgebra(Integers(),4) | ];
    k := 1;
    h := ClassNumber(G);
    vprintf Brandt : "Computing row entries for %o classes:\n", h;
    for i in [1..h] do
	norm_grams[k] := ReducedGramMatrix(RightOrder(G,i));
	auto_nums[i] :=
	    2*#ShortestVectors(LatticeWithGram(norm_grams[k]));
        k +:= 1;
	for j in [(i+1)..h] do
	    J := IdealClass(G,[i,j]);
	    norm_grams[k] := Norm(J)^-1 * ReducedGramMatrix(J);
	    k +:= 1;
	end for;
        vprintf Brandt : " %3o", i;
        if i mod 16 eq 0 then vprint Brandt : ""; end if;
    end for;
    if h mod 16 ne 0 then vprint Brandt : ""; end if;
    return norm_grams, auto_nums;
end function;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                            Creation functions                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BrandtModule(G::SymAlgQuat : ComputeGrams := false) -> ModBrdt
    {}
    return BrandtModule(G,Integers() : ComputeGrams := ComputeGrams);
end intrinsic;

intrinsic BrandtModule(G::SymAlgQuat,R::Rng : ComputeGrams := false)
    -> ModBrdt
    {The Eichler-Brandt quaternion ideal divisor group of G.}
    M := New(ModBrdt);
    M`IsFull := true;
    M`RamifiedPrimes := RamifiedPrimes(G);
    M`Conductor := Level(G);
    M`FullLevelIndex := FullLevelIndex(G);
    M`BaseRing := R;
    M`LeftIdeals := LeftIdealClasses(G);
    if ComputeGrams then
	M`NormGrams, M`AutoNums := NormGramsGroupoid(G);
    else
        M`AutoNums := [ #Units(RightOrder(I)) : I in M`LeftIdeals ];
    end if;
    M`HeckePrecision := 1;
    M`ThetaSeries := [ PowerSeriesRing(R) | ];
    M`HeckePrimes := [ Integers() | ];
    h := #M`AutoNums;
    MatR := MatrixAlgebra(R,h);
    M`HeckeOperators := [ MatR | ];
    M`Module := RSpace(R,h,
	DiagonalMatrix(MatR,[ w div 2 : w in M`AutoNums ]));
    M`DecompositionIdeal := {@ @};
    return M; 
end intrinsic;

