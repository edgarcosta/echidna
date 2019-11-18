//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                SUPERSINGULAR MODULE DATABASE CONSTRUCTOR                 //
//                                                                          //
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildSupersingularPolynomialsDatabase(
    Dat::DBUser,S::[RngIntElt])
    {}
    require Dat`DBIdentifier eq "Supersingular divisors" : 
        "Argument 1 must be the database of supersingular divisors.";
    for p in S do
        require IsPrime(p) : "Elements of argument 2 must be prime.";
        K := FiniteField(p);
        H := SupersingularPolynomial(K);
        SS := {@ h[1] : h in Factorization(H) @};
        Write(Dat,SS);
    end for;
end intrinsic;

function SupersingularThetaSort(SS,TT)
    return SS;
end function;

intrinsic BuildSupersingularDatabase(
    Dat::DBUser,S::[RngIntElt])
    {}
    require Dat`DBIdentifier eq "Supersingular divisors" : 
        "Argument 1 must be the database of supersingular divisors.";
    DBBM := BrandtModuleDatabase();
    function DiscriminantMatrix(M)
        return MinkowskiGramReduction(
            Matrix(3,[ M[1,1]*M[i,j]-M[1,i]*M[1,j] : i, j in [2..4] ]));
    end function;
    function ScaledGramDualMatrix(M,n)
        return MinkowskiGramReduction(MatrixAlgebra(Integers(),3)!
            (n*GramMatrix(Dual(LatticeWithGram(M)))));
    end function;
    for p in S do
        require IsPrime(p) : "Elements of argument 2 must be prime.";
        //BuildSupersingularPolynomialsDatabase(Dat,p);
        M := BrandtModule(DBBM,p, 1);
        h := Dimension(M);
        SSNorm := {@ ReducedNormGram(M,[i,i]) : i in [1..h] @};
        SSDisc := {@ DiscriminantMatrix(M) : M in SSNorm @};
        SSDDsc := {@ ScaledGramDualMatrix(M,2*p) : M in SSDisc @};
        SSThta := {@ ThetaSeries(LatticeWithGram(D),4*p) : D in SSDisc @};
        SSDtht := {@ ThetaSeries(LatticeWithGram(D),4*p) : D in SSDDsc @};
        if false then
            SSPoly := SupersingularPolynomials(Dat,p);
            SSPoly := SupersingularThetaSort(SSPoly,SSThta);
            Write(Dat,SSPoly);
        end if;
        Write(Dat,SSNorm,SSDisc,SSDDsc,p);
        Write(Dat,SSThta,SSDtht,p);
    end for;
end intrinsic;

