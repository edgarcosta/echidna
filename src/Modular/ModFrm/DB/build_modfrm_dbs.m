//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                       MODULAR FORMS DATABASE                             //
//                                                                          // 
//         Copyright (C) 2009 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function AtkinLehnerDecomposition(M)
    N := Level(M);
    decmp := [ M ];
    signs := [ [] ];
    for p in PrimeDivisors(N) do
	decmp := &cat[ [ AtkinLehnerSubspace(A,p,+1), AtkinLehnerSubspace(A,p,-1) ] : A in decmp ];
	signs := &cat[ [ Append(sgn,+1), Append(sgn,-1) ] : sgn in signs ];
    end for;  
    return decmp, signs;
end function;

intrinsic BuildModularFormsDatabase(
    Dat::DBUser,S::[RngIntElt],k::RngIntElt,n::RngIntElt : Al := "ModularSymbols")
    {Build the modular forms database of forms on Gamma_0(N) and weight k, for N in S, to precision n.}
    require Dat`DBIdentifier eq "Modular forms" : 
        "Argument 1 must be the database of modular forms.";
    require &and[ N gt 1 : N in S ]:
        "Argument 2 must be a sequence integers greater than 1."; 
    require k gt 0 and k mod 2 eq 0 :
        "Argument 3 must be a non-negative even integer."; 
    require Al in {"ModularSymbols","BrandtModule"} :
	"Parameter Al must be in {\"ModularSymbols\",\"BrandtModule\"}.";
    for N in S do
	s := [ -1 : i in [1..#PrimeDivisors(N)] ]; 
	if <N,k,s> in Dat then 
	    prec := ModularFormsPrecision(Dat,N,k,s);
	    if n eq prec then
		printf "Forms of level %o and weight %o already in database to precision %o.\n", N, k, prec;
		continue;
	    elif n lt prec then
		printf "Forms of level %o and weight %o already in database to precision %o > %o.\n", N, k, prec, n;
		continue;
	    end if;
	end if;
	printf "Building forms of level %o and weight %o\n", N, k; 
	tyme := Cputime();
	if Al eq "ModularSymbols" then
	    X := NewSubspace(CuspidalSubspace(ModularSymbols(N,k,1)));
	else
	    require IsPrime(N) and k eq 2 :
		"Argument 2 must be prime and argument 3 must be 2."; 
	    DBBM := BrandtModuleDatabase();
	    if [N,1] in DBBM then
		M := BrandtModule(DBBM,N,1);
	    else
		M := BrandtModule(N,1);
	    end if;
	    X := CuspidalSubspace(BaseExtend(M,RationalField()));
	end if;
	decomp, signs := AtkinLehnerDecomposition(X);
	for i in [1..#decomp] do
	    B := qExpansionBasis(decomp[i],n);
	    Write(Dat,<N,k,signs[i]>,B : Overwrite := true);
	end for;
	printf "  Time for level %o: %o\n", N, Cputime(tyme);
    end for;
end intrinsic;

intrinsic BuildModularFormsDatabase(
    Dat::DBUser,N::RngIntElt,X::[RngIntElt],n::RngIntElt)
    {Build the modular forms database of forms on Gamma_0(N) and weight k, for k in X, to precision n.}
    require Dat`DBIdentifier eq "Modular forms" : 
        "Argument 1 must be the database of modular forms.";
    require N gt 1 : 
        "Argument 2 must be an integer greater than 1."; 
    require &and[ k gt 0 and k mod 2 eq 0 : k in X ] : 
        "Argument 3 must be a sequence of positive even integers."; 
    for k in X do
	tyme := Cputime();
	X := NewSubspace(CuspidalSubspace(ModularSymbols(N,k,1)));
	decomp, signs := AtkinLehnerDecomposition(X);
        for i in [1..#decomp] do
            B := qExpansionBasis(decomp[i],n);
            Write(Dat,<N,k,signs[i]>,B);
        end for;
	printf "  Time for weight %o: %o\n", k, Cputime(tyme);
    end for;
end intrinsic;

