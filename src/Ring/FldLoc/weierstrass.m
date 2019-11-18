////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   WEIERSTRASS PREPARATION THEOREM                  //
//                             David Kohel                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

/*
> prec := 60;
> dble_prec := 2*(prec + 2);
> R := pAdicRing(2);
> Q<x> := PowerSeriesRing(R);
> f := Q!CyclotomicPolynomial(12) + O(R.1^dble_prec);
> g := 1/(1 - 2*x + 2*x^2 + O(x^dble_prec));
> h := f*g;
> f1, g1 := WeierstrassPreparation(h : Precision := prec);
> [ Valuation(Coefficient(f1,i)-Coefficient(f,i)) : i in [0..4] ];
*/

intrinsic WeierstrassPreparation(x::RngSerElt : 
    ReductionPrecision := 0, LiftingPrecision := 20)
    -> RngUPolElt, RngSerElt
    {}
    Q := Parent(x);
    R := BaseRing(Q);
    print "Type =", Type(R);
    require Type(R) in {FldPad,RngPad,RngPadRes,RngPadResExt} :  
	"Base ring of argument's parent must be a local ring.";
    p := Prime(R);
    if Type(R) eq RngPadRes then
	prec := Precision(R);
	R := pAdicRing(p,prec);
	S, n0 := Eltseq(x);
	bool, S := CanChangeUniverse(S,pAdicRing(p,prec));
	assert bool;
	bool, S := CanChangeUniverse(S,Integers());
	assert bool;
	bool, S := CanChangeUniverse(S,R);
	assert bool;
	Q := LaurentSeriesRing(R); 
	x := Q.1^n0*LaurentSeriesRing(R)!S;
    else 
	assert Type(R) ne RngPadResExt;
    end if;
    S, n0 := Eltseq(x); 
    r := Min([ Valuation(c) : c in Eltseq(x) | c ne 0 ]);
    if ReductionPrecision gt r then
	r := ReductionPrecision;
    end if;
    N := Max([ n0 + i-1 : i in [1..#S] | Valuation(S[i]) eq r ]);
    P := PolynomialRing(R);
    x0 := P.1^n0*P!S;
    f0 := P.1^n0*P![ Integers()!(c+O(R!p^(r+1))) : c in S[1..N-n0+1] ]; 
    f1 := P!1;
    f0, f1 := HenselLift(x0,f0,f1 : Precision := LiftingPrecision);
    return f0, Q!f1;
end intrinsic;

