////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                     SATOH AGM Trace Computation                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function VerifyTrace(E,t)
    /*
    This will fail the assertion if Q is always a 2-torsion point. 
    */
    O := E!0;
    K := BaseRing(E);
    q := #K;
    if q eq 5 and t eq 2 then
	return #E(K) eq q-t+1; // Just enumerate points...
    end if;
    for i in [1..8] do
	P := Random(E);
	R := (q+1)*P;
	Q := t*P;
	assert R[1] eq Q[1];
	if Q eq -Q then
	    continue;
	elif R eq Q then
	    return true;
	else
	    return false;
	end if;
    end for;
    assert false;
end function;

function SatohAGMFunction(j,p)
    case p:
    when 2: x := 1/j;
    when 3: x := 1/j;
    when 5: x := 1/j;
    when 7: x := 1/(j+1);
    when 11: x := 1/j;
    when 13: x := 1/(j-5);
    end case;
    return x;
end function;

function SatohFrobeniusNorm(p,x)
    case p:
    when 2:
        // Square of Frobenius:
        y := FrobeniusImage(x);
        Num := (-256*y*(256*y+1)+16*x+1);
        Den := (512*y*(64*y+1)-8*x+1);
        return Exp(Trace(Log(Num div Den)) div 2);
    when 3:
        // Square of Frobenius:
        Num := (3*x+1)*(-19683*x^2-486*x+1);
        Den := (243*x+1)*(-27*x^2+18*x+1);
        return Exp(Trace(Log(Num div Den)) div 2);
    when 5:
        // Square of Frobenius:
        x2 := 5^2*x; x3 := 5*x2;
        Num := (5*(x + 2)*x + 1)*(-x3^2 - 4*x3 + 1);
        Den := (5*(x2 + 2)*x2 + 1)*(-x^2 + 4*x + 1);
        // Log doesn't converge, so we have to call Norm:
        return Sqrt(Norm(Num div Den));
    when 7:
        // Square of Frobenius:
        x2 := 7^2*x;
        Num := (x^2 + 5*x + 1)*(-7^7*x^4 - (2*x2^2 + 9*x2 + 10)*x2 + 1);
        Den := (x2^2 + 5*x2 + 1)*(-7*x^4 + 7*(10*x^2 + 9*x + 2)*x + 1);
        // Log doesn't converge, so we have to call 'Norm'.
        return Sqrt(Norm(Num div Den));
    when 13:
        // Square of Frobenius:
        Num := (x^4 + 19*x^3 + 20*x^2 + 7*x + 1)* 
            (-((13*x)^6 + 10*(13*x)^5 + 46*(13*x)^4
            + 108*(13*x)^3 + 122*(13*x)^2 + 38*(13*x)) + 1);
        Den := ((13*x)^4 + 7*(13*x)^3 + 20*(13*x)^2 + 19*(13*x) + 1)*
            (-x^6 + 38*x^5 + 122*x^4 + 108*x^3 + 46*x^2 + 10*x + 1);
        // Log doesn't converge, so we have to call 'Norm'.
        return Sqrt(Norm(Num div Den));
    end case;
end function;

function SupersingularTrace(E)
    K := BaseField(E);
    p := Characteristic(K);
    n := Degree(K);
    if n eq 1 and p gt 3 then
	return 0;
    end if;
    // Fall back on Magma's built-in.
    return TraceOfFrobenius(E);
end function;

function CMTrace(E)
    return TraceOfFrobenius(E);
end function;

intrinsic SatohAGMTrace(E::CrvEll) -> RngIntElt
    {}
    K := BaseField(E);
    p := Characteristic(K);
    n := Degree(K);
    // Check the trace computation for p = 7 and 13.
    require p in {2,3,5} :
        "Argument must be defined over a finite field of characteristic 2, 3, or 5.";
    require p in {2,3,5,7,13} :
        "Argument must be defined over a finite field of characteristic 2, 3, 5, 7, or 13.";
    // Just enumerate points...
    if n eq 1 then return p^n+1-#E(K); end if;
    j := jInvariant(E);
    prec := ((n+1) div 2)+8;
    vprint Satoh: "Lifting precision:", prec;
    run_tyme := Cputime();
    j := SatohAGMLift(j,prec); 
    vprint Satoh: "Lifting total:    ", Cputime(run_tyme);
    x := SatohAGMFunction(j,p);
    nrm_tyme := Cputime();
    Nrm := SatohFrobeniusNorm(p,x);
    vprint Satoh: "Exp(Trace(Log())):", Cputime(nrm_tyme);
    k := Min(((n+1) div 2)+2,n); m := p^k;
    t := (Integers()!Nrm) mod m;
    if t gt m-t then t -:= m; end if;
    vprint Satoh: "Total trace time: ",Cputime(run_tyme);
    vprint Satoh: "Frobenius trace:  ", t;
    bool := VerifyTrace(E,t);
    return bool select t else -t;
end intrinsic;

