////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                     AGM-X0(N) Trace Computation                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare verbose AGM, 3;

import "frobenius_representation.m" : AGMFrobeniusNorm;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

function VerifyTraceCharacter(E,t)
    // Replace this with an analysis of the character 
    // of Frobenius on some the torsion module. 
    P := Random(E);
    q := #BaseRing(E);
    if (q+1-t)*P ne E!0 then
        assert (q+1+t)*P eq E!0;
        return false;
    end if;
    return true;
end function;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

function AGMInitialValues(j,p,n)
    prec := ((n+1) div 2)+1+(4 div p);
    case p:
    when 2: x := 1/j;
    when 3: x := 1/j;
    when 5: x := 1/j;
    when 7: x := 1/(j+1);
    when 13: x := 1/(j-5);
    end case;
    return x, prec; 
end function;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
    
intrinsic AGMTrace(E::CrvEll : Cyclotomic := true) -> RngIntElt
    {}
    K := BaseField(E);
    p := Characteristic(K);
    n := Degree(K);
    if p ne 2 then Cyclotomic := false; end if;
    require p in {2,3,5,7,13} and n gt 1 :
        "Argument must be defined over a nonprime " *
        "finite field of characteristic 2, 3, 5, 7, or 13.";
    return AGMTrace(E,p);
end intrinsic;

intrinsic AGMTrace(E::CrvEll,N::RngIntElt :
    Cyclotomic := true,
    ExtensionRing := false) -> RngIntElt
    {}
    K := BaseField(E);
    p := Characteristic(K);
    n := Degree(K);
    if p ne 2 then Cyclotomic := false; end if;
    require p in {1,2,3,5,7,13} and n gt 1 :
        "Argument must be defined over a nonprime " *
        "finite field of characteristic 2, 3, 5, 7, or 13.";
    require N eq 1 or N mod p eq 0 :
        "Argument 2 must be zero modulo the characteristic.";
    j := jInvariant(E);
    if N gt 1 then
        x, prec := AGMInitialValues(j,p,n);
    else
        x := j; prec := ((n+1) div 2)+1+(4 div p);
    end if;
    vprint AGM, 2: "Final precision:  ", prec;
    run_tyme := Cputime();
    x := AGMLift(N,x,prec :
        Cyclotomic := Cyclotomic,
        ExtensionRing := ExtensionRing);
    vprint AGM, 1: "Lifting total:    ", Cputime(run_tyme);
    nrm_tyme := Cputime();
    Nrm := AGMFrobeniusNorm(N,p,x);
    vprint AGM, 1: "Exp(Trace(Log())):", Cputime(nrm_tyme);
    if p eq 2 then prec -:= 1; end if;
    m := p^prec;
    t := (Integers()!Nrm) mod m;
    if t gt m-t then t -:= m; end if;
    vprint AGM, 1: "Total trace time: ",Cputime(run_tyme);
    vprint AGM, 1: "Frobenius trace:  ", t;
    bool := VerifyTraceCharacter(E,t);
    return bool select t else -t;
end intrinsic;

