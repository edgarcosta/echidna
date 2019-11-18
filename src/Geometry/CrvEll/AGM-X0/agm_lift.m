////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                     AGM-X0(N) Lifting Algorithms                   //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "analytic_frobenius_lift.m" : AnalyticAGMLift;
import "modular_correspondences.m" : PhiX0, DxPhiX0, DyPhiX0;

forward LinearAGMLift, BlockAGMLift;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

function MagmaWordSize(p)
    // Returns n such that p^n < 2^30.
    case p:
    when 2: return 29;
    when 3: return 18;
    when 5: return 12;
    when 7: return 10;
    when 13: return 8;
    end case;
end function;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

intrinsic AGMLift(N::RngIntElt,x::FldFinElt,prec::RngIntElt : 
    Cyclotomic := true,
    ExtensionRing := false) -> RngPadResExtElt
    {}
    F := Parent(x);
    n := Degree(F);
    p := Characteristic(F);
    require p in {2,3,5,7,13} : // and n gt 1 :
        "Argument must be defined over a nonprime " *
        "finite field of characteristic 2, 3, 5, 7, or 13.";
    require N eq 1 or N mod p eq 0 :
        "Argument 1 must be zero modulo the characteristic.";
    require x ne 0 :
        "Argument 2 must be nonzero.";
    word := Min(MagmaWordSize(p),prec);
    tyme := Cputime();
    if Type(ExtensionRing) eq BoolElt then
        Z := pAdicQuotientRing(p,prec);
        if Cyclotomic then
            S := CyclotomicUnramifiedExtension(Z,n);
        else
            S := UnramifiedExtension(Z,n);
        end if;
    else
        S := ChangePrecision(ExtensionRing,prec);
    end if;
    Embed(ResidueClassField(S),Parent(x));
    if Cyclotomic then
	vprint AGM, 2: "Cyclotomic setup  ", Cputime(tyme);
    end if;
    // Do an analytic list using initial segments of the
    // analytic Frobenius; can add a precision argument.
    if N gt 1 then
        analt := word;
        R := ChangePrecision(S,analt);
	tyme := Cputime();
	x := AnalyticAGMLift(N,R!x);
    else
        analt := 0;
    end if;
    vprint AGM, 2: "Analytic lift:    ", Cputime(tyme);
    // Currently the linear lifting phase is done with 
    // the precomputed analytic Frobenius.
    if analt lt word then
	R := ChangePrecision(S,word);
        tyme := Cputime();
        x := LinearAGMLift(N,R!x); 
        vprint AGM, 2: "Linear lift:      ", Cputime(tyme);
    end if;
    // Once the initial lift is complete to one word block,
    // lift using a blockwise algorithm. 
    tyme := Cputime();
    x := BlockAGMLift(N,S,x); 
    vprint AGM, 2: "Total block lift: ", Cputime(tyme);
    return x;
end intrinsic;

function LinearAGMLift(N,x)
    // Lift x linearly to a root of the modular polynomial, 
    // up to the precision of the residue class ring.
    S := Parent(x);
    p := Prime(S);
    FF := ResidueClassField(S);
    j := 1;
    repeat 
        Delta := PhiX0(N,p,x,FrobeniusImage(x));
        j := Valuation(Delta);
        if j eq 1 then
            vprint AGM, 2: "Initial valuation:", j;
        end if;
	if N eq 1 then
	    print "0 VALUATION:", j;
	    print "1 VALUATION:", Valuation(DxPhiX0(N,p,x,FrobeniusImage(x)));
	    x +:= p^j*S!Root(FF!(Delta div p^j),p);
	else
	    x +:= p^j*S!Root(FF!(Delta div p^j),p);
	end if;
    until Delta eq 0;
    vprint AGM, 2: "Final valuation:  ", j;
    return x;
end function;

function BlockAGMLift(N,S,x);
    // S is a ring of the desired final precision, and R = Parent(x)
    // is a ring whose precision is truncated to optimize operations 
    // on computer words. 
    R := Parent(x);
    p := Prime(S);
    n := Degree(S);
    prec := Precision(S);
    word := Precision(R);
    FF := ResidueClassField(S);
    tyme := Cputime();
    y := FrobeniusImage(x);
    DX := DxPhiX0(N,p,x,y);
    DY := DyPhiX0(N,p,x,y);
    m := 1;
    q := p^word; 
    prec0 := word; 
    vprint AGM, 2: "Block lift init:  ", Cputime(tyme);
    while true do
        Rm := ChangePrecision(S,Min(prec,(m+1)*word));
        x := Rm!x;
        ntyme := Cputime();
        vprintf AGM, 2: "  Eval at prec %o: ", (m+1)*word;
        Rx := R!(PhiX0(N,p,x,FrobeniusImage(x)) div q);
        vprint AGM, 2: Cputime(ntyme);
        for i in [0..word-1] do
            if m*word+i eq prec then return x; end if;
            dx := R!Root(FF!Rx,p);
            Rx +:= DX*dx + DY*FrobeniusImage(dx);
            Rx div:= p;
            x +:= q*(Rm!dx);
            q *:= p;
        end for;
        vprint AGM, 2: "Block lift step:  ", Cputime(tyme);
        m +:= 1;
    end while;
    return x;
end function;

