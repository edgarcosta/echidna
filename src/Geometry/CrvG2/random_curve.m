//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                  RANDOM GENUS 2 CURVES BY MODULI                         //
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// 2007.08: Added random curves with given real discriminants

/*
2011.01: Cleaned up Level2 function -- TODO: come up with uniform syntax.
*/

intrinsic RandomGenus2CurveWithRM(FF::FldFin,D::RngIntElt :
    Level2ThetaNull := false, Rosenhain := false, AbsolutelySimple := false) -> CrvHyp
    {Caution: returns only ordinary curves...and for char(FF) > 2 returns
    only curves with full 2-torsion subgroup.}
    require D gt 0 and D mod 4 in {0,1} and D gt 1 :
        "Argument 2 must be a real discriminant greater than 1.";
    p := Characteristic(FF); q := #FF;
    if Level2ThetaNull then
        if p eq 2 then
            Level2ThetaNullDiscs := {5,8,9,12,13,17,24,28,40,44,56,60};
        else
            Level2ThetaNullDiscs := {4,5,8,9,12,13,16,17,20,24,28,32,40,44,48,52,56,60}; // -- error in 68
        end if;
        require D in Level2ThetaNullDiscs : 
            "Argument 2 must be D in " * Sprint(Level2ThetaNullDiscs) *".";
        if Characteristic(FF) eq 2 then
            xx := RandomAffineLevel2ThetaNullPointWithRM(FF,D : AbsolutelySimple := AbsolutelySimple);
            return HyperellipticCurveFromAffineLevel2ThetaNullPoint(xx);
        elif Characteristic(FF) eq 3 and D eq 17 then
            ee := RandomRosenhainInvariantsWithRM(FF,D : AbsolutelySimple := AbsolutelySimple);
            return HyperellipticCurveFromRosenhainInvariants(ee);
        else
            xx := RandomLevel2ThetaNullPointWithRM(FF,D : AbsolutelySimple := AbsolutelySimple);
            ee := Level2ThetaNullPointToRosenhainInvariants(xx);
            return HyperellipticCurveFromRosenhainInvariants(ee);
        end if;
    elif Rosenhain then
        require p ne 2 : "Argument 1 must be a finite field of odd characteristic.";
        require q ge 5 : "Argument 1 must be a finite field of at least 5 elements.";
        ee := RandomRosenhainInvariantsWithRM(FF,D : AbsolutelySimple := AbsolutelySimple);
        return HyperellipticCurveFromRosenhainInvariants(ee);
    end if;
    case p:
    when 2:
        require D in {5,8,12,13,17,24} : "Argument 2 must be D = 5, 8, 12, 13, 17, or 24.";
    when 3:
        require D in {5,8,12,13} : "Argument 2 must be D = 5, 8, 12, or 13.";
    else
        require D in {4,5,8,9,12,13,16,17,20,21} : "Argument 2 must be D = 5, 8, 12, or 13.";
    end case;
    JJ := RandomIgusaInvariantsWithRM(FF,D : AbsolutelySimple := AbsolutelySimple);
    return HyperellipticCurveFromIgusaInvariants(JJ);
end intrinsic;

intrinsic RandomGenus2CurveWithFrobeniusCharpoly(chi::RngUPolElt[RngInt] : 
    RealDiscriminant := 0) -> CrvHyp
    {Given chi = x^4 - s1*x^3 + s2*x^2 - s1*q*x + q^2, return a genus 2
    hyperelliptic curve with characteristic polynomial of Frobenius chi
    found by random search over invariants.  If a small RealDiscriminat
    is given, then a search over the Humbert of that discriminant is
    used to reduce the search space.}
    return RandomHyperellipticCurveWithFrobeniusCharpoly(chi :
        RealDiscriminant := RealDiscriminant);
end intrinsic;

intrinsic RandomHyperellipticCurveWithFrobeniusCharpoly(chi::RngUPolElt[RngInt] : RealDiscriminant := 0) -> CrvHyp
    {Given chi = x^4 - s1*x^3 + s2*x^2 - s1*q*x + q^2, return a genus 2
    hyperelliptic curve with characteristic polynomial of Frobenius chi
    found by random search over invariants.  If a small RealDiscriminat
    is given, then a search over the Humbert of that discriminant is
    used to reduce the search space.}

    require Degree(chi) eq 4 :
        "Argument 1 must be the charpoly of Frobenius of a genus 2 curve [not implemented for g > 2].";
    cc := Eltseq(chi); s1 := -cc[4]; s2 := cc[3]; q_square := cc[1];
    bool, p, r := IsPrimePower(q_square);
    n := r div 2; q := p^n;
    require bool and r mod 2 eq 0 and cc[2] eq -q*s1 and cc[5] eq 1 : 
        "Argument 1 must be the charpoly of Frobenius of a genus 2 curve.";
    // I should actually do some additional check since this assumes
    // that the only twists are quadratic.
    FF := FiniteField(q);
    x := Parent(chi).1;
    SmallField := q le 65536; // some arbitrary but explicit bound for naive point counting
    if s2 mod p ne 0 then
        if RealDiscriminant ne 0 then
            D := s1^2 - 4*s2 + 8*q;
            require D mod RealDiscriminant eq 0 and IsSquare(D div RealDiscriminant) :
                "Parameter \"RealDiscriminant\" must divide s1^2 - 4*s2 + 8*q with square cofactor.";;
        end if;
        xi := 1; yi := 1;
        while xi ne chi and yi ne chi do
            if RealDiscriminant ne 0 then
                C := RandomGenus2CurveWithRM(FF,RealDiscriminant);
            else
                C := RandomOrdinaryGenus2Curve(FF);
            end if;
            if SmallField and q+1-#C notin {-s1,s1} then continue; end if;
            xi := FrobeniusCharacteristicPolynomial(C);
            yi := Evaluate(xi,-x);
        end while;
    elif s1 mod p ne 0 then
        repeat
            C := RandomIntermediateGenus2Curve(FF);
            xi := FrobeniusCharacteristicPolynomial(C);
            yi := Evaluate(xi,-x);
        until xi eq chi or yi eq chi;
    else
        repeat
            C := RandomSupersingularGenus2Curve(FF);
            xi := FrobeniusCharacteristicPolynomial(C);
            yi := Evaluate(xi,-x);
        until xi eq chi or yi eq chi;
    end if;
    if xi eq chi then
        return C;
    else
        return QuadraticTwist(C);
    end if;
end intrinsic;

intrinsic RandomMaximalHyperellipticCurveWithFrobeniusCharpoly(chi::RngUPolElt[RngInt]) -> CrvHyp
    {}
    require Degree(chi) eq 4 and IsIrreducible(chi) :
        "Argument 1 must be the charpoly of Frobenius of a genus 2 curve with simple ordinary Jacobian.";
    cc := Eltseq(chi); s1 := -cc[4]; s2 := cc[3]; q := cc[1];
    bool, p, r := IsPrimePower(q); 
    n := r div 2; q := p^n;
    require bool and r mod 2 eq 0 and cc[2] eq -q*s1 and cc[5] eq 1 : 
        "Argument 1 must be the charpoly of Frobenius of a genus 2 curve with simple ordinary Jacobian.";
    // I should actually do some additional check since this assumes
    // that the only twists are quadratic.
    FF := FiniteField(q);
    x := Parent(chi).1;
    require s2 mod p ne 0 :
        "Argument 1 must be the charpoly of Frobenius of a genus 2 curve with simple ordinary Jacobian.";
    DAB := QuarticCMFieldInvariants(NumberField(chi));
    require DAB[1] ne 1 and DAB[2] ne 0 : 
        "Argument 1 must be the charpoly of Frobenius of a genus 2 curve with simple ordinary Jacobian.";
    JJ_invs := {@ @};
    while true do
        C := RandomOrdinaryGenus2Curve(FF);
        JJ := AbsoluteIgusaInvariants(C);
        if JJ in JJ_invs then continue; end if;
        xi := FrobeniusCharacteristicPolynomial(C);
        yi := Evaluate(xi,-x);
        if xi ne chi and yi ne chi then continue; end if;
        for s in [1..r] do
            Include(~JJ_invs,[ JJ[i]^p^s : i in [1..#JJ] ]);
        end for;
        print "#JJ_invs:", #JJ_invs;
        R, cond := EndomorphismRing(Jacobian(C));
        print "Endomorphism ring conductor:", cond;
        if cond eq [] then break; end if;
    end while;
    if xi eq chi then
        return C;
    else
        return QuadraticTwist(C);
    end if;
end intrinsic;

intrinsic RandomOrdinaryGenus2Curve(FF::FldFin) -> CrvHyp, SeqEnum
    {Constructs a random ordinary genus 2 curve (p rank 2) by choosing random
    ordinary Igusa invariants, returning the curve and its invariant sequence.}
    p := Characteristic(FF);
    case p:
    when 2:
        j1,j2,j4 := Explode([ Random(FF) : i in [1..3] ]);
        // The condition for a curve to be ordinary in
        // characteristic 2 is j1 != 0.
        while j1 eq 0 do
            j1 := Random(FF);
        end while;
        // JJ := [1,j2/j1,(j2/j1)^2,j4/j1,1/j1];
        // As a consequence the "absolute" invariants are:
        jj := [j1,j2,j2^2/j1,j4,j2^3/j1^2,j2*j4^2/j1,j2^4*j4/j1^3,j2^10/j1^7,j2^2*j4^3/j1^2,j4^5/j1];
    when 3:
        JJ := [ Random(FF) : i in [1..5] ];
        while JJ[1] eq 0 do
            JJ[1] := Random(FF);
        end while;
        while JJ[5] eq 0 do
            JJ[5] := Random(FF);
        end while;
        JJ[4] := JJ[1]*JJ[3] - JJ[2]^2;
        jj := IgusaToAbsoluteIgusaInvariants(JJ);
    else
        //print "Warning: ordinary condition not tested for characteristic", p;
        JJ := [ Random(FF) : i in [1..3] ];
        Append(~JJ,(JJ[1]*JJ[3] - JJ[2]^2)/4);
        Append(~JJ,0);
        while JJ[5] eq 0 do
            JJ[5] := Random(FF);
        end while;
        jj := IgusaToAbsoluteIgusaInvariants(JJ);
    end case;
    return HyperellipticCurveFromAbsoluteIgusaInvariants(jj), jj;
end intrinsic;

intrinsic RandomIntermediateGenus2Curve(FF::FldFin) -> CrvHyp, SeqEnum
    {Constructs a random intermediate genus 2 curve (p rank 1) by choosing
    random intermediate Igusa invariants, returning the curve and its
    invariant sequence.}
    p := Characteristic(FF);
    case p:
    when 2:
        j7 := 0; j8 := 0;
        while j7 eq 0 do
            j7 := Random(FF);
        end while;
        while j8 eq 0 do
            j8 := Random(FF);
        end while;
        // The "absolute" invariants are (with J2 = 0):
        jj := [0,0,0,0,0,0,j7,j8,j7^3/j8,j7^5/j8^2];
    when 3:
        j5 := 0; j8 := 0;
        while j5 eq 0 do
            j5 := Random(FF);
        end while;
        while j8 eq 0 do
            j8 := Random(FF);
        end while;
        uu := j5^3/j8;
        JJ := [ 0, uu, uu, -uu^2, uu^2/j5 ];
        jj := IgusaToAbsoluteIgusaInvariants(JJ);
    else
        require false: Sprintf("Not implemented (characteristic %o).",p);
    end case;
    return HyperellipticCurveFromAbsoluteIgusaInvariants(jj), jj;
end intrinsic;

intrinsic RandomSupersingularGenus2Curve(FF::FldFin) -> CrvHyp, SeqEnum
    {Constructs a random supersingular curve (p rank 0) by choosing
    random supersingular Igusa invariants, returning the curve and
    its invariant sequence.}
    p := Characteristic(FF);
    case p:
    when 2:
        j10 := 0;
        while j10 eq 0 do
            j10 := Random(FF);
        end while;
        // The "absolute" invariants are (with J2 = J4 = J6 = 0):
        // assert false; // J8 = ???
        jj := [0,0,0,0,0,0,0,0,0,j10];
    else
        require false: Sprintf("Not implemented (characteristic %o).",p);
    end case;
    return HyperellipticCurveFromAbsoluteIgusaInvariants(jj), jj;
end intrinsic;


//////////////////////////////////////////////////////////////////////////////
// Random curves via level 2 theta null constants
//////////////////////////////////////////////////////////////////////////////

intrinsic RandomLevel2ThetaNullGenus2Curve(FF::FldFin)  -> CrvHyp, SeqEnum, RngIntElt
    {If FF has characteristic 2, returns a random curve y^2 + v(x)y = v(x)u(x)
    defined by theta null constants [a1,a2,a3,e1,e3,e5] such that v(x) = (x-e1)(x-e3)(x-e5)
    and u(x) equals a1 (x-e3)(x-e5) + a2 (x-e1)(x-e5) + a3 (x-e1)(x-e3). Otherwise
    return a hyperelliptic curve defined by level 2 theta null points (a00:a01:a10:a11).}
    p := Characteristic(FF); r := Degree(FF); q := #FF;
    require q ge 4 : "Argument must be a finite field of at least 4 elements.";
    if p eq 2 then
        PF := PolynomialRing(FF); x := PF.1;
        while true do
            // e2 := e1 + 4*a1; e4 := e3 + 4*a2; e6 := e5 + 4*a3;
            e1 := Random(FF); e3 := Random(FF); e5 := Random(FF);
            a1 := Random(FF); a2 := Random(FF); a3 := Random(FF);
            v := (x-e1)*(x-e3)*(x-e5);
            u := a1*(x-e3)*(x-e5) + a2*(x-e1)*(x-e5) + a3*(x-e1)*(x-e3);
            bool, C := IsHyperellipticCurve([u*v,v]);
            if bool then return C; end if;
        end while;
    else
        while true do
            aa := [ Random(FF) : i in [1..4] ];
            a00, a01, a10, a11 := Explode(aa);
            good := not &or[
                a00*a01 + a10*a11 eq 0,
                a00*a10 + a01*a11 eq 0,
                a00*a11 + a01*a10 eq 0,
                a00*a01 - a10*a11 eq 0,
                a00*a10 - a01*a11 eq 0,
                a00*a11 - a01*a10 eq 0,
                a00^2 + a01^2 + a10^2 + a11^2 eq 0,
                a00^2 + a01^2 - a10^2 - a11^2 eq 0,
                a00^2 - a01^2 + a10^2 - a11^2 eq 0,
                a00^2 - a01^2 - a10^2 + a11^2 eq 0
                ];
            if good then
                ee := Level2ThetaNullPointToRosenhainInvariants(aa);
                return HyperellipticCurveFromRosenhainInvariants(ee);
            end if;
        end while;
    end if;
end intrinsic;

intrinsic RandomLevel2ThetaNullGenus2CurveWithFrobeniusCharpoly(
    FF::FldFin,chi::RngUPolElt[RngInt]) -> SeqEnum
    {}
    p := Characteristic(FF); r := Degree(FF); q := #FF;
    require not [p,r] eq [2,1] :
        "Argument 1 must be a finite field more than 2 elements.";
    require Coefficient(chi,0) eq q^2 : 
        "Argument 2 must be Frobenius charpoly of a curve over argument 1.";
    x := PolynomialRing(IntegerRing()).1;
    t1 := -Coefficient(chi,3); 
    while true do
        C := RandomLevel2ThetaNullGenus2Curve(FF);
        s1 := q + 1 - #C;
        if s1 eq -t1 then
            C := QuadraticTwist(C); s1 *:= -1;
        elif s1 ne t1 then
            continue;
        end if;
        s2 := (#BaseExtend(C,FiniteField(q^2))-q^2-1+s1^2) div 2;
        xi := x^4 - s1*x^3 + s2*x^2 - s1*q*x + q^2;
        if chi eq xi then return C; end if;
    end while;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Random curves via rosenhain invariants
//////////////////////////////////////////////////////////////////////////////

intrinsic RandomRosenhainGenus2Curve(FF::FldFin)  -> CrvHyp, SeqEnum, RngIntElt
    {Given a finite field of odd characteristic, returns a random
    hyperelliptic curve y^2 = x*(x-1)*(x-e1)*(x-e2)*(x-e3).}
    p := Characteristic(FF); r := Degree(FF); q := #FF;
    require p ne 2 : "Argument must be a finite field of odd characteristic.";
    require q ge 5 : "Argument must be a finite field of at least 5 elements.";
    while true do
        ee := [ Random(FF) : i in [1..3] ];
        if #(SequenceToSet(ee) join {0,1}) ne 5 then continue; end if;
        return HyperellipticCurveFromRosenhainInvariants(ee);
    end while;
end intrinsic;

intrinsic RandomRosenhainGenus2CurveWithFrobeniusCharpoly(
    FF::FldFin,chi::RngUPolElt[RngInt]) -> SeqEnum
    {}
    p := Characteristic(FF); r := Degree(FF); q := #FF;
    require p ne 2 : "Argument 1 must be a finite field of odd characteristic.";
    require q ge 5 : "Argument 1 must be a finite field of at least 5 elements.";
    require Coefficient(chi,0) eq q^2 : 
        "Argument 2 must be Frobenius charpoly of a curve over argument 1.";
    x := PolynomialRing(IntegerRing()).1;
    t1 := -Coefficient(chi,3); 
    while true do
        C := RandomRosenhainGenus2Curve(FF);
        s1 := q + 1 - #C;
        if s1 eq -t1 then
            C := QuadraticTwist(C); s1 *:= -1;
        elif s1 ne t1 then
            continue;
        end if;
        s2 := (#BaseExtend(C,FiniteField(q^2))-q^2-1+s1^2) div 2;
        xi := x^4 - s1*x^3 + s2*x^2 - s1*q*x + q^2;
        if chi eq xi then return C; end if;
    end while;
end intrinsic;
