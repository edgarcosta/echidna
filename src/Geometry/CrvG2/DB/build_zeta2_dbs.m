//////////////////////////////////////////////////////////////////////////////
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

import "genus2_curves.m": IsValidFrobeniusCharpoly;

function CMFieldTypeToGaloisGroup(cmfield_type)
    case cmfield_type:
    when [2,2]:
        return "C2 x C2";
    when [4]:
        return "C4";
    when [8]:
        return "D4";
    end case;
end function;

function Frobcharpolycoeffs(C,q : Traces := {})
    s1 := q+1-#C;
    if #Traces ne 0 and s1 notin Traces then return 0, 0, 0; end if;
    if q lt 1024 then
        s2 := (#BaseExtend(C,FiniteField(q^2))-q^2-1+s1^2) div 2;
    else
        n1 := #Jacobian(C); // = (1 + q^2) - s1*(1 + q) + s2;
        s2 := (n1 - (1 + q^2) + s1*(1 + q));
    end if;
    return s1, s2, q;
end function;

intrinsic BuildGenus2ZetaFunctionsDatabase(Dat::DBUser,p::RngIntElt,r::RngIntElt,k::RngIntElt : 
    ClassNumberBound := 0,
    ExactClassNumber := 0,
    RealDiscriminant := 0,
    SimpleJacobian := true,
    Level2ThetaNull := false,
    Rosenhain := false,
    ComplementIgusaLIX := true,
    MinimalDefiningField := false,
    MaximalCurveFailures := Infinity(),
    FrobeniusCharacteristicPolynomial := 0,
    DisplayIsogenyClass := false)
    {}
    require Dat`DBIdentifier eq "Genus 2 zeta functions" : 
        "Argument 1 must be the database of genus 2 zeta functions.";
    if MaximalCurveFailures lt Infinity() then
        max_tot := k + MaximalCurveFailures;
    else
        max_tot := 8*k; // Impose some bound for finite runtime.
    end if;
    h0 := ExactClassNumber eq 0;
    DBCM := QuarticCMFieldDatabase();
    DBIX := IgusaLIXDatabase();
    FF := FiniteField(p,r);
    q := p^r;
    if not Level2ThetaNull then
        HumbertDiscs := p eq 2 select {5,8,12,13,17} else {5,8,12,13};
    else
        HumbertDiscs := p eq 2
            select {5,8,9,12,13,17,24,28,40,44,56,60}
            else {4,5,8,9,12,13,16,17,20,24,28,32,40,44,48,52,56,60,68};
    end if;
    case Type(FrobeniusCharacteristicPolynomial):
    when RngIntElt:
        xis := {}; assert FrobeniusCharacteristicPolynomial eq 0;
    when RngUPolElt:
        xis := {FrobeniusCharacteristicPolynomial};
    when SetEnum:
        xis := FrobeniusCharacteristicPolynomial;
    when SeqEnum:
        xis := SequenceToSet(FrobeniusCharacteristicPolynomial);
    else
        require false: "Parameter \"FrobeniusCharacteristicPolynomial\" must be a polynomial or set or sequence thereof.";
    end case;
    for xi in xis do
        bool, pi, ri := IsValidFrobeniusCharpoly(xi,2);
        require bool and pi eq p and ri eq r :
            "Parameter \"FrobeniusCharacteristicPolynomial\" must specify Frobenius characteristic polynomials of the correct characteristic and degree:", xi;
    end for;
    num := 0;
    tot := 0;
    incr := true;
    DBG2 := Genus2CurvesDatabase();
    FrobeniusTraces := { IntegerRing() | u*Coefficient(xi,3) : u in [1,-1], xi in xis };
    while num lt k and tot lt max_tot do
        tot +:= 1;
        if incr then
            incr := false;
            printf "num = %o/%o [tot = %o < %o]\n", num, k, tot, max_tot;
        end if;
        if RealDiscriminant eq 0 then
            if Level2ThetaNull then
                C := RandomLevel2ThetaNullGenus2Curve(FF);
            elif Rosenhain then
                C := RandomRosenhainGenus2Curve(FF);
            else
                C := RandomOrdinaryGenus2Curve(FF);
            end if;
        elif RealDiscriminant in HumbertDiscs then
            C := RandomGenus2CurveWithRM(FF,RealDiscriminant :
                Level2ThetaNull := Level2ThetaNull, Rosenhain := Rosenhain);
        else
            require false :
                "Parameter \"RealDiscriminant\" must be in " * Sprint(HumbertDiscs) * ".";
        end if;
        s1, s2 := Frobcharpolycoeffs(C,q : Traces := FrobeniusTraces);
        // Check that the curve has simple Jacobian:
        if s1 eq 0 then continue; end if;
        // Normalize s1:
        if s1 lt 0 then s1 *:= -1; C := QuadraticTwist(C); end if;
        // Check that the curve is ordinary:
        if s2 mod p eq 0 then continue; end if;
        chi := Polynomial([q^2,-q*s1,s2,-s1,1]);
        // Check that given FrobeniusCharacteristicPolynomial(s) include chi:
        if #xis gt 0 and chi notin xis then
            continue;
        end if;
        JJ := IgusaToNormalizedIgusaInvariants(IgusaInvariants(C));
        s := LCM([ Degree(MinimalPolynomial(ii)) : ii in JJ ]);
        print "  chi:", chi;
        if s ne r then
            printf "  Invariants defined over subfield of degree %o.\n", s; incr := true; continue;
        end if;
        if IsIrreducible(chi) and not (SimpleJacobian and s1 eq 0) then
            K := NumberField(chi);
            DAB := QuarticCMFieldInvariants(K);
            if DAB in DBCM then
                h := QuarticCMFieldClassNumber(DBCM,DAB);
            else
                h := ClassNumber(K);
            end if;
            if ClassNumberBound ne 0 and ClassNumberBound lt h then
                printf "  Class number: %o (> %o)\n", h, ClassNumberBound;
                incr := true;
                continue;
            end if;
            in_DBIX := DAB in DBIX;
            if not ComplementIgusaLIX and in_DBIX then
                print "  Class number:", h;
                print "  CM invariants:", DAB;
                print "  DBIX: true (continuing)";
                incr := true;
                continue;
            end if;
            if C in Dat then
                print "  Class number:", h;
                print "  CM invariants:", DAB;
                print "  DBIX:", in_DBIX;
                print "  DBZ2: true (continuing)";
                incr := true;
                continue;
            end if;
            if MinimalDefiningField then
                if DAB in DBCM then
                    if h eq 1 then
                        e := 1;
                    else
                        exps := QuarticCMFieldClassInvariants(DBCM,DAB);
                        e := exps[#exps];
                    end if;
                else
                    e := Exponent(ClassGroup(K));
                end if;
                if false then // e mod r ne 0 then
                    /*
                    Counterexample:
                    Over the field F_{2^8} there exists a Frobenius
                    characteristic polynomial:
                       chi: x^4 - 19*x^3 + 457*x^2 - 4864*x + 65536
                    The class group is Z/2Z x Z/20Z, of exponent 20,
                    but the exponent is not divisible by r = 8 and
                    there exists no Frobenius characteristic polynomial
                    of degree 4.
                    */
                    // If there exists a curve with maximal endomorphism ring
                    // defined over a smaller field then continue:
                    printf "  Class group of exponent %o (!= 0 mod %o) defined over smaller field\n", e, r;
                    incr := true; continue;
                end if;
            end if;
            // On the other hand, we need the invariants to not lie in a subfield:
            deg := #{ [ ji^p^k : ji in JJ ] : k in [0..r-1] };
            if deg lt r then
                printf "  Igusa invariants defined over smaller field of degree %o < %o\n", e, r; continue;
            end if;
            cmfield_type := QuarticCMFieldType(K);
            if SimpleJacobian and cmfield_type eq [2,2] then
                continue;
            end if;
            if DisplayIsogenyClass or GetVerbose("Genus2ZetaFunctions") gt 1 then
                print "  JJ:", JJ;
            end if;
            print "  Class number:", h;
            print "  CM invariants:", DAB;
            print "  Galois group:", CMFieldTypeToGaloisGroup(cmfield_type);
            print "  chi in DBZ2:", chi in Dat;
            print "  chi in DBIX:", DAB in DBIX;
	    print "  chi in DBCM:", DAB in DBCM;
            cond := FrobeniusVerschiebungConductorAbelianInvariants(chi);
            print "  Conductor of Z[pi,nu]:", cond;
            if RealDiscriminant ne 0 then
                K<pi> := NumberField(chi);
                OK := MaximalOrder(K);
                F := TotallyRealSubfield(K);
                OF := MaximalOrder(F);
                O := sub< OK | [ pi, p^r/pi ] cat [ K!F!w : w in Basis(OF) ] >;
                cond := ConductorAbelianInvariants(O);
                print "  Conductor of O_F[pi,nu]:", cond;
            end if;
        else
            print "  Skipping split Jacobian."; incr := true; continue;
        end if;
        IndentPush();
        if cond eq [] then
            // "Overwrite" actually appends...
            OK := MaximalOrder(NumberField(chi));
            Write(DBG2,chi,<C,OK> : Overwrite);
        else
            // "Overwrite" actually appends...
            Write(Dat,chi,C : Overwrite);
        end if;
        if DisplayIsogenyClass then
            DisplayGenus2CurvesNumbers(DBG2,chi);
        end if;
        IndentPop();
        IndentPop();
        if DAB notin DBCM then
            Write(DBCM,K);
        end if;
        num +:= 1; incr := true;
    end while;
end intrinsic;

intrinsic BuildGenus2ZetaFunctionsDatabase(Dat::DBUser,p::RngIntElt,r::RngIntElt : 
    ClassNumberBound := 0,
    ExactClassNumber := 0,
    SimpleJacobian := true,
    ComplementIgusaLIX := true,
    MinimalDefiningField := false,
    FrobeniusCharacteristicPolynomial := 0,
    DisplayIsogenyClass := false)
    {}
    require Dat`DBIdentifier eq "Genus 2 zeta functions" : 
        "Argument 1 must be the database of genus 2 zeta functions.";
    h0 := ExactClassNumber eq 0;
    num := 0;
    DBCM := QuarticCMFieldDatabase();
    DBIX := IgusaLIXDatabase();
    FF := FiniteField(p,r);
    q := p^r;
    case Type(FrobeniusCharacteristicPolynomial):
    when RngIntElt:
        xis := {}; assert FrobeniusCharacteristicPolynomial eq 0;
    when RngUPolElt:
        xis := {FrobeniusCharacteristicPolynomial};
    when SetEnum:
        xis := FrobeniusCharacteristicPolynomial;
    when SeqEnum:
        xis := SequenceToSet(FrobeniusCharacteristicPolynomial);
    end case;
    DBG2 := Genus2CurvesDatabase();
    FrobeniusTraces := { u*Coefficient(xi,3) : u in [1,-1], xi in xis };
    i := Random([1..q]); j := Random([1..q]);
    S3 := [ x : x in FF ];
    S1 := S3[[i..q]] cat S3[[1..i-1]];
    S2 := S3[[j..q]] cat S3[[1..j-1]];
    for x1 in S1, x2 in S2, x3 in S3 do
        ss := [x1,x2,x3];
        if p eq 2 then
            sym1, sym2, sym3 := Explode(ss);
            if sym3 eq 0 then continue; end if;
            j2 := sym2^2/sym3;
            JJ := [ 1, j2, j2^2, sym1^2 + j2^3*(j2 + 1), sym3 ];
        else
            j1, j2, j3 := Explode(ss);
            if j1 eq 0 then continue; end if;
            u1 := 1/j1;
            JJ := [1,j2*u1,j3*u1,(j3-j2^2*u1)*u1/4,u1];
        end if;
        C := HyperellipticCurveFromIgusaInvariants(JJ);
        s1, s2 := Frobcharpolycoeffs(C,q : Traces := FrobeniusTraces);
        // Check that the curve has simple Jacobian:
        if s1 eq 0 then continue; end if;
        // Normalize s1:
        if s1 lt 0 then s1 *:= -1; C := QuadraticTwist(C); end if;
        // Check that the curve is ordinary:
        if s2 mod p eq 0 then continue; end if;
        chi := Polynomial([q^2,-q*s1,s2,-s1,1]);
        // Check that given FrobeniusCharacteristicPolynomial(s) include chi:
        if #xis gt 0 and chi notin xis then
            continue;
        end if;
        s := LCM([ Degree(MinimalPolynomial(ii)) : ii in JJ ]);
        print "  chi:", chi;
        if s ne r then
            printf "  Invariants defined over subfield of degree %o.\n", s; continue;
        end if;
        if IsIrreducible(chi) and not (SimpleJacobian and s1 eq 0) then
            K := NumberField(chi);
            DAB := QuarticCMFieldInvariants(K);
            if DAB in DBCM then
                h := QuarticCMFieldClassNumber(DBCM,DAB);
            else
                h := ClassNumber(K);
            end if;
            if ClassNumberBound ne 0 and ClassNumberBound lt h then
                printf "  Class number: %o (> %o)\n", h, ClassNumberBound;
                continue;
            end if;
            if not ComplementIgusaLIX and DAB in DBIX then
                print "  Class number:", h;
                print "  CM invariants:", DAB;
                print "  DBIX: true (continuing)";
                continue;
            end if;
            if C in Dat then
                print "  Class number:", h;
                print "  CM invariants:", DAB;
                print "  DBZ2: true (continuing)";
                incr := true;
                continue;
            end if;
            if MinimalDefiningField then
                if DAB in DBCM then
                    if h eq 1 then
                        e := 1;
                    else
                        exps := QuarticCMFieldClassInvariants(DBCM,DAB);
                        e := exps[#exps];
                    end if;
                else
                    e := Exponent(ClassGroup(K));
                end if;
                if false then // e mod r ne 0 then
                    /*
                    Counterexample:
                    Over the field F_{2^8} there exists a Frobenius
                    characteristic polynomial:
                       chi: x^4 - 19*x^3 + 457*x^2 - 4864*x + 65536
                    The class group is Z/2Z x Z/20Z, of exponent 20,
                    but the exponent is not divisible by r = 8 and
                    there exists no Frobenius characteristic polynomial
                    of degree 4. 
                    */
                    // If there exists a curve with maximal endomorphism ring
                    // defined over a smaller field then continue:
                    printf "  Class group of exponent %o (!= 0 mod %o) defined over smaller field\n", e, r; continue;
                end if;
            end if;
            // On the other hand, we need the invariants to not lie in a subfield:
            deg := #{ [ ji^p^k : ji in JJ ] : k in [0..r-1] };
            if deg lt r then
                printf "  Igusa invariants defined over smaller field of degree %o < %o\n", e, r; continue;
            end if;
            cmfield_type := QuarticCMFieldType(K);
            if SimpleJacobian and cmfield_type eq [2,2] then
                continue;
            end if;
            if DisplayIsogenyClass then
                print "  JJ:", JJ;
            end if;
            print "  Class number:", h;
            print "  CM invariants:", DAB;
            print "  Galois group:", CMFieldTypeToGaloisGroup(cmfield_type);
            print "  chi in DBZ2:", chi in Dat;
            print "  chi in DBIX:", DAB in DBIX;
            print "  chi in DBCM:", DAB in DBCM;
            cond := FrobeniusVerschiebungConductorAbelianInvariants(chi);
            print "  Conductor of Z[pi,nu]:", cond;
        else
            print "  Skipping split Jacobian."; continue;
        end if;
        IndentPush();
        if cond eq [] then
            // "Overwrite" actually appends...
            Write(DBG2,chi,C : Overwrite);
        else
            // "Overwrite" actually appends...
            Write(Dat,chi,C : Overwrite);
        end if;
        if DisplayIsogenyClass then
            DBG2 := Genus2CurvesDatabase();
            DisplayGenus2CurvesNumbers(DBG2,chi);
        end if;
        IndentPop();
        if DAB notin DBCM then
            Write(DBCM,K);
        end if;
    end for;
end intrinsic;

