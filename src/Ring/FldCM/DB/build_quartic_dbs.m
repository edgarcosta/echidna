//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildQuarticCMFieldDatabase(Dat::DBUser,D::RngIntElt :
    ConductorBound := 1,
    DiscriminantBound := 0,
    ClassNumberBound := 1024,
    Primitive := true)
    {}
    require Dat`DBIdentifier eq "Quartic CM fields" :
        "Argument 1 must be the database of quartic CM fields";
    require D gt 0 and not IsSquare(D) and D mod 4 in {0,1} and IsFundamental(D) : 
        "Argument 2 must be a real fundamental discriminant.";
    if DiscriminantBound eq 0 then
        DiscriminantBound := ConductorBound^2*D;
    end if;
    x := PolynomialRing(IntegerRing()).1;
    F := QuadraticField(D); r := F.1;
    t := -(D mod 4);
    w := (t + r)/2;
    N := (t^2 - D)/4;
    for b in [1..ConductorBound] do
        print "  Conductor b =", b;
        A1 :=  Ceiling(b*(Sqrt(D)-t)/2);
        A2 := Floor(Sqrt(DiscriminantBound+b^2*D/4)-b*t/2);
        printf "  Searching %o <= a <= %o\n", A1, A2;
        for a in [A1..A2] do
            if not IsSquarefree(GCD(a,b)) then continue; end if;
            A := 2*a + t*b;
            B := a^2 + a*b*t + b^2*N;
            assert B le DiscriminantBound;
            s := a + b*w;
            f := Polynomial([Norm(s),0,Trace(s),0,1]);
            if IsIrreducible(f) then
                K := NumberField(f);
                if Primitive and QuarticCMFieldType(K) eq [2,2] then continue; end if;
                printf "  (A,B) = (%4o,%6o): ", A, B;
                assert IsQuarticCMField(K);
                DAB := QuarticCMFieldInvariants(K);
                if not DAB in Dat then
                    h_invs := AbelianInvariants(ClassGroup(K));
                    h := &*h_invs;
                    if h le ClassNumberBound then
                        printf "Writing invariants: %o; ", DAB;
                        printf "h = &*%o = %o\n", h_invs, h;
                        Write(Dat,K);
                    else
                        printf "Omitting invariants: %o (h = %o)\n", DAB, h;
                    end if;
                else
                    h := QuarticCMFieldClassNumber(Dat,DAB);
                    printf "Invariants in database: %o (h = %o)\n", DAB, h;
                end if;
            end if;
        end for;
    end for;
end intrinsic;

intrinsic BuildQuarticCMFieldDatabaseFromCurves(
    Dat::DBUser,FF::FldFin : ClassNumberBound := 1024)
    {}
    require Dat`DBIdentifier eq "Quartic CM fields" :
        "Argument 1 must be the database of quartic CM fields";
    p := Characteristic(FF); q := #FF;
    S2 := [ x : x in FF ];
    for i in [1..q] do
        J2 := Random(S2); Exclude(~S2,J2);
        S4 := [ x : x in FF ];
        for j in [1..q] do
            printf "Iteration (i,j) = (%o,%o)\n", i, j;
            J4 := Random(S4); Exclude(~S4,J4);
            S6 := [ x : x in FF ];
            for k in [1..q] do
                J6 := Random(S6); Exclude(~S6,J6);
                J10 := FF!1;
                if p eq 2 and J2 eq 0 then
                    // J2 = 0, so 4*J8 = J2*J6 - J4^2 implies only J4 = 0  
                    // (J6,J8) <- (J4,J6)
                    JJ := [0,0,J4,J6,J10];
                elif p eq 2 then
                    // (J6,J8) <- (J4^2/J2,J6)
                    JJ := [J2,J4,J4^2/J2,J6,J10];
                else
                    JJ := [J2,J4,J6,(J2*J6-J4^2)/4,J10];
                end if;
                C := HyperellipticCurveFromIgusaInvariants(JJ);
                xi := FrobeniusCharacteristicPolynomial(C);
                if Coefficient(xi,2) mod p eq 0 and Coefficient(xi,3) mod p eq 0 then
                    continue;
                end if;
                if IsIrreducible(xi) then
                    K := NumberField(xi);
                    if QuarticCMFieldType(K) eq [2,2] then continue; end if;
                    DAB := QuarticCMFieldInvariants(K);
                    if not DAB in Dat then
                        h_invs := AbelianInvariants(ClassGroup(K));
                        h := &*h_invs;
                        if h le ClassNumberBound then
                            printf "Writing invariants: %o; ", DAB;
                            printf "h = &*%o = %o\n", h_invs, h;
                            Write(Dat,K);
                        else
                            printf "Omitting invariants: %o (h = %o)\n", DAB, h;
                        end if;
                    else
                        h := QuarticCMFieldClassNumber(Dat,DAB);
                        printf "Invariants in database: %o (h = %o)\n", DAB, h;
                    end if;
                end if;
            end for;
        end for;
    end for;
end intrinsic;

intrinsic BuildQuarticCMFieldDatabaseFromNormEquation(
    Dat::DBUser,D::RngIntElt,S::[RngIntElt] : ClassNumberBound := 1024)
    {}
    require Dat`DBIdentifier eq "Quartic CM fields" :
        "Argument 1 must be the database of quartic CM fields";
    X := PolynomialRing(RationalField()).1;
    require not IsSquare(D) and IsFundamental(D):
        "Argument 2 must be a fundamental discriminant.";
    F := QuadraticField(D);
    O := MaximalOrder(F);
    u := FundamentalUnit(O);
    if Norm(u) eq -1 then u := u^2; end if;
    v := u^-1;
    for B in S do
        // If the narrow class number if not 1 then IsSquarefree is too strong here...
        if not IsSquarefree(B) or not B gt 1 then continue; end if;
        if &or[ f[2] ge 4 : f in Factorization(B) ] then continue; end if;
        bool, S := NormEquation(O,B : Exact);
        if bool then
            if Norm(u) eq 1 and &and[ Norm(xi) lt 0 : xi in S ] then continue; end if;
            printf "Found solutions for (D,B) = (%o,%o)\n", D, B;
            Xis := {@ @}; 
            Polys := {@ @}; 
            for i in [1..#S] do
                xi := S[i]; assert Norm(xi) eq B;
                if Trace(xi) gt 0 then xi *:= -1; end if;
                if Abs(Trace(xi*u)) lt Abs(Trace(xi)) then
                    repeat
                        xi *:= u;
                        // print "minpol [u]:", MinimalPolynomial(xi);
                    until Abs(Trace(xi*u)) ge Abs(Trace(xi));
                elif Abs(Trace(xi*v)) lt Abs(Trace(xi)) then
                    repeat
                        xi *:= v;
                        // print "minpol [v]:", MinimalPolynomial(xi);
                    until Abs(Trace(xi*v)) ge Abs(Trace(xi));
                end if;
                yi := xi*u;
                if Abs(Trace(xi*v)) lt Abs(Trace(yi)) then
                    yi := xi*v;
                end if;
                if Norm(u) eq 1 then
                    solns := [ xi, yi ];
                else
                    solns := [ xi ];
                end if;
                for zi in solns do
                    f := Evaluate(MinimalPolynomial(zi),X^2);
                    if Degree(f) ne 2 then
                        Include(~Xis,xi);
                        Include(~Polys,f);
                    end if;
                end for;
            end for;
            T := PolynomialRing(F).1;
            for xi in Xis do
                print "  Polynomial:", Polys[Index(Xis,xi)];
                L := NumberField(T^2-xi);
		// The maximal order computation is easy for the relative field, 
		// but will become impossible for the absolute field if we don't
		// first compute the maximal order computation for the former.
		tyme := Cputime();
		OL := MaximalOrder(L);
                // print "    Relative maximal order time:", Cputime(tyme);
                K := AbsoluteField(L);
		tyme := Cputime();
                OK := MaximalOrder(K);
		// print "    Absolute maximal order time:", Cputime(tyme);
		tyme := Cputime();
		// The maximal order of the real subfield must be computed to 
		// determine the CM field invariants, so we must cache this 
		// subfield in such a way that its defining polynomial is of
		// a reasonable size.  Normally this is computed in the call 
		// to IsCMFIeld, so both are cached here.
		K`IsCMField := true;
		K`TotallyRealSubfield := sub< K | K!L!F.1 >;
		print "    Real subfield defining polynomial:", MinimalPolynomial(K`TotallyRealSubfield.1);
		DAB := QuarticCMFieldInvariants(K);
		// printf "    Invariants: %o (time %o)\n", DAB, Cputime(tyme);
                if QuarticCMFieldType(K) eq [2,2] then continue; end if;
                if not DAB in Dat then
                    h_invs := AbelianInvariants(ClassGroup(OK));
                    h := &*h_invs;
                    if h le ClassNumberBound then
                        printf "    Writing invariants: %o; ", DAB;
                        printf "h = &*%o = %o\n", h_invs, h;
                        Write(Dat,K);
                    else
                        printf "    Omitting invariants: %o (h = %o)\n", DAB, h;
                    end if;
                else
                    h := QuarticCMFieldClassNumber(Dat,DAB);
                    printf "    Invariants in database: %o (h = %o)\n", DAB, h;
                end if;
            end for;
        end if;
    end for;
end intrinsic;

