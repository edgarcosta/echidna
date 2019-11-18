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

declare verbose FormalMorphism, 2;

intrinsic MorphismInterpolation(
    phi::MapSch, pnts::SeqEnum, degs::SeqEnum[RngIntElt] :
    Precision := 32,
    Indices := [],
    BasisDimension := 0,
    ExpandMorphism := false,
    MonomialSequences := [],
    MonomialReduction := true,
    LLLReduction := true,
    LLLScalar := 10^6,
    PolynomialTransformation := 0,
    PolynomialKernelTransformation := 0) -> SeqEnum
    {}
    // INPUT: (Since generalized considerably, but one possibility is):
    //   phi : E x E -> E with the domain in a product projective space
    //   pnts : a list of points on E x E
    //   degs : the degrees of polynomials which interpolate phi.
    //   Indices : the subset of codomain coordinate indices to be used.
    // OUTPUT: A basis of defining polynomials
    X := Domain(phi);
    Y := Codomain(phi);
    PX := AmbientSpace(X);
    AX := CoordinateRing(PX);
    PY := AmbientSpace(Y);
    wgts := Gradings(PX);
    require #pnts gt 0 : "Argument 2 must be nonempty.";
    require #wgts eq #degs :
        "Argument 3 must be a degree sequence of length equal to the number of gradings on argument 1.";
    P := pnts[1];
    case Type(P):
    when SeqEnum:
        K := Universe(P);
    when Pt, PtEll:
        K := Ring(Parent(P));
        require Parent(P) eq X(K) :
            "Argument 2 must be a sequence of coefficient sequences or points in the domain of argument 1.";
        pnts := [ Eltseq(P) : P in pnts ];
    else
        require false:
            "Argument 2 must be a sequence of coefficient sequences or points in the domain of argument 1.";
    end case;
    n := #pnts[1];
    K := Universe(pnts[1]);
    II := DefiningIdeal(X);
    if MonomialSequences cmpeq [] then
        mons_seqs := [];
        for i in [1..#degs] do
            jj := [ j : j in [1..#wgts[i]] | wgts[i][j] ne 0 ];
            ee := wgts[i][jj];
            AA := PolynomialRing(K,ee);
            m := hom< AA->AX | [ AX.j : j in jj ] >;
            mons := [ m(mon) : mon in MonomialsOfWeightedDegree(AA,degs[i]) ];
            if Type(PolynomialTransformation) ne RngIntElt then
                if Type(PolynomialTransformation) eq SeqEnum then
                    for f in PolynomialTransformation do
                        mons := [ f(mon) : mon in mons ];
                    end for;
                else
                    mons := [ PolynomialTransformation(mon) : mon in mons ];
                end if;
                mons := [ mon : mon in mons | mon ne 0 ];
            end if;
            if MonomialReduction then
                mons := [ mon : mon in mons | mon eq NormalForm(mon,II) ];
            end if;
            Append(~mons_seqs,[ mon : mon in mons ]);
        end for;
    else
        require #MonomialSequences eq #degs :
            "Parameter \"MonomialSequences\" must be a sequence (of sequences) of length equal to the number of given degrees.";
        for i in [1..#degs] do
            require &and [ Degree(f) eq degs[i] : f in MonomialSequences[i] ] :
                "Parameter \"MonomialSequences\" must be a sequence (of sequences of polynomials) of degrees given by Argument 3.";
        end for;
        mons_seqs := MonomialSequences;
    end if;
    vprint FormalMorphism : mons_seqs;
    mons := [ &*[ ms[i] : i in [1..#degs] ] : ms in CartesianProduct(mons_seqs) ];
    if MonomialReduction and MonomialSequences cmpeq [] then
        mons := [ mon : mon in mons | mon eq NormalForm(mon,II) ];
    end if;
    if Type(PolynomialTransformation) ne RngIntElt then
        if Type(PolynomialTransformation) eq SeqEnum then
            for f in PolynomialTransformation do
                mons := [ f(mon) : mon in mons ];
            end for;
        else
            mons := [ PolynomialTransformation(mon) : mon in mons ];
        end if;
        mons := [ mon : mon in mons | mon ne 0 ];
    end if;
    if not ExpandMorphism then
        if #Indices eq 0 then
            pols := [1..Length(Codomain(phi))];
        else
            pols := Indices;
        end if;
    elif #Indices eq 0 then
        pols := DefiningPolynomials(phi);
    elif ExtendedType(Indices) eq SeqEnum[RngIntElt] then
        pols := pols[Indices];
    else
        assert false;
    end if;
    vprint FormalMorphism : "#mons =", #mons;
    vprint FormalMorphism : "#pnts =", #pnts;
    vprint FormalMorphism : "#pols =", #pols;
    vprint FormalMorphism : "prec  =", Precision;
    vprint FormalMorphism, 2 : "Monomials:"; mons;
    F := BaseRing(K);
    U_mons := VectorSpace(F,#mons);
    if Type(PolynomialKernelTransformation) ne RngIntElt then
        if Type(PolynomialKernelTransformation) ne SeqEnum then
            red_maps := [ PolynomialKernelTransformation ];
        else
            red_maps := PolynomialKernelTransformation;
        end if;
        for r in red_maps do
            fncs_img := [ r(mon) : mon in mons ];
            mons_img := &join[ {@ mon : mon in Monomials(fnc) @} : fnc in fncs_img ];
            T := Matrix([ [ MonomialCoefficient(fnc_img,mon) : mon in mons_img ] : fnc_img in fncs_img ]);
            U_mons meet:= Kernel(T);
        end for;
        U_prod := ProductSpace(U_mons,#pols);
        printf "Reduced monomial space from dimension %o to %o\n", #mons, Rank(U_mons);
    else
        U_prod := VectorSpace(F,#mons*#pols);
    end if;
    Z_mons := U_mons;
    W_prod := U_prod;
    wgts := Gradings(PY);
    if #Indices gt 0 then
        wgts := [ w[Indices] : w in wgts ];
    end if;
    require &and[ SequenceToSet(w) subset {0,1} : w in wgts ] :
        "Algorithm implemented only for gradings with weights 0 and 1.";
    /* TODO: both the grad_lens and the cross products need to be changed for alternative weights. */
    grad_lens := [ &+w : w in wgts ];
    s := 1;
    N := &+[ Binomial(len,2) : len in grad_lens ];
    tyme := Cputime();
    prec := Precision;
    for P in pnts do
        T := RMatrixSpace(K,#mons*#pols,N)!0;
        eval_mons_P := [ Evaluate(m,P) : m in mons ];
        if ExpandMorphism then
            eval_phi := [ Evaluate(f,P) : f in pols ];
        else
            eval_phi := [ Evaluate(f,P) : f in DefiningPolynomials(phi) ];
            if #Indices gt 0 then
                eval_phi := eval_phi[Indices];
            end if;
        end if;
        if &and[ RelativePrecision(c) lt prec : c in eval_phi ]then
            continue;
        end if;
        val := Min([ Valuation(c) : c in eval_phi ]);
        if val gt 0 then
            eval_phi  := [ c div (K.1)^val : c in eval_phi ];
        end if;
        ij := 0;
        for grad in wgts do
            for i in [1..#pols-1] do
                if grad[i] eq 0 then continue; end if;
                for j in [i+1..#pols] do
                    if grad[j] eq 0 then continue; end if;
                    ij +:= 1;
                    for k in [1..#mons] do
                        T[(i-1)*#mons+k,ij] := eval_mons_P[k]*eval_phi[j];
                        T[(j-1)*#mons+k,ij] := -eval_mons_P[k]*eval_phi[i];
                    end for;
                end for;
            end for;
        end for;
        // print "Valuations:";
        // print Matrix([ [ Valuation(T[i,j]) : i in [1..#mons*#pols] ] : j in [1..N] ]);
        // print "Relative precision:";
        // print Matrix([ [ RelativePrecision(T[i,j]) : i in [1..#mons*#pols] ] : j in [1..N] ]);
        T_F := Matrix([ &cat[ [ Coefficient(T[i,j],k) : k in [0..prec] ] : j in [1..N] ] : i in [1..#mons*#pols] ]);
        S_F := Matrix([ [ Coefficient(eval_mons_P[i],k) : k in [0..prec] ] : i in [1..#mons] ]);
        W_prod meet:= Kernel(T_F); dim_W := Dimension(W_prod);
        Z_mons meet:= Kernel(S_F); dim_Z := Dimension(Z_mons);
        print "Dimension of sections:", dim_W;
        print "Dimension of kernel  :", dim_Z;
        assert dim_W ge dim_Z;
        printf "Point %2o: %o\n", s, Cputime(tyme); s +:= 1;
        if dim_W le Max(BasisDimension,0) then break; end if;
    end for;
    tyme := Cputime();
    if LLLReduction and Type(F) eq FldRat then
        M_W := LLL(LLLScalar * BasisMatrix(W_prod));
        B_W := [ 1/LLLScalar * M_W[i] : i in [1..Nrows(M_W)] ];
    else
        B_W := Basis(W_prod);
    end if;
    //print "HERE LLL 1:", Cputime(tyme);
    tyme := Cputime();
    if LLLReduction and Type(F) eq FldRat then
        M_Z := LLL(BasisMatrix(Z_mons));
        B_Z := [ M_Z[i] : i in [1..Nrows(M_Z)] ];
    else
        B_Z := Basis(Z_mons);
    end if;
    //print "HERE LLL 2:", Cputime(tyme);
    tyme := Cputime();
    PF := Universe(mons);
    proj_seq := [ hom< U_prod->U_mons | u :-> U_mons!Eltseq(u)[[(i-1)*#mons+1..i*#mons]] > : i in [1..#pols] ];
    cffs_to_poly := map< U_mons->PF | cffs :-> &+[ cffs[i] * mons[i] : i in [1..#mons] ] >;
    if Type(PolynomialTransformation) eq RngIntElt then
        function poly_to_cffs(f)
            assert f eq &+[ MonomialCoefficient(f,m)*m : m in mons ];
            return U_mons![ MonomialCoefficient(f,m) : m in mons ];
        end function;
    end if;
    prjs := [ [ pi(u) : pi in proj_seq ] : u in B_W ];
    pols := [ ];
    //print "HERE RED 1:", Cputime(tyme);
    for w in B_W do
        v_seq := [ pi(w) : pi in proj_seq ];
        if not &or[ v in Z_mons : v in v_seq ] then
            Append(~pols,[ cffs_to_poly(v) : v in v_seq ]);
        end if;
    end for;
    //print "HERE RED 2:", Cputime(tyme);
    pker := [ ];
    for v in B_Z do
        pol := cffs_to_poly(v);
        if pol eq 0 then continue; end if;
        Append(~pker,cffs_to_poly(v));
    end for;
    //print "HERE RED 3:", Cputime(tyme);
    if Type(PolynomialTransformation) eq RngIntElt then
        return pols, pker, W_prod, Z_mons, proj_seq, cffs_to_poly, poly_to_cffs;
    else
        return pols, pker, W_prod, Z_mons, proj_seq, cffs_to_poly, _;
    end if;
end intrinsic;

intrinsic MorphismInverseInterpolation(
    phi::MapSch, pnts::SeqEnum, degs::SeqEnum[RngIntElt] :
    Precision := 16,
    Indices := [],
    BasisDimension := 0,
    ExpandMorphism := false,
    MonomialSequences := [],
    MonomialReduction := true,
    LLLReduction := true,
    LLLScalar := 10^6,
    PolynomialTransformation := 0,
    PolynomialKernelTransformation := 0) -> SeqEnum
    {Assumes input morphism phi is an isomorphism, and computes
    polynomial representations for the inverse.}
    // INPUT: (Since generalized considerably, but one possibility is):
    //   phi : E x E -> E with the domain in a product projective space
    //   pnts : a list of points on E x E
    //   degs : the degrees of polynomials which interpolate phi.
    //   Indices : the subset of codomain coordinate indices to be used.
    // OUTPUT: A basis of defining polynomials for
    X := Domain(phi);
    Y := Codomain(phi);
    PX := AmbientSpace(X); lenX := Length(PX);
    PY := AmbientSpace(Y); lenY := Length(PY);
    AY := CoordinateRing(PY);
    wgtsY := Gradings(PY);
    require #pnts gt 0 : "Argument 2 must be nonempty.";
    require #wgtsY eq #degs :
        "Argument 3 must be a degree sequence of length equal to the number of gradings on argument 1.";
    P := pnts[1];
    case Type(P):
    when SeqEnum:
        K := Universe(P);
    when Pt, PtEll:
        K := Ring(Parent(P));
        require Parent(P) eq X(K) :
            "Argument 2 must be a sequence of coefficient sequences or points in the domain of argument 1.";
        pnts := [ Eltseq(P) : P in pnts ];
    else
        require false:
            "Argument 2 must be a sequence of coefficient sequences or points in the domain of argument 1.";
    end case;
    n := #pnts[1];
    K := Universe(pnts[1]);
    II := DefiningIdeal(Y);
    if MonomialSequences cmpeq [] then
        mons_seqs := [];
        for i in [1..#degs] do
            jj := [ j : j in [1..#wgtsY[i]] | wgtsY[i][j] ne 0 ];
            ee := wgtsY[i][jj];
            AA := PolynomialRing(K,ee);
            m := hom< AA->AY | [ AY.j : j in jj ] >;
            mons := [ m(mon) : mon in MonomialsOfWeightedDegree(AA,degs[i]) ];
            if Type(PolynomialTransformation) ne RngIntElt then
                if Type(PolynomialTransformation) eq SeqEnum then
                    for f in PolynomialTransformation do
                        mons := [ f(mon) : mon in mons ];
                    end for;
                else
                    mons := [ PolynomialTransformation(mon) : mon in mons ];
                end if;
                mons := [ mon : mon in mons | mon ne 0 ];
            end if;
            if MonomialReduction then
                mons := [ mon : mon in mons | mon eq NormalForm(mon,II) ];
            end if;
            Append(~mons_seqs,[ mon : mon in mons ]);
        end for;
    else
        require #MonomialSequences eq #degs :
            "Parameter \"MonomialSequences\" must be a sequence (of sequences) of length equal to the number of given degrees.";
        for i in [1..#degs] do
            require &and [ Degree(f) eq degs[i] : f in MonomialSequences[i] ] :
                "Parameter \"MonomialSequences\" must be a sequence (of sequences of polynomials) of degrees given by Argument 3.";
        end for;
        mons_seqs := MonomialSequences;
    end if;
    print mons_seqs;
    mons := [ &*[ ms[i] : i in [1..#degs] ] : ms in CartesianProduct(mons_seqs) ];
    if MonomialReduction and MonomialSequences cmpne [] then
        mons := [ mon : mon in mons | mon eq NormalForm(mon,II) ];
    end if;
    if Type(PolynomialTransformation) ne RngIntElt then
        if Type(PolynomialTransformation) eq SeqEnum then
            for f in PolynomialTransformation do
                mons := [ f(mon) : mon in mons ];
            end for;
        else
            mons := [ PolynomialTransformation(mon) : mon in mons ];
        end if;
        mons := [ mon : mon in mons | mon ne 0 ];
    end if;
    if not ExpandMorphism then
        if #Indices eq 0 then
            pols := [1..Length(Codomain(phi))];
        else
            pols := Indices;
        end if;
    elif #Indices eq 0 then
        pols := DefiningPolynomials(phi);
    elif ExtendedType(Indices) eq SeqEnum[RngIntElt] then
        pols := pols[Indices];
    else
        assert false;
    end if;
    print "#mons =", #mons;
    print "#pnts =", #pnts;
    print "#pols =", #pols;
    print "prec  =", Precision;
    F := BaseRing(K);
    U_mons := VectorSpace(F,#mons);
    if Type(PolynomialKernelTransformation) ne RngIntElt then
        if Type(PolynomialKernelTransformation) ne SeqEnum then
            red_maps := [ PolynomialKernelTransformation ];
        else
            red_maps := PolynomialKernelTransformation;
        end if;
        for r in red_maps do
            fncs_img := [ r(mon) : mon in mons ];
            mons_img := &join[ {@ mon : mon in Monomials(fnc) @} : fnc in fncs_img ];
            T := Matrix([ [ MonomialCoefficient(fnc_img,mon) : mon in mons_img ] : fnc_img in fncs_img ]);
            U_mons meet:= Kernel(T);
        end for;
        U_prod := ProductSpace(U_mons,lenX);
        printf "Reduced monomial space from dimension %o to %o\n", #mons, Rank(U_mons);
    else
        U_prod := VectorSpace(F,#mons*lenX);
    end if;
    Z_mons := U_mons;
    W_prod := U_prod;
    wgtsX := Gradings(PX);
    if #Indices gt 0 then
        wgtsX := [ w[Indices] : w in wgtsX ];
    end if;
    require &and[ SequenceToSet(w) subset {0,1} : w in wgtsX ] :
        "Algorithm implemented only for gradings with weights 0 and 1.";
    /* TODO: both the grad_lens and the cross products need to be changed for alternative weights. */
    grad_lens := [ &+w : w in wgtsX ];
    s := 1;
    N := &+[ Binomial(len,2) : len in grad_lens ];
    tyme := Cputime();
    prec := Precision;
    for P in pnts do
        // HERE T := RMatrixSpace(K,#mons*#pols,N)!0;
        T := RMatrixSpace(K,#mons*lenX,N)!0;
        if ExpandMorphism then
            eval_phi := [ Evaluate(f,P) : f in pols ];
        else
            eval_phi := [ Evaluate(f,P) : f in DefiningPolynomials(phi) ];
            if #Indices gt 0 then
                eval_phi := eval_phi[Indices];
            end if;
        end if;
        if &and[ RelativePrecision(c) lt prec : c in eval_phi ]then
            continue;
        end if;
        val := Min([ Valuation(c) : c in eval_phi ]);
        if val gt 0 then
            eval_phi  := [ c div (K.1)^val : c in eval_phi ];
        end if;
        eval_mons_Q := [ Evaluate(m,eval_phi) : m in mons ];
        ij := 0;
        for grad in wgtsX do
            for i in [1..lenX-1] do
                if grad[i] eq 0 then continue; end if;
                for j in [i+1..lenX] do
                    if grad[j] eq 0 then continue; end if;
                    ij +:= 1;
                    for k in [1..#mons] do
                        T[(i-1)*#mons+k,ij] := eval_mons_Q[k]*P[j];
                        T[(j-1)*#mons+k,ij] := -eval_mons_Q[k]*P[i];
                    end for;
                end for;
            end for;
        end for;
        T_F := Matrix([ &cat[ [ Coefficient(T[i,j],k) : k in [0..prec] ] : j in [1..N] ] : i in [1..#mons*lenX] ]);
        S_F := Matrix([ [ Coefficient(eval_mons_Q[i],k) : k in [0..prec] ] : i in [1..#mons] ]);
        W_prod meet:= Kernel(T_F); dim_W := Dimension(W_prod);
        Z_mons meet:= Kernel(S_F); dim_Z := Dimension(Z_mons);
        print "Dimension of sections:", dim_W;
        print "Dimension of kernel  :", dim_Z;
        assert dim_W ge dim_Z;
        printf "Point %2o: %o\n", s, Cputime(tyme); s +:= 1;
        if dim_W le Max(BasisDimension,0) then break; end if;
    end for;
    tyme := Cputime();
    if LLLReduction and Type(F) eq FldRat then
        M_W := LLL(LLLScalar * BasisMatrix(W_prod));
        B_W := [ 1/LLLScalar * M_W[i] : i in [1..Nrows(M_W)] ];
    else
        B_W := Basis(W_prod);
    end if;
    //print "HERE LLL 1:", Cputime(tyme);
    tyme := Cputime();
    if LLLReduction and Type(F) eq FldRat then
        M_Z := LLL(BasisMatrix(Z_mons));
        B_Z := [ M_Z[i] : i in [1..Nrows(M_Z)] ];
    else
        B_Z := Basis(Z_mons);
    end if;
    //print "HERE LLL 2:", Cputime(tyme);
    tyme := Cputime();
    PF := Universe(mons);
    proj_seq := [ hom< U_prod->U_mons | u :-> U_mons!Eltseq(u)[[(i-1)*#mons+1..i*#mons]] > : i in [1..lenX] ];
    cffs_to_poly := map< U_mons->PF | cffs :-> &+[ cffs[i] * mons[i] : i in [1..#mons] ] >;
    if Type(PolynomialTransformation) eq RngIntElt then
        function poly_to_cffs(f)
            assert f eq &+[ MonomialCoefficient(f,m)*m : m in mons ];
            return U_mons![ MonomialCoefficient(f,m) : m in mons ];
        end function;
    end if;
    prjs := [ [ pi(u) : pi in proj_seq ] : u in B_W ];
    pols := [ ];
    //print "HERE RED 1:", Cputime(tyme);
    for w in B_W do
        v_seq := [ pi(w) : pi in proj_seq ];
        if not &or[ v in Z_mons : v in v_seq ] then
            Append(~pols,[ cffs_to_poly(v) : v in v_seq ]);
        end if;
    end for;
    //print "HERE RED 2:", Cputime(tyme);
    pker := [ ];
    for v in B_Z do
        pol := cffs_to_poly(v);
        if pol eq 0 then continue; end if;
        Append(~pker,cffs_to_poly(v));
    end for;
    //print "HERE RED 3:", Cputime(tyme);
    if Type(PolynomialTransformation) eq RngIntElt then
        return pols, pker, W_prod, Z_mons, proj_seq, cffs_to_poly, poly_to_cffs;
    else
        return pols, pker, W_prod, Z_mons, proj_seq, cffs_to_poly, _;
    end if;
end intrinsic;

intrinsic MorphismPushThroughInterpolation(
    phi::MapSch, psi::MapSch, pnts::SeqEnum, degs::SeqEnum[RngIntElt] :
    Precision := 16,
    Indices := [],
    BasisDimension := 0,
    //ExpandMorphism := false,
    MonomialSequences := [],
    MonomialReduction := true,
    LLLReduction := true,
    LLLScalar := 10^6,
    PolynomialTransformation := 0,
    PolynomialKernelTransformation := 0) -> SeqEnum
    {Given phi:X->Y and psi:X->Z, determine a basis for a morphism
    rho:Z->Y such that phi = rho \circ psi (= psi*rho in Magma).}
    /*
    1. Apply the morphism psi to the points.
    2. Contruct the monomial sequence on Z.
    3. Pull out interpolation code to apply to this setting.
    */
    require Domain(phi) eq Domain(psi) :
        "The domains of argument 1 and 2 must be the same.";
    Y := Codomain(phi); Z := Codomain(psi);
    PY := AmbientSpace(Y); lenY := Length(PY);
    PZ := AmbientSpace(Z); lenZ := Length(PZ);
    AZ := CoordinateRing(PZ);
    wgtsZ := Gradings(PZ);
    require #pnts gt 0 : "Argument 2 must be nonempty.";
    require #wgtsZ eq #degs :
        "Argument 3 must be a degree sequence of length equal to the number of gradings on the codomain of argument 1.";
    P := pnts[1];
    case Type(P):
    when SeqEnum:
        K := Universe(P);
    when Pt, PtEll:
        K := Ring(Parent(P));
        require Parent(P) eq Z(K) :
            "Argument 2 must be a sequence of coefficient sequences or points in the domain of argument 1.";
        pnts := [ Eltseq(P) : P in pnts ];
    else
        require false:
            "Argument 2 must be a sequence of coefficient sequences or points in the domain of argument 1.";
    end case;
    n := #pnts[1];
    K := Universe(pnts[1]);
    II := DefiningIdeal(Z);
    if MonomialSequences cmpeq [] then
        mons_seqs := [];
        for i in [1..#degs] do
            jj := [ j : j in [1..#wgtsZ[i]] | wgtsZ[i][j] ne 0 ];
            ee := wgtsZ[i][jj];
            AA := PolynomialRing(K,ee);
            m := hom< AA->AZ | [ AZ.j : j in jj ] >;
            mons := [ m(mon) : mon in MonomialsOfWeightedDegree(AA,degs[i]) ];
            if Type(PolynomialTransformation) ne RngIntElt then
                if Type(PolynomialTransformation) eq SeqEnum then
                    for f in PolynomialTransformation do
                        mons := [ f(mon) : mon in mons ];
                    end for;
                else
                    mons := [ PolynomialTransformation(mon) : mon in mons ];
                end if;
                mons := [ mon : mon in mons | mon ne 0 ];
            end if;
            if MonomialReduction then
                mons := [ mon : mon in mons | mon eq NormalForm(mon,II) ];
            end if;
            Append(~mons_seqs,[ mon : mon in mons ]);
        end for;
    else
        require #MonomialSequences eq #degs :
            "Parameter \"MonomialSequences\" must be a sequence (of sequences) of length equal to the number of given degrees.";
        for i in [1..#degs] do
            require &and [ Degree(f) eq degs[i] : f in MonomialSequences[i] ] :
                "Parameter \"MonomialSequences\" must be a sequence (of sequences of polynomials) of degrees given by Argument 3.";
        end for;
        mons_seqs := MonomialSequences;
    end if;
    print mons_seqs;
    mons := [ &*[ ms[i] : i in [1..#degs] ] : ms in CartesianProduct(mons_seqs) ];
    if MonomialReduction and #MonomialSequences eq 0 then
        mons := [ mon : mon in mons | mon eq NormalForm(mon,II) ];
    end if;
    if Type(PolynomialTransformation) ne RngIntElt then
        if Type(PolynomialTransformation) eq SeqEnum then
            for f in PolynomialTransformation do
                mons := [ f(mon) : mon in mons ];
            end for;
        else
            mons := [ PolynomialTransformation(mon) : mon in mons ];
        end if;
        mons := [ mon : mon in mons | mon ne 0 ];
    end if;
    if #Indices eq 0 then
        pols_phi := DefiningPolynomials(phi);
        pols_psi := DefiningPolynomials(psi);
    elif ExtendedType(Indices) eq SeqEnum[RngIntElt] then
        pols_psi := pols_psi[Indices];
    else
        assert false;
    end if;
    print "#mons =", #mons;
    print "#pnts =", #pnts;
    print "#pols(psi) =", #pols_psi;
    print "prec  =", Precision;
    F := BaseRing(K);
    U_mons := VectorSpace(F,#mons);
    if Type(PolynomialKernelTransformation) ne RngIntElt then
        if Type(PolynomialKernelTransformation) ne SeqEnum then
            red_maps := [ PolynomialKernelTransformation ];
        else
            red_maps := PolynomialKernelTransformation;
        end if;
        for r in red_maps do
            fncs_img := [ r(mon) : mon in mons ];
            mons_img := &join[ {@ mon : mon in Monomials(fnc) @} : fnc in fncs_img ];
            T := Matrix([ [ MonomialCoefficient(fnc_img,mon) : mon in mons_img ] : fnc_img in fncs_img ]);
            U_mons meet:= Kernel(T);
        end for;
        U_prod := ProductSpace(U_mons,lenY);
        printf "Reduced monomial space from dimension %o to %o\n", #mons, Rank(U_mons);
    else
        U_prod := VectorSpace(F,#mons*lenY);
    end if;
    Z_mons := U_mons;
    W_prod := U_prod;
    wgtsY := Gradings(PY);
    if #Indices gt 0 then
        wgtsY := [ w[Indices] : w in wgtsY ];
    end if;
    require &and[ SequenceToSet(w) subset {0,1} : w in wgtsY ] :
        "Algorithm implemented only for gradings with weights 0 and 1.";
    /* TODO: both the grad_lens and the cross products need to be changed for alternative weights. */
    grad_lens := [ &+w : w in wgtsY ];
    s := 1;
    N := &+[ Binomial(len,2) : len in grad_lens ];
    tyme := Cputime();
    prec := Precision;
    pnts_phi := [ ];
    for P in pnts do
        // Interpolate w.r.t. (phi_p,Q), where P -> phi_P -> Q
        T := RMatrixSpace(K,#mons*lenY,N)!0;
        eval_phi_P := [ Evaluate(f,P) : f in pols_phi ];
        val_phi_P := Min([ Valuation(c) : c in eval_phi_P ]);
        if val_phi_P gt 0 then
            phi_P  := [ c div (K.1)^val_phi_P : c in eval_phi_P ];
        end if;
        psi_P := [ Evaluate(f,P) : f in pols_psi ];
        if &and[ RelativePrecision(c) lt prec : c in psi_P ] then continue; end if;
        val_psi := Min([ Valuation(c) : c in psi_P ]);
        if val_psi gt 0 then
            psi_P  := [ c div (K.1)^val_psi : c in psi_P ];
        end if;
        eval_mons_psi_P := [ Evaluate(m,psi_P) : m in mons ];
        ij := 0;
        for grad in wgtsY do
            for i in [1..lenY-1] do
                if grad[i] eq 0 then continue; end if;
                for j in [i+1..lenY] do
                    if grad[j] eq 0 then continue; end if;
                    ij +:= 1;
                    for k in [1..#mons] do
                        T[(i-1)*#mons+k,ij] := eval_mons_psi_P[k]*eval_phi_P[j];
                        T[(j-1)*#mons+k,ij] := -eval_mons_psi_P[k]*eval_phi_P[i];
                    end for;
                end for;
            end for;
        end for;
        T_F := Matrix([ &cat[ [ Coefficient(T[i,j],k) : k in [0..prec] ] : j in [1..N] ] : i in [1..#mons*lenY] ]);
        S_F := Matrix([ [ Coefficient(eval_mons_psi_P[i],k) : k in [0..prec] ] : i in [1..#mons] ]);
        W_prod meet:= Kernel(T_F); dim_W := Dimension(W_prod);
        Z_mons meet:= Kernel(S_F); dim_Z := Dimension(Z_mons);
        print "Dimension of sections:", dim_W;
        print "Dimension of kernel  :", dim_Z;
        assert dim_W ge dim_Z;
        printf "Point %2o: %o\n", s, Cputime(tyme); s +:= 1;
        if dim_W le Max(BasisDimension,0) then break; end if;
    end for;
    tyme := Cputime();
    if LLLReduction and Type(F) eq FldRat then
        M_W := LLL(LLLScalar * BasisMatrix(W_prod));
        B_W := [ 1/LLLScalar * M_W[i] : i in [1..Nrows(M_W)] ];
    else
        B_W := Basis(W_prod);
    end if;
    //print "HERE LLL 1:", Cputime(tyme);
    tyme := Cputime();
    if LLLReduction and Type(F) eq FldRat then
        M_Z := LLL(BasisMatrix(Z_mons));
        B_Z := [ M_Z[i] : i in [1..Nrows(M_Z)] ];
    else
        B_Z := Basis(Z_mons);
    end if;
    //print "HERE LLL 2:", Cputime(tyme);
    tyme := Cputime();
    PF := Universe(mons);
    proj_seq := [ hom< U_prod->U_mons | u :-> U_mons!Eltseq(u)[[(i-1)*#mons+1..i*#mons]] > : i in [1..lenY] ];
    cffs_to_poly := map< U_mons->PF | cffs :-> &+[ cffs[i] * mons[i] : i in [1..#mons] ] >;
    if Type(PolynomialTransformation) eq RngIntElt then
        function poly_to_cffs(f)
            assert f eq &+[ MonomialCoefficient(f,m)*m : m in mons ];
            return U_mons![ MonomialCoefficient(f,m) : m in mons ];
        end function;
    end if;
    prjs := [ [ pi(u) : pi in proj_seq ] : u in B_W ];
    pols := [ ];
    //print "HERE RED 1:", Cputime(tyme);
    for w in B_W do
        v_seq := [ pi(w) : pi in proj_seq ];
        //if not &or[ v in Z_mons : v in v_seq ] then
            Append(~pols,[ cffs_to_poly(v) : v in v_seq ]);
        //end if;
    end for;
    //print "HERE RED 2:", Cputime(tyme);
    pker := [ ];
    for v in B_Z do
        pol := cffs_to_poly(v);
        if pol eq 0 then continue; end if;
        Append(~pker,cffs_to_poly(v));
    end for;
    //print "HERE RED 3:", Cputime(tyme);
    if Type(PolynomialTransformation) eq RngIntElt then
        return pols, pker, W_prod, Z_mons, proj_seq, cffs_to_poly, poly_to_cffs;
    else
        return pols, pker, W_prod, Z_mons, proj_seq, cffs_to_poly, _;
    end if;
end intrinsic;
