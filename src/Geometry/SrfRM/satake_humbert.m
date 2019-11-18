//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        Copyright (C) 2015 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic Level1SatakeHumbertRationalPoints(FF::FldFin,D::RngIntElt) -> SetIndx
    {}
     if #FF gt 10^6 then print "Warning: Argument 1 may be too big."; end if;
    require D gt 0 and D mod 4 in {0,1} and D le 21 :
        "Argument 2 must be a positive discriminant bounded by 21.";
    P<x> := PolynomialRing(FF);
    H := Level1SatakeHumbertPolynomial(FF,D);
    pnts := {@ @};
    // First assume s2 and s3 are nonzero, and set u1 = s2/s3.
    // Then we set a0 = s2^3/s3^2 = u1^2*s2 = u1^3*s3, b0 = u1^5*s5
    // and c0 = u1^5*s6. This gives (s2:s3:s5:s6) = (a0:a0:b0:c0). 
    for a0 in FF do
        if a0 eq 0 then continue; end if;
        for b0 in FF do
            h := H([a0,a0,b0,x]);
            if h eq 0 then 
                for c0 in FF do
                    Include(~pnts,[a0,a0,b0,c0]);
                end for;
            else
                for r in Roots(h) do
                    c0 := r[1];
                    Include(~pnts,[a0,a0,b0,c0]);
                end for;
            end if;
        end for;
    end for;
    // Next assume s2 = 0, and s3 and s5 are nonzero. Set u1 = s5/s3^2,
    // such that a0 = s5^3/s3^5 = s3*u1^3 and a0^2 = s5*u1^5.  
    // This gives (s2:s3:s5:s6) = (0:a0:a0^2:b0) where b0 = s6*u1^6. 
    for a0 in FF do
        if a0 eq 0 then continue; end if;
        h := H([0,a0,a0^2,x]);
        if h eq 0 then
            for b0 in FF do
                Include(~pnts,[0,a0,a0^2,b0]);
            end for;
        else
            for r in Roots(h) do
                b0 := r[1];
                Include(~pnts,[0,a0,a0^2,b0]);
            end for;
        end if;
    end for;
    // Next assume s3 = 0, and s2 and s5 are nonzero. Set u1 = s2^2/s5,
    // such that a0 = s2^5/s5^2 = s2*u1^2 and a0^2 = s5*u1^5.  
    // This gives (s2:s3:s5:s6) = (a0:0,a0^2:b0) where b0 = s6*u1^6. 
    for a0 in FF do
        if a0 eq 0 then continue; end if;
        h := H([a0,0,a0^2,x]);
        if h eq 0 then
            for b0 in FF do
                Include(~pnts,[a0,0,a0^2,b0]);
            end for;
        else
            for r in Roots(h) do
                b0 := r[1];
                Include(~pnts,[a0,0,a0^2,b0]);
            end for;
        end if;
    end for;
    // Now we consider s2 = s3 = 0. Both s5 and s6 are nonzero and 
    // we can normalize (s2:s3:s5:s6) = (0:0:s5^6/s6^5:s5^6/s6^5).
    h := H([0,0,x,x]);
    if h ne 0 then 
    for r in Roots(h) do
        a0 := r[1];
        Include(~pnts,[0,0,a0,a0]);
    end for;
    end if;
    // The two cases s2 = s5 = 0 and s3 = s5 = 0 remain. These give
    // (s2:s3:s5:s6) = (0:s3^2/s6:0:s3^2/s6), using u1 = (s3/s6)^1/3, 
    h := H([0,x,0,x]);
    if h ne 0 then 
    for r in Roots(h) do
        a0 := r[1];
        if a0 ne 0 then
            Include(~pnts,[0,a0,0,a0]);
        end if;
    end for;
    end if;
    // (s2:s3:s5:s6) = (s2^3/s6:0:0:s2^3/s6), using u1 = (s2/s6)^1/2.
    h := H([x,0,0,x]);
    if h ne 0 then 
    for r in Roots(h) do
        a0 := r[1];
        if a0 ne 0 then
            Include(~pnts,[a0,0,0,a0]);
        end if;
    end for;
    end if;
    // Remark: Both of the latter points are singular.
    return pnts;
end intrinsic;
