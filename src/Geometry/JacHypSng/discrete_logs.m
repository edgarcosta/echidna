////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  HYPERELLIPTIC DISCRETE LOGARITHMS                 //
//                             David Kohel                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic SmoothRelations(
    J::PicHypSng,~Divs::SeqEnum,~Rels::SeqEnum,
    deg::RngIntElt,N::RngIntElt)
    {}
    n := #Divs;
    g := Dimension(J);
    DivsP1 := {@ D[1] : D in Divs @};
    assert #DivsP1 eq n;
    r := 16; b := Max(8,(4*g) div r);
    for i in [1..N] do
	rel := [ <Random([1..n]),Random([-b..b])> : j in [1..r] ];
	pp := &+[ t[2]*J!Divs[t[1]] : t in rel ];
	ax, bx := Explode(pp`Divisor);
	fac := Factorization(ax);
	degs := [ Degree(ff[1]) : ff in fac ];
	maxd := Max(degs);
	if maxd gt deg and maxd le deg+1 then
	    vprintf Relations, 2 :
		"%6o: Reject [max: %2o] %o\n", i, Max(degs), degs;
	end if;
	if maxd le deg then
	    vprintf Relations : "%6o: %o\n", i, degs;
	    for ff in fac do
		j := Index(DivsP1,ff[1]);
		if j eq 0 then
		    Include(~DivsP1,ff[1]);
		    Append(~Divs,[ff[1],bx mod ff[1]]);
		    Append(~rel,<n+1,-ff[2]>);
		    n +:= 1; 
		elif bx mod ff[1] eq Divs[j][2] then
		    Append(~rel,<j,-ff[2]>);
		else
		    assert -bx mod ff[1] eq Divs[j][2];
		    Append(~rel,<j,ff[2]>);
		end if;
	    end for;
	    if &+[ t[2]*J!Divs[t[1]] : t in rel ] ne J!0 then
		print "&+ =", &+[ t[2]*J!Divs[t[1]] : t in rel ];
		print "relation =", rel;
		print "divisors =", [ Divs[t[1]] : t in rel ];
		assert false;
	    end if;
	    Append(~Rels,rel);
	end if;
    end for;
end intrinsic;
