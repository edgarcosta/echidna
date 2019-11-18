//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//         Copyright (C) 2008 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic Graph(A::AlgMatElt[RngInt]) -> GrphUnd
    {}
    n := Nrows(A);
    require n eq Ncols(A) and IsSymmetric(A) :
	"Argument must be a symmetric matrix.";
    return Graph(A,{@ i : i in [1..n] @});
end intrinsic;

intrinsic Graph(A::AlgMatElt[RngInt],V::SetIndx) -> GrphUnd
    {An undirected graph with symmetric adjacency matrix A.}
    n := #V;
    require n eq Nrows(A) and n eq Ncols(A) and IsSymmetric(A) :
	"Argument must be a symmetric matrix.";
    E := [ ]; 
    for i in [1..n] do
	Append(~E,<V[i],{ V[j] : j in [1..n] | A[i,j] ne 0 }>); 
    end for;
    return Graph< V | E >;
end intrinsic;
    
