//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                    Gross-Zagier Orders                                   //
//        Copyright (C) 2014 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
EXAMPLE::
    magma: FF<Tx,Ty,Nx,Ny,Txy> := FunctionField(ZZ,5);
    magma: O := GrossZagierOrder(FF,Tx,Nx,Ty,Ny,Txy);
*/

intrinsic GrossZagierOrder(Rx::RngUPolRes,Ry::RngUPolRes,Txy::RngElt) -> AlgAss
    {Returns an associative algebra R<x,y> over a ring R defined by quadratic
    suborders Rx = R[x] and Ry = R[y] are of discriminant D1 and D2, respectively,
    and Tr(x*y) = Txy.  Then R[[x,y]], where [x,y] = xy - yx, is a quadratic suborder
    of discriminant D1*D2 - T^2, where T = Tr(x)*Tr(y) - 2*Tr(x*y).}
    R := BaseRing(Rx);
    require R cmpeq BaseRing(Ry) :
        "Arguments 1 and 2 must be defined over the same subring.";
    bool, Txy := IsCoercible(R,Txy);
    require bool : "Argument 3 must be coercible into the base ring of arguments 1 and 2.";
    fx := Modulus(Rx);
    require Degree(fx) eq 2 and IsMonic(fx) : "Argument 1 must be an integral quadratic ring.";
    fy := Modulus(Ry);
    require Degree(fy) eq 2 and IsMonic(fy) : "Argument 2 must be an integral quadratic ring.";
    Nx, Tx := Eltseq(fx);
    Ny, Ty := Eltseq(fy);
    return GrossZagierOrder(R,Tx,Nx,Ty,Ny,Txy);
end intrinsic;

intrinsic GrossZagierOrder(
    R::Rng,Tx::RngElt,Nx::RngElt,Ty::RngElt,Ny::RngElt,Txy::RngElt) -> AlgAss
    {Returns an associative algebra R<x,y> over a ring R defined
    by x^2 - Tx*x + Nx = y^2 - Ty*y + Ny = 0 and Tr(x*y) = Txy.
    If R[x] and R[y] are of discriminants D1 and D2, then and
    R[x*y-y*x] is a quadratic subring of discriminant D1*D2 - T^2,
    where T = Tx*Ty - 2*Txy.} 
    require &and[ IsCoercible(R,T) : T in [Tx,Ty,Nx,Ny,Txy] ] : "Arguments 2-6 must coerce in argument 1.";
    return AssociativeAlgebra< R, 4 |
        [
        [ [1,0,0,0], [   0,  1,  0,  0],       [  0,0, 1,0], [   0,   0,  0,   1] ],
        [ [0,1,0,0], [ -Nx, Tx,  0,  0],       [  0,0, 0,1], [   0,   0, -Nx, Tx] ],
        [ [0,0,1,0], [-Tx*Ty+Txy, Ty, Tx, -1], [-Ny,0,Ty,0], [-Tx*Ny,Ny, Txy,  0] ],
        [ [0,0,0,1], [-Ty*Nx,Txy,Nx,0],        [0,-Ny,0,Ty], [-Nx*Ny, 0,  0, Txy] ]
        ] >;
end intrinsic;

