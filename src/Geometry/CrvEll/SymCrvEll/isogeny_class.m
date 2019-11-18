//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                   ISOGENY CLASSES OF ELLIPTIC CURVES                     //
//        Copyright (C) 2013 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


/* Created David Kohel, November 2000 */

////////////////////////////////////////////////////////////////////////
//                       Attribute declarations                       //
////////////////////////////////////////////////////////////////////////

declare type SymCrvEll;

declare attributes SymCrvEll:
   EllipticCurve,
   Representatives;

////////////////////////////////////////////////////////////////////////
//                         Creation Function                          //
////////////////////////////////////////////////////////////////////////

intrinsic IsogenyClass(E::CrvEll) -> SymCrvEll
   {}
   G := New(SymCrvEll);
   G`EllipticCurve := E;
   return G;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                            Coercion                                //
////////////////////////////////////////////////////////////////////////

intrinsic IsCoercible(G::SymCrvEll,E::.) -> CrvEll
   {}
   if Type(E) eq CrvEll then
      if E in G then
         return true, E;
      end if;
   end if;
   return false;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                           Membership                               //
////////////////////////////////////////////////////////////////////////

intrinsic 'in'(E::., G::SymCrvEll) -> BoolElt
   {Returns true if E is in G.}
   require Type(E) eq CrvEll : "Argument 1 must be an elliptic curve";
   return true;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                            Printing                                //
////////////////////////////////////////////////////////////////////////

intrinsic Print(G::SymCrvEll,L::MonStgElt)
   {}
   E := G`EllipticCurve;
   printf "Isogeny class of %o", E;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                        Attribute Access                            //
////////////////////////////////////////////////////////////////////////

intrinsic InternalRepresentative(G::SymCrvEll) -> CrvEll
   {A representative curve of G.}
   require assigned G`EllipticCurve : "No representative is known";
   return G`EllipticCurve;
end intrinsic;
