/*****************************************************************************
#  Copyright (C) 2005 David Kohel <kohel@maths.usyd.edu>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty
#    of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
#
#  See the GNU General Public License for more details; the full text
#  is available at:
#
#                  http://www.gnu.org/licenses/
#****************************************************************************/
	    
/*
intrinsic Valuation(f::RngUPolElt,p::RngUPolElt) -> RngIntElt
    {}
    require Parent(f) eq Parent(p): 
	"Arguments must share a common parent.";
    require IsIrreducible(p): "Argument 2 must be irreducible.";
    if f eq 0 then
	return Infinity();
    elif Degree(f) lt Degree(p) then
	return 0;
    end if;
    n := 0;
    f, rem := Quotrem(f,p);
    while rem eq 0 do
	n +:= 1;
	f, rem := Quotrem(f,p);
    end while;
    return n;
end intrinsic;
*/
