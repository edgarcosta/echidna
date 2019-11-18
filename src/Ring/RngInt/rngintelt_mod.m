intrinsic BalancedMod(a::RngIntElt,n::RngIntElt) -> RngIntElt
   {}
   return r lt (n div 2) select r else r-n where r := a mod n;
end intrinsic;
