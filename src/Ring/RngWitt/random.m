intrinsic Random(W::RngWittNew) -> RngWittNewElt
{}
  k := BaseRing(W);
  require IsFinite(k):
    "W must be definied over a finite ring";
  return W![Random(k) : x in [1..Length(W)]];
end intrinsic

intrinsic Random(W::RngWittNew, i::RngIntElt) -> RngWittNewElt
{}
  k := BaseRing(W);
  return W![Random(k, i) : x in [1..Length(W)]];
end intrinsic;

