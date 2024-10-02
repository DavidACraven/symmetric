intrinsic IsCluster(X::SeqEnum[SeqEnum]) -> BoolElt
{Checks whether all partitions in X have the same hook lengths.}
require &and[IsPartition(i):i in X]: "Not all elements of X are partitions";
return #{HookLengths(i):i in X} eq 1;
end intrinsic;

intrinsic IsCluster(X::SetEnum[SeqEnum]) -> BoolElt
{Checks whether all partitions in X have the same hook lengths.}
require &and[IsPartition(i):i in X]: "Not all elements of X are partitions";
return #{HookLengths(i):i in X} eq 1;
end intrinsic;

intrinsic IsPeriodicCluster(X::SeqEnum[SeqEnum[RngIntElt]]) -> BoolElt,SetEnum
{Returns whether X is a periodic cluster of partitions, and the set of integers p for which X forms a periodic cluster of period p. If the cluster is not periodic, it will return false.}
require &and[IsPartition(i):i in X]: "Not all elements of X are partitions";
if #{HookLengths(i):i in X} ne 1 then return false,_; end if;
// Now we look at the periods.

// Maximum period:
maxp:=Minimum([#i:i in X])-1;
allperiods:={};
for per in [1..maxp] do
  Remainders:={[i[j]:j in [per+1..#i]]:i in X};
  if not IsCluster(Remainders) then continue per; end if;
  InfParts:={InfinityPartition([i[j]:j in [1..per]],per):i in X};
  if(IsCluster(InfParts)) then Include(~allperiods,per); end if;
end for;
if #allperiods eq 0 then return false,_; end if;
return true,allperiods;
end intrinsic;

intrinsic PeriodicClusterGenerator(X::SetEnum[SeqEnum[RngIntElt]],p:RngIntElt) -> SetEnum
{Given a periodic cluster X with period p, returns the smallest periodic cluster in the same sequence as X, with the condition that the conjugate partitions of the elements in the cluster are distinct from the cluster. (The period must be specified as clusters may have more than one period.)}
bool,periods:=IsPeriodicCluster(X);
require bool and p in periods: "Is not a periodic cluster with period p";
nn:=Minimum([i[p]-i[p+1]:i in X]);
Y:={[i[j]-nn:j in [1..p]] cat [i[j]:j in [p+1..#i]]:i in X};
if #(Y join {ConjugatePartition(i):i in Y}) eq 2*#Y then
  return Y;
else
  return {[i[j]+1:j in [1..p]] cat [i[j]:j in [p+1..#i]]:i in Y};
end if;
end intrinsic;


intrinsic PeriodicClusterExtension(X::SetEnum[SeqEnum[RngIntElt]],p::RngIntElt,n::RngIntElt) -> SetEnum
{Given a periodic cluster X with period p, returns the periodic cluster obtained by extending this cluster by n. Note that while n may be negative, it cannot reduce the size of the cluster below that of the generator of the periodic cluster.}
bool,periods:=IsPeriodicCluster(X);
require bool and p in periods: "Is not a periodic cluster with period p";
XGen:=PeriodicClusterGenerator(X,p);
xext:=(&+Rep(XGen)-&+Rep(X)) div p;
require n ge xext: "extension is below generator threshold";
return {[i[j]+n:j in [1..p]] cat [i[j]:j in [p+1..#i]]:i in X};
end intrinsic;



intrinsic DetermineClustersOfPartitions(n::RngIntElt) -> SeqEnum,SeqEnum
{Determines all clusters among the partitions of of size n. The function returns the clusters of partitions, and also the hook lengths of each cluster. The function DetermineLargeClustersOfPartitions should be used if one wants just the clusters of order at least 3, as it is faster.}
requirege n,1;
HL:=[];
ClusteredPartitions:=[];
X:=[n];
for iii in [1..NumberOfPartitions(n)] do
  if(X lt ConjugatePartition(X)) then NextPartition(~X,n); continue iii; end if;
  H:=HookLengths(X);
  nn:=Position(HL,H);
  if(nn ne 0) then
    ClusteredPartitions[nn] join:={X,ConjugatePartition(X)};
  else
    Append(~ClusteredPartitions,{X,ConjugatePartition(X)});
    Append(~HL,H);
  end if;
  NextPartition(~X,n);
end for;
return ClusteredPartitions,HL;
end intrinsic;


intrinsic DetermineLargeClustersOfPartitions(n::RngIntElt) -> SeqEnum
{Determines all clusters of size at least 3 among the partitions of of size n. The function returns only the clusters of partitions. This method is faster than DetermineClustersOfPartitions.}

requirege n,1;
num:=NumberOfPartitions(n);
P:=[n];
CharDegs:=[];
Parts:=[];
g:=Sym(n)!1;
for i in [1..num] do
  if(P lt ConjugatePartition(P)) then NextPartition(~P,n); continue i; end if;
  t:=SymmetricCharacterValue(P,g);
  nn:=Position(CharDegs,t);
  if(nn eq 0) then
    Append(~CharDegs,t);
    Append(~Parts,{P,ConjugatePartition(P)});
    delete t;
  else
    Parts[nn] join:={P,ConjugatePartition(P)};
  end if;
  NextPartition(~P,n);
end for;
delete CharDegs; "Stage 1 done";
ClusteredPartitions:=[];

for ii in Parts do
  if #ii le 2 then continue ii; end if;
  Seqii:=SetToSequence(ii);
  HL:=[HookLengths(X):X in Seqii];
  HL2:=SequenceToSet(HL);
  for i in HL2 do
    if(Multiplicity(HL,i) le 2) then continue i; end if;
    Append(~ClusteredPartitions,{Seqii[j]:j in [1..#ii]|HL[j] eq i});
  end for;
end for;

return ClusteredPartitions;
end intrinsic;

function CheckForCluster(B,R)
FoundClusters:=[];
for i1 in R do
  for i2 in R do
    if(HookLengths(B[1] cat i1) eq HookLengths(B[2] cat i2)) then
      for i3 in R do
        if(HookLengths(B[1] cat i1) eq HookLengths(B[3] cat i3)) then
          for i4 in R do
            if(HookLengths(B[1] cat i1) eq HookLengths(B[4] cat i4)) then
              Append(~FoundClusters,{B[1] cat i1,B[2] cat i2,B[3] cat i3,B[4] cat i4});
            end if;
          end for;
        end if;
      end for;
    end if;
  end for;
end for;

return FoundClusters;

end function;


intrinsic MatchInfinityPartitionsToClusters(X::SeqEnum[SetEnum[InfPart]],R::SeqEnum[SetEnum[SeqEnum]]) -> SeqEnum[SetEnum[SeqEnum]]
{Given a collection X of clusters of infinity-partitions and a set R of clusters of partitions, finds all periodic clusters with infinity-partition from X and remainder from R. At the moment, all clusters in X and R should have cardinality 4 for this to work, as it is optimized to find periodic clusters of cardinality 8 (when taken with their conjugates).}
require &and[IsCluster(i):i in X]: "The infinity-partitions are not all in clusters";
require &and[IsCluster(i):i in R]: "The remainder partitions are not all in clusters";

ThePeriod:=Rep(Rep(X))`Period;
FoundClusters:=[];
for infp in X do
  for rem in R do
    nn:=Maximum([i[1]:i in rem]);
    A:=[[j+nn:j in i`UnderlyingPartition]:i in infp]; // These are big enough. Now need to make them all the same size
    MaxSize:=Maximum([&+i:i in A]);
    B:=[[j+(MaxSize-&+i) div ThePeriod:j in i]:i in A];
    for i in rem do for j in rem do
      if(HookLengths(B[1] cat i) eq HookLengths(B[2] cat j)) then FoundClusters cat:=CheckForCluster(B,rem); continue rem; end if;
    end for; end for;
  end for;
end for;

SmallestClusters:=[PeriodicClusterGenerator(i,ThePeriod):i in FoundClusters];

return SmallestClusters;

end intrinsic;


intrinsic EnvelopingPartition(pa::SeqEnum[RngIntElt]) -> SeqEnum
{ Returns the enveloping partition corresponding to the partition pa. If pa and pa2 have the same hook lengths then so do their enveloping partitions. Furthermore, they form a periodic cluster. This is the central construction in the 2008 paper of Craven. }
require IsPartition(pa): "Input must be a partition";
require pa[#pa] ge 1: "Input cannot have trailing zeros";

n:=#pa+pa[1];
pa2:=[n:i in [1..n]] cat pa;
for i in [1..#pa] do pa2[i]+:=pa[i]; end for;
pat:=ConjugatePartition(pa);
for i in [1..#pat] do pa2[#pa+i]-:=pat[#pat+1-i]; end for;
return pa2;

end intrinsic;
