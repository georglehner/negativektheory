output := OutputTextFile( "output.txt" , true );


SearchAllGroupsForS := function(n)
local j, s, G;
for j in [1..Length(AllSmallGroups(n))] do
G := SmallGroup(n,j);
s := sOfGroup(G);
if s>0 then AppendTo(output, " & ",j," & ",StructureDescription(G)," & ",s," & \\","\\","\n"); fi;
od;
end;


#for k in Filtered([128..128], i -> GcdInt(i,4)=4) do

#AppendTo(output, "\\","hline \n","$n = ", k,"$ & Index  &  Structure  & $s(G)$ & Quotients & Subgroups \\","\\ \n","\\","hline \n");
#SearchAllGroupsForS(k);
#od;


#Next we want to compute a list of the building blocks of groups with s>0. For that we have
#to create a list ElementGrps

ElementGrps := [ [ 16, 9 ], [ 20, 1 ], [ 24, 4 ], [ 32, 20 ], [ 32, 44 ], [ 40, 4 ], [ 48, 28 ],
  [ 52, 1 ], [ 56, 3 ], [ 64, 54 ], [ 64, 154 ], [ 64, 191 ], [ 64, 259 ], [ 68, 1 ],
  [ 80, 33 ], [ 80, 40 ], [ 84, 5 ], [ 88, 3 ], [ 96, 31 ], [ 96, 119 ], [ 96, 190 ],
  [ 96, 191 ], [ 96, 217 ], [ 104, 4 ], [ 116, 1 ], [ 120, 5 ], [ 120, 8 ], [ 128, 66 ],
  [ 128, 72 ], [ 128, 74 ], [ 128, 82 ], [ 128, 90 ], [ 128, 137 ], [ 128, 143 ],
  [ 128, 152 ], [ 128, 163 ], [ 128, 634 ], [ 128, 637 ], [ 128, 879 ], [ 128, 912 ],
  [ 128, 927 ], [ 128, 946 ], [ 128, 954 ], [ 128, 971 ], [ 128, 996 ], [ 128, 2025 ],
  [ 128, 2149 ], [ 128, 2318 ], [ 132, 3 ], [ 136, 3 ], [ 136, 4 ], [ 144, 15 ],
  [ 144, 43 ], [ 144, 59 ], [ 144, 118 ], [ 144, 138 ], [ 148, 1 ], [ 152, 3 ],
  [ 156, 1 ], [ 160, 31 ], [ 160, 80 ], [ 160, 133 ], [ 160, 225 ], [ 164, 1 ],
  [ 168, 7 ], [ 168, 12 ], [ 168, 15 ] ];
#Order < 180

SearchAllBuildingBlocksForS := function(n)
local j, s, G;
for j in [1..Length(AllSmallGroups(n))] do
G := SmallGroup(n,j);
s := sOfGroup(G);
if s>0 then 
     if not ForAny( NormalSubgroups(G), N ->  IdSmallGroup( FactorGroup( G, N ) ) in ElementGrps ) then Add(ElementGrps, [n,j]); fi;
     fi;          
od;
end;

for k in Filtered([152..180], i -> GcdInt(i,4)=4) do
SearchAllBuildingBlocksForS(k);
od;

Print( ElementGrps );