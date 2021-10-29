$ontext
    File name: pmodel.gms
    Author: Mohammed Alfaki, December, 2010.
    GAMS model for the P-formulation.
$offtext

#===============================================================================
# Declare options
#===============================================================================
options optcr=1.e-3, limrow=0, limcol=0, reslim=3600;

#===============================================================================
# Declare sets
#===============================================================================
sets lt(i), l(i);
lt(i) = i(i)-s(i); l(i) = i(i)-s(i)-t(i);
alias (l,h);

# Is there a path between (s,l)
parameter p(i,j);
#===============================================================================
# Compute p(s,i) using the Breadth-first-search (BFS)
#===============================================================================
alias (i,ii,iii), (j,jj), (l,h);
scalar u,path,n,mn;
set openlst(i);
set closedlst(i);
parameter val(i);
loop((ii,jj)$(ord(ii)<=ord(jj)),
  n = 1;
  path = 0;
  val(i) = +inf;
  openlst(i) = no;
  closedlst(i) = no;
  openlst(i)$(ord(i) eq ord(ii)) = yes;
  val(i)$(ord(i) eq ord(ii)) = n;
  while((card(openlst)>0 and path eq 0),
    mn = smin(openlst(i), val(i));
    loop(i$openlst(i),
      if((mn eq val(i)),
        u = ord(i);
        val(i) = +inf;
      );
    );
    openlst(i)$(ord(i) eq u) = no;
    if((ord(jj) eq u),
      path = 1;
    else
      closedlst(i)$(ord(i) eq u) = yes;
      loop((iii,j)$(ord(iii) eq u and a(iii,j)>0 and 
                                         not closedlst(j) and not openlst(j)),
        n = n+1;
        val(j) = n;
        openlst(i)$(ord(i) eq ord(j)) = yes;
      );
    );
  );
  p(ii,jj) = path;
);

#===============================================================================
# Declare variables/bounds
#===============================================================================
variables cost, w(i,k), v(k,i,j);
positive variable f(i,j);

w.lo(l,k) = smin(s$(p(s,l)>0),q(s,k));
w.up(l,k) = smax(s$(p(s,l)>0),q(s,k)); 
f.up(i,j) = min(bu(i),bu(j))*a(i,j);

#===============================================================================
# Declare constraints
#===============================================================================
equations obj, sflowcaplb(s), sflowcapub(s), tflowcaplb(t), ptflowcapub(i),
          flowmassblnc(i), qualblnc(i,k), qualub(t,k), flowweight(k,i,j);

#===============================================================================
# Define constraints
#===============================================================================
#-----------------------------Objective function--------------------------------
obj.. cost =e= sum((i,j)$(a(i,j)>0), c(i,j)*f(i,j));
#-------------------------Raw material availabilities---------------------------
sflowcaplb(s)$(bl(s)>0).. sum(j$(a(s,j)>0), f(s,j)) =g= bl(s);
sflowcapub(s)$(bu(s)<+inf).. sum(j$(a(s,j)>0), f(s,j)) =l= bu(s);
#----------------Pool capacities and product demand restrictions----------------
tflowcaplb(t)$(bl(t)>0).. sum(j$(a(j,t)>0), f(j,t)) =g= bl(t);
ptflowcapub(lt)$(bu(lt)<+inf).. sum(j$(a(j,lt)>0), f(j,lt)) =l= bu(lt);
#------------------------Flow mass balance around pools-------------------------
flowmassblnc(l).. sum(j$(a(j,l)>0), f(j,l)) - sum(j$(a(l,j)>0), f(l,j)) =e= 0;
#-------------------Quality specifications balances around pools----------------
qualblnc(l,k).. sum(s$(a(s,l)>0), q(s,k)*f(s,l)) + sum(h$(a(h,l)>0), v(k,h,l)) 
                                           - sum(j$(a(l,j)>0), v(k,l,j)) =e= 0;
#------------------------Product quality specifications-------------------------
qualub(t,k)$(abs(q(t,k))<+inf).. sum(s$(a(s,t)>0), q(s,k)*f(s,t)) + 
          sum(l$(a(l,t)>0), v(k,l,t)) - q(t,k)*sum(j$(a(j,t)>0), f(j,t)) =l= 0;
#----------------------------------Weighted flow--------------------------------
flowweight(k,l,j)$(a(l,j)>0).. v(k,l,j) =e= w(l,k)*f(l,j);

#===============================================================================
# Solve the model
#===============================================================================
option nlp = baron;
model pmodel /all/;
pmodel.solprint = 2;
pmodel.workspace = 1500;
solve pmodel minimizing cost using nlp;
#============================Print solution information=========================
scalar nlts;
nlts = 0;
loop((k,l,j)$(a(l,j)>0),
  nlts = nlts + 1;
);
scalars ae, re;
ae = abs(pmodel.objest - pmodel.objval);
re = ae/abs(pmodel.objest);
file line;
put_utility line 'msg' / '#####' ' Solution Summary #####';
line.nd = 6;
line.nw = 18;
put_utility line 'msg' / pmodel.objval ' ' pmodel.objest ' ' pmodel.resusd ' ' 
re ' ' ae;
line.nd = 0;
put_utility line 'msg' / pmodel.solvestat ' ' pmodel.nodusd ' ' 
(pmodel.numvar-1) ' ' nlts ' ' (pmodel.numequ-nlts-1) ' ' nlts;
option f:6:0:2; display f.l;
option w:6:0:2; display w.l;
#========================================END====================================