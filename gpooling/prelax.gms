$ontext
    File name: prelax.gms
    Author: Mohammed Alfaki, December, 2010.
    GAMS model for the P-relaxation.
$offtext

#===============================================================================
# Declare options
#===============================================================================
options optcr=1.e-9, limrow=0, limcol=0, iterlim=1.e9, reslim=1.e9;

#===============================================================================
# Declare sets
#===============================================================================
sets lt(i), l(i);
lt(i) = i(i)-s(i); l(i) = i(i)-s(i)-t(i);
alias (l,h);

# Is there a path between (s,l)
parameter p(s,i);
#===============================================================================
# Compute p(s,i) using the Breadth-first-search (BFS)
#===============================================================================
alias(i,i1,i2);
scalars u, path, n, mn;
set openlst(i);
set closedlst(i);
parameter val(i);
loop((s,i1)$(ord(i1)>card(s) and ord(i1) le card(i)-card(t)),
  n = 1;
  path = 0;
  val(i) = +inf;
  openlst(i) = no;
  closedlst(i) = no;
  openlst(i)$(ord(i) eq ord(s)) = yes;
  val(i)$(ord(i) eq ord(s)) = n;
  while((card(openlst)>0 and path eq 0),
    mn = smin(openlst(i), val(i));
    loop(i$openlst(i),
      if((mn eq val(i)),
        u = ord(i);
        val(i) = +inf;
      );
    );
    openlst(i)$(ord(i) eq u) = no;
    if((ord(i1) eq u),
      path = 1;
    else
      closedlst(i)$(ord(i) eq u) = yes;
      loop((i2,j)$(ord(i2) eq u and a(i2,j)>0 and
                                         not closedlst(j) and not openlst(j)),
        n = n+1;
        val(j) = n;
        openlst(i)$(ord(i) eq ord(j)) = yes;
      );
    );
  );
  p(s,i1) = path;
);

#===============================================================================
# Declare variables/bounds
#===============================================================================
variables cost, w(i,k), v(k,i,j);
positive variable f(i,j);

w.up(l,k) = smax(s$(p(s,l)>0),q(s,k)); 
w.lo(l,k) = smin(s$(p(s,l)>0),q(s,k));
f.up(i,j) = min(bu(i),bu(j))*a(i,j);

#===============================================================================
# Declare constraints
#===============================================================================
equations obj, sflowcaplb(s), sflowcapub(s), tflowcaplb(t), ptflowcapub(i),
          flowmassblnc(i), qualub(t,k), qualblnc(i,k), vexlb(k,i,j), 
          vexub(k,i,j), cavlb(k,i,j), cavub(k,i,j);

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
#--------------Convex/concave envelopes of v(k,l,j) = w(l,k)*f(l,j)-------------
vexlb(k,l,j)$(a(l,j)>0).. v(k,l,j) - w.lo(l,k)*f(l,j) -
                                    w(l,k)*f.lo(l,j) =g= - w.lo(l,k)*f.lo(l,j); 
vexub(k,l,j)$(a(l,j)>0).. v(k,l,j) - w.up(l,k)*f(l,j) -
                                    w(l,k)*f.up(l,j) =g= - w.up(l,k)*f.up(l,j);
cavlb(k,l,j)$(a(l,j)>0).. v(k,l,j) - w.lo(l,k)*f(l,j) -
                                    w(l,k)*f.up(l,j) =l= - w.lo(l,k)*f.up(l,j);
cavub(k,l,j)$(a(l,j)>0).. v(k,l,j) - w.up(l,k)*f(l,j) -
                                    w(l,k)*f.lo(l,j) =l= - w.up(l,k)*f.lo(l,j);

#===============================================================================
# Solve the model
#===============================================================================
option lp = cplex;
model prelax /all/;
prelax.solprint = 2;
solve prelax minimizing cost using lp;
#============================Print solution information=========================
scalars ae, re;
ae = abs(prelax.objval - prelax.objval);
re = ae/abs(prelax.objval);
file line; 
put_utility line 'msg' / '#####' ' Solution Summary #####';
line.nd = 6;
line.nw = 18;
put_utility line 'msg' / prelax.objval ' ' prelax.objval ' ' prelax.resusd ' ' 
re ' ' ae;
line.nd = 0;
put_utility line 'msg' / prelax.solvestat ' ' prelax.iterusd ' ' 
(prelax.numvar-1) ' ' 0 ' ' (prelax.numequ-1) ' ' 0;
option f:6:0:2; display f.l;
option w:6:0:2; display w.l;
#========================================END====================================