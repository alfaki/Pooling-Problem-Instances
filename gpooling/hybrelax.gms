$ontext
    File name: hybrelax.gms
    Author: Mohammed Alfaki, December, 2010.
    GAMS model for the HYB-formulation.
$offtext

#===============================================================================
# Declare options
#===============================================================================
options optcr=1.e-9, limrow=0, limcol=0, iterlim=1.e9, reslim=1.e9;

#===============================================================================
# Declare sets
#===============================================================================
sets lt(i), l(i), l1(i), i1(i), l2(i);
lt(i) = i(i)-s(i); l(i) = i(i)-s(i)-t(i);
alias (l,h), (l1,h1), (l2,h2), (i1,j1);
l1(i) = i(i)-s(i)-t(i);
loop(l,
     l1(h)$(a(l,h)>0) = no;
);
l2(i) = l(i)-l1(i); i1(i) = i(i)-l1(i);

# Is there a path between (s,l)
parameter p(s,i);
#===============================================================================
# Compute p(s,i) using the Breadth-first-search (BFS)
#===============================================================================
alias(i,i3,i2);
scalars u, path, n, mn;
set openlst(i);
set closedlst(i);
parameter val(i);
loop((s,i3)$(ord(i3)>card(s) and ord(i3) le card(i)-card(t)),
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
    if((ord(i3) eq u),
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
  p(s,i3) = path;
);

#===============================================================================
# Declare variables/bounds
#===============================================================================
variable cost, w(i,k), v(k,i,j);
positive variables f(i,j), y(s,i), x(s,i,j);

f.up(i,j1) = min(bu(i),bu(j1))*a(i,j1);
y.up(s,l1) = a(s,l1);
w.lo(l2,k) = smin(s$(p(s,l2)>0),q(s,k));
w.up(l2,k) = smax(s$(p(s,l2)>0),q(s,k));
x.up(s,l1,j) = min(bu(s),bu(l1),bu(j))*a(s,l1)*a(l1,j);

#===============================================================================
# Declare constraints
#===============================================================================
equations obj, sflowcaplb(s), sflowcapub(s), pflowcapub(i), tflowcaplb(t), 
          tflowcapub(i), flowpathblnc(i), flowmassblnc(i), qualblnc(i,k), 
          propblnc(i), qualub(t,k), rlt1(i,j), rlt2(s,i), vexlby(s,i,j), 
          vexuby(s,i,j), cavlby(s,i,j), cavuby(s,i,j), vexlbw(k,i,j), 
          vexubw(k,i,j), cavlbw(k,i,j), cavubw(k,i,j);

#===============================================================================
# Define constraints
#===============================================================================
#-----------------------------Objective function--------------------------------
obj.. cost =e= sum((s,j1)$(a(s,j1)>0), c(s,j1)*f(s,j1)) + 
                        sum((s,l1,j)$(a(s,l1)*a(l1,j)>0), c(s,l1)*x(s,l1,j)) + 
                                          sum((l,j)$(a(l,j)>0), c(l,j)*f(l,j));
#-------------------------Raw material availabilities---------------------------
sflowcaplb(s)$(bl(s)>0).. sum(j1$(a(s,j1)>0), f(s,j1)) + 
                           sum((l1,j)$(a(s,l1)*a(l1,j)>0),x(s,l1,j)) =g= bl(s);
sflowcapub(s)$(bu(s)<+inf).. sum(j1$(a(s,j1)>0), f(s,j1)) + 
                           sum((l1,j)$(a(s,l1)*a(l1,j)>0),x(s,l1,j)) =l= bu(s);
#----------------Pool capacities and product demand restrictions----------------
pflowcapub(l)$(bu(l)<+inf).. sum(j$(a(l,j)>0), f(l,j)) =l= bu(l);
tflowcaplb(t)$(bl(t)>0).. sum(j$(a(j,t)>0), f(j,t)) =g= bl(t);
tflowcapub(t)$(bu(t)<+inf).. sum(j$(a(j,t)>0), f(j,t)) =l= bu(t);
#-----------------------Commodity flow balance around pools---------------------
flowpathblnc(l1).. 
 sum(j$(a(l1,j)>0), f(l1,j)) - sum((s,j)$(a(s,l1)*a(l1,j)>0), x(s,l1,j)) =e= 0;
#------------------------Flow mass balance around pools-------------------------
flowmassblnc(l2).. 
               sum(j$(a(j,l2)>0), f(j,l2)) - sum(j$(a(l2,j)>0), f(l2,j)) =e= 0;
#-------------------Quality specifications balances around pools----------------
qualblnc(l2,k).. sum(s$(a(s,l2)>0), q(s,k)*f(s,l2)) + 
                         sum((s,l1)$(a(s,l1)*a(l1,l2)>0), q(s,k)*x(s,l1,l2)) + 
        sum(h2$(a(h2,l2)>0), v(k,h2,l2)) - sum(j$(a(l2,j)>0), v(k,l2,j)) =e= 0;
#------------------------Product quality specifications-------------------------
qualub(t,k)$(abs(q(t,k))<+inf).. sum(s$(a(s,t)>0), q(s,k)*f(s,t)) + 
                           sum((s,l1)$(a(s,l1)*a(l1,t)>0), q(s,k)*x(s,l1,t)) + 
       sum(h2$(a(h2,t)>0), v(k,h2,t)) - q(t,k)*sum(j$(a(j,t)>0), f(j,t)) =l= 0;
#-------------------------Commodity proportion balances-------------------------
propblnc(l1).. sum(s$(a(s,l1)>0), y(s,l1)) - 1 =e= 0;
#---------------------RLT for commodity proportion balances---------------------
rlt1(l1,j)$(a(l1,j)>0).. f(l1,j) - sum(s$(a(s,l1)>0), x(s,l1,j)) =e= 0;
#----------------------------RLT for pool capacities----------------------------
rlt2(s,l1)$(a(s,l1)>0 and bu(l1)<+inf).. sum(j$(a(l1,j)>0), x(s,l1,j)) - 
                                                          y(s,l1)*bu(l1) =l= 0;
#--------------Convex/concave envelopes of x(s,l1,j) = y(s,l1)*f(l1,j)----------
vexlby(s,l1,j)$(a(s,l1)*a(l1,j)>0).. x(s,l1,j) =g= y.lo(s,l1)*f(l1,j) + 
                                    y(s,l1)*f.lo(l1,j) - y.lo(s,l1)*f.lo(l1,j); 
vexuby(s,l1,j)$(a(s,l1)*a(l1,j)>0).. x(s,l1,j) =g= y.up(s,l1)*f(l1,j) + 
                                    y(s,l1)*f.up(l1,j) - y.up(s,l1)*f.up(l1,j);
cavlby(s,l1,j)$(a(s,l1)*a(l1,j)>0).. x(s,l1,j) =l= y.lo(s,l1)*f(l1,j) + 
                                    y(s,l1)*f.up(l1,j) - y.lo(s,l1)*f.up(l1,j);
cavuby(s,l1,j)$(a(s,l1)*a(l1,j)>0).. x(s,l1,j) =l= y.up(s,l1)*f(l1,j) + 
                                    y(s,l1)*f.lo(l1,j) - y.up(s,l1)*f.lo(l1,j);
#--------------Convex/concave envelopes of v(k,l2,j) = w(l2,k)*f(l2,j)----------
vexlbw(k,l2,j)$(a(l2,j)>0).. v(k,l2,j) =g= w.lo(l2,k)*f(l2,j) +
                                    w(l2,k)*f.lo(l2,j) - w.lo(l2,k)*f.lo(l2,j); 
vexubw(k,l2,j)$(a(l2,j)>0).. v(k,l2,j) =g= w.up(l2,k)*f(l2,j) +
                                    w(l2,k)*f.up(l2,j) - w.up(l2,k)*f.up(l2,j);
cavlbw(k,l2,j)$(a(l2,j)>0).. v(k,l2,j) =l= w.lo(l2,k)*f(l2,j) +
                                    w(l2,k)*f.up(l2,j) - w.lo(l2,k)*f.up(l2,j);
cavubw(k,l2,j)$(a(l2,j)>0).. v(k,l2,j) =l= w.up(l2,k)*f(l2,j) +
                                    w(l2,k)*f.lo(l2,j) - w.up(l2,k)*f.lo(l2,j);

#===============================================================================
# Solve the model
#===============================================================================
option lp = cplex;
model hybrelax /all/;
hybrelax.solprint = 2;
solve hybrelax minimizing cost using lp;
#============================Print solution information=========================
scalars ae, re;
ae = abs(hybrelax.objval - hybrelax.objval);
re = ae/abs(hybrelax.objval);
file line; 
put_utility line 'msg' / '#####' ' Solution Summary #####';
line.nd = 6;
line.nw = 18;
put_utility line 'msg' / hybrelax.objval ' ' hybrelax.objval ' ' hybrelax.resusd 
' ' re ' ' ae;
line.nd = 0;
put_utility line 'msg' / hybrelax.solvestat ' ' hybrelax.iterusd ' ' 
(hybrelax.numvar-1) ' ' 0 ' ' (hybrelax.numequ-1) ' ' 0;
option f:6:0:2; display f.l;
option y:6:0:2; display y.l;
option w:6:0:2; display w.l;
#========================================END====================================