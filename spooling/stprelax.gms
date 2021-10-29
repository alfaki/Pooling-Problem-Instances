$ontext
    File name: stprelax.gms.
    Author: Mohammed Alfaki, December, 2010.
    GAMS model for the STP-relaxation.
$offtext

#===============================================================================
# Declare options
#===============================================================================
options optcr=1.e-9, limrow=0, limcol=0, iterlim=1.e9, reslim=1.e9;

#===============================================================================
# Declare sets
#===============================================================================
set l(i); l(i) = i(i)-s(i)-t(i);

#===============================================================================
# Declare variables/bounds
#===============================================================================
variable cost;
positive variables f(i,j), y(i,j), x(s,i,t);

f.up(i,j) = min(bu(i),bu(j))*a(i,j);
y.up(i,j) = a(i,j);
x.up(s,i,t) = min(bu(s),bu(i),bu(t))*a(s,i)*a(i,t);

#===============================================================================
# Declare constraints
#===============================================================================
equations obj, sflowcaplb(s), sflowcapub(s), pflowcap(i), tflowcaplb(t), 
          tflowcapub(t), qualub(t,k), spropblnc(i), tpropblnc(i), srlt1(i,t), 
          trlt1(s,j), srlt2(s,j), trlt2(i,t), svexlb(s,i,t), svexub(s,i,t), 
          scavlb(s,i,t), scavub(s,i,t), tvexlb(s,i,t), tvexub(s,i,t), 
          tcavlb(s,i,t), tcavub(s,i,t);

#===============================================================================
# Define constraints
#===============================================================================
#-----------------------------Objective function--------------------------------
obj.. cost =e= sum((s,l,t)$(a(s,l)*a(l,t)>0),(c(s,l) + c(l,t))*x(s,l,t)) +
                                          sum((s,t)$(a(s,t)>0), c(s,t)*f(s,t));
#-------------------------Raw material availabilities---------------------------
sflowcaplb(s)$(bl(s)>0).. sum((l,t)$(a(s,l)*a(l,t)>0), x(s,l,t)) + 
                                           sum(t$(a(s,t)>0), f(s,t)) =g= bl(s);
sflowcapub(s)$(bu(s)<+inf).. sum((l,t)$(a(s,l)*a(l,t)>0), x(s,l,t)) +
                                           sum(t$(a(s,t)>0), f(s,t)) =l= bu(s);
#-------------------------------Pool capacities---------------------------------
pflowcap(l)$(bu(l)<+inf).. sum((s,t)$(a(s,l)*a(l,t)>0), x(s,l,t)) =l= bu(l);
#-------------------------Product demand restrictions---------------------------
tflowcaplb(t)$(bl(t)>0).. sum((s,l)$(a(s,l)*a(l,t)>0), x(s,l,t)) + 
                                           sum(s$(a(s,t)>0), f(s,t)) =g= bl(t);
tflowcapub(t)$(bu(t)<+inf).. sum((s,l)$(a(s,l)*a(l,t)>0), x(s,l,t)) + 
                                           sum(s$(a(s,t)>0), f(s,t)) =l= bu(t);
#------------------------Product quality specifications-------------------------
qualub(t,k)$(abs(q(t,k))>0 and abs(q(t,k))<+inf).. 
                  sum((l,s)$(a(s,l)*a(l,t)>0), (q(s,k) - q(t,k))*x(s,l,t)) + 
                             sum(s$(a(s,t)>0), (q(s,k) - q(t,k))*f(s,t)) =l= 0;
#------------------------------Proportion balances------------------------------
spropblnc(l).. sum(s$(a(s,l)>0), y(s,l)) =e= 1;
tpropblnc(l).. sum(t$(a(l,t)>0), y(l,t)) =e= 1;
#--------------------------RLT for proportion balances--------------------------
srlt1(l,t)$(a(l,t)>0).. sum(s$(a(s,l)>0), x(s,l,t)) =e= f(l,t);
trlt1(s,l)$(a(s,l)>0).. sum(t$(a(l,t)>0), x(s,l,t)) =e= f(s,l);
#----------------------------RLT for pool capacities----------------------------
srlt2(s,l)$(a(s,l)>0 and bu(l)<+inf).. f(s,l) =l= bu(l)*y(s,l);
trlt2(l,t)$(a(l,t)>0 and bu(l)<+inf).. f(l,t) =l= bu(l)*y(l,t);
#---------------Convex/concave envelopes of x(s,l,t) = y(s,l)*f(l,t)------------
svexlb(s,l,t)$(a(s,l)*a(l,t)>0).. x(s,l,t) =g= y.lo(s,l)*f(l,t) +
                                        y(s,l)*f.lo(l,t) - y.lo(s,l)*f.lo(l,t); 
svexub(s,l,t)$(a(s,l)*a(l,t)>0).. x(s,l,t) =g= y.up(s,l)*f(l,t) +
                                        y(s,l)*f.up(l,t) - y.up(s,l)*f.up(l,t);
scavlb(s,l,t)$(a(s,l)*a(l,t)>0).. x(s,l,t) =l= y.lo(s,l)*f(l,t) +
                                        y(s,l)*f.up(l,t) - y.lo(s,l)*f.up(l,t);
scavub(s,l,t)$(a(s,l)*a(l,t)>0).. x(s,l,t) =l= y.up(s,l)*f(l,t) +
                                        y(s,l)*f.lo(l,t) - y.up(s,l)*f.lo(l,t);
#--------------Convex/concave envelopes of x(s,l,t) = y(l,t)*f(s,l)-------------
tvexlb(s,l,t)$(a(s,l)*a(l,t)>0).. x(s,l,t) =g= y.lo(l,t)*f(s,l) +
                                        y(l,t)*f.lo(s,l) - y.lo(l,t)*f.lo(s,l); 
tvexub(s,l,t)$(a(s,l)*a(l,t)>0).. x(s,l,t) =g= y.up(l,t)*f(s,l) +
                                        y(l,t)*f.up(s,l) - y.up(l,t)*f.up(s,l);
tcavlb(s,l,t)$(a(s,l)*a(l,t)>0).. x(s,l,t) =l= y.lo(l,t)*f(s,l) +
                                        y(l,t)*f.up(s,l) - y.lo(l,t)*f.up(s,l);
tcavub(s,l,t)$(a(s,l)*a(l,t)>0).. x(s,l,t) =l= y.up(l,t)*f(s,l) +
                                        y(l,t)*f.lo(s,l) - y.up(l,t)*f.lo(s,l);

#===============================================================================
# Solve the model
#===============================================================================
option lp = cplex;
model stprelax /all/;
stprelax.solprint = 2;
solve stprelax minimizing cost using lp;
#============================Print solution information=========================
scalars ae, re;
ae = abs(stprelax.objval - stprelax.objval);
re = ae/abs(stprelax.objval);
file line;
put_utility line 'msg' / '#####' ' Solution Summary #####';
line.nd = 6;
line.nw = 18;
put_utility line 'msg' / stprelax.objval ' ' stprelax.objval ' ' stprelax.resusd 
re ' ' ae;
line.nd = 0;
put_utility line 'msg' / stprelax.solvestat ' ' stprelax.iterusd ' ' 
(stprelax.numvar-1) ' ' 0 ' ' (stprelax.numequ-1) ' ' 0;
option f:6:0:2; display f.l;
option y:6:0:2; display y.l;
#========================================END====================================