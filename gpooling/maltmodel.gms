$ontext
    File name: hrspmodel.gms
    Author: Mohammed Alfaki, December, 2010.
    GAMS model for the multi-start alternate heuristic with the P-formulation.
$offtext

#===============================================================================
# Declare options
#===============================================================================
options limrow=0, limcol=0;

#===============================================================================
# Declare sets and parameters
#===============================================================================
sets lt(i), l(i);
lt(i) = i(i)-s(i); l(i) = i(i)-s(i)-t(i);
parameters Fp(i,j), Wp(i,k); Fp(i,j) = 0; Wp(i,k) = 0; 
scalars igap, gap; igap = 1.e-3; gap = 1.e-6; 

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
variable cost, w(i,k);
positive variables f(i,j);

w.lo(l,k) = smin(s$(p(s,l)>0),q(s,k));
w.up(l,k) = smax(s$(p(s,l)>0),q(s,k));
f.up(i,j) = min(bu(i),bu(j))*a(i,j);

#===============================================================================
equations obj1, obj2, sflowcaplb1(s), sflowcaplb2(s), sflowcapub1(s), 
          sflowcapub2(s), tflowcaplb1(t), tflowcaplb2(t), ptflowcapub1(i), 
          ptflowcapub2(i), flowmassblnc1(i), flowmassblnc2(i), qualblnc1(i,k), 
          qualblnc2(i,k), qualub1(t,k), qualub2(t,k);

#===============================================================================
# Define constraints
#==========================Fixing quality attributes============================
obj1.. cost =e= sum((i,j)$(a(i,j)>0), c(i,j)*f(i,j));
sflowcaplb1(s)$(bl(s)>0).. sum(j$(a(s,j)>0), f(s,j)) =g= bl(s);
sflowcapub1(s)$(bu(s)<+inf).. sum(j$(a(s,j)>0), f(s,j)) =l= bu(s);
tflowcaplb1(t)$(bl(t)>0).. sum(j$(a(j,t)>0), f(j,t)) =g= bl(t);
ptflowcapub1(lt)$(bu(lt)<+inf).. sum(j$(a(j,lt)>0), f(j,lt)) =l= bu(lt);
flowmassblnc1(l).. sum(j$(a(j,l)>0), f(j,l)) =e= sum(j$(a(l,j)>0), f(l,j));
qualblnc1(l,k).. sum(s$(a(s,l)>0), q(s,k)*f(s,l)) + 
        sum(h$(a(h,l)>0), Wp(h,k)*f(h,l)) =e= Wp(l,k)*sum(j$(a(l,j)>0), f(l,j));
qualub1(t,k)$(abs(q(t,k))<+inf).. sum(s$(a(s,t)>0), q(s,k)*f(s,t)) + 
     sum(l$(a(l,t)>0), Wp(l,k)*f(l,t)) - q(t,k)*sum(j$(a(j,t)>0), f(j,t)) =l= 0;

option lp = cplex;
model altw /obj1, sflowcaplb1, sflowcapub1, tflowcaplb1, ptflowcapub1, 
            flowmassblnc1, qualblnc1, qualub1/;
altw.solprint = 2;
altw.tolinfeas = igap;
#==========================Fixing flow of f(l,j)================================
obj2.. cost =e= sum((s,j)$(a(s,j)>0), c(s,j)*f(s,j)) +
                                          sum((l,j)$(a(l,j)>0), c(l,j)*Fp(l,j));
sflowcaplb2(s)$(bl(s)>0).. sum(j$(a(s,j)>0), f(s,j)) =g= bl(s);
sflowcapub2(s)$(bu(s)<+inf).. sum(j$(a(s,j)>0), f(s,j)) =l= bu(s);
tflowcaplb2(t)$(bl(t)>0).. sum(s$(a(s,t)>0), f(s,t)) + 
                                           sum(l$(a(l,t)>0), Fp(l,t)) =g= bl(t);
ptflowcapub2(lt)$(bu(lt)<+inf).. sum(s$(a(s,lt)>0), f(s,lt)) + 
                                        sum(l$(a(l,lt)>0), Fp(l,lt)) =l= bu(lt);
flowmassblnc2(l).. sum(j$(a(j,l)>0), f(j,l)) =e= sum(j$(a(l,j)>0), Fp(l,j));
qualblnc2(l,k).. sum(s$(a(s,l)>0), q(s,k)*f(s,l)) + 
        sum(h$(a(h,l)>0), w(h,k)*Fp(h,l)) =e= w(l,k)*sum(j$(a(l,j)>0), Fp(l,j));
qualub2(t,k)$(abs(q(t,k))<+inf).. sum(s$(a(s,t)>0), q(s,k)*f(s,t)) + 
         sum(l$(a(l,t)>0), w(l,k)*Fp(l,t)) - q(t,k)*sum(s$(a(s,t)>0), f(s,t)) -
                                        q(t,k)*sum(l$(a(l,t)>0), Fp(l,t)) =l= 0;

model altf /obj2, sflowcaplb2, sflowcapub2, tflowcaplb2, ptflowcapub2, 
               flowmassblnc2, qualblnc2, qualub2/;
altf.solprint = 2;
altf.tolinfeas = igap;
#===============================================================================
$set console 
$ifthen set fo $set console msmmodel.log
$elseif %system.filesys% == UNIX $set console /dev/tty
$elseif %system.filesys% == DOS $set console con
$else "%console%." == "." abort "file system not recognized"
$endif
file screen /'%console%'/;
put screen;
put /;
put 'Multi-start Alternate Heuristic'/;
put '========================================='/;
put 'Iter          Time      Feasible Solution'/;
putclose;

scalars converge, ptime, starttime, elapsed, p0, solp, soltime; 
p0 = 0; solp = 0; soltime = 0; starttime = jnow;
scalars alt_obj, obj_best, ttime; obj_best = inf; ttime = 3600;
parameter fs(i,j), ws(i,k);
fs(i,j)$(a(i,j)>0) = 0;

repeat(
  execseed = 1+gmillisec(jnow);
  Wp(l,k) = uniform(w.lo(l,k),w.up(l,k));
  p0 = p0+1;
  repeat(
    ptime = ttime-(jnow - starttime)*24*3600;
    if(ptime > 0,
      f.l(i,j)$(a(i,j)>0) = 0; cost.l = 0;
      altw.reslim = ptime;
      solve altw minimizing cost using lp;
      Fp(i,j)$(a(i,j)>0) = f.l(i,j);
    );
    ptime = ttime-(jnow - starttime)*24*3600;
    if(ptime > 0,
      w.l(l,k) = 0.5*(w.lo(l,k)+w.up(l,k)); f.l(s,j)$(a(s,j)>0) = 0; cost.l = 0;
      altf.reslim = ptime;
      solve altf minimizing cost using lp;
      Fp(s,j)$(a(s,j)>0) = f.l(s,j);  
    );
    converge = (altw.modelstat le 2 and altf.modelstat le 2 and 
                smax((l,k), abs(w.l(l,k)-Wp(l,k))) < gap and 
                smax((i,j)$(a(i,j)>0), abs(f.l(i,j)-Fp(i,j))) < gap);
    Wp(l,k) = w.l(l,k);
    elapsed = (jnow - starttime)*24*3600;
  until(converge or elapsed ge ttime));
  if(converge, 
    alt_obj = sum((i,j)$(a(i,j)>0), c(i,j)*f.l(i,j));
    if((alt_obj < obj_best), 
      obj_best = alt_obj;
      fs(i,j)$(a(i,j)>0) = f.l(i,j);
      ws(l,k) = w.l(l,k);
      solp = p0;
      soltime = (jnow - starttime)*24*3600;
      put screen;
      screen.nw = 4;
      screen.nd = 0;
      put p0;
      screen.nw = 7;
      screen.nd = 2;
      put @12 soltime;
      screen.nw = 16;
      screen.nd = 6;
      put @26 obj_best/;
      putclose;        
    );
  );
  elapsed = (jnow - starttime)*24*3600;
until(elapsed ge ttime));

Fp(i,j) = fs(i,j);
Wp(l,k) = ws(l,k);

put screen;
screen.nw = 16;
put /'========================================='/;
put 'Best feasible solution = ' obj_best /;
screen.nd = 0;
put 'Soltion found at iter  = ' solp /;
put 'Total number of iters  = ' p0 /;
screen.nd = 2;
put 'Soution found at time  = ' soltime /;
put 'Total time in seconds  = ' elapsed /;
put '========================================='/;
putclose;
#============================Print solution information=========================
scalar vars, lcsts;
vars = max(altw.numvar,altf.numvar)-1;
lcsts = max(altw.numequ,altf.numequ)-1;
file line;
put_utility line 'msg' / '#####' ' Solution Summary #####';
line.nw = 16;
line.nd = 6;
put_utility line 'msg' / obj_best ' ' soltime ' ' elapsed ' ' solp ' ' 0.0;
line.nd = 0;
put_utility line 'msg' / 1 ' ' p0 ' ' vars ' ' 0 ' ' lcsts ' ' 0;
# First row: best sol (ub), sol time, total time.
# Second row: solstat, num iter, vars, sol iter, lconsts, 
option Fp:6:0:2; display Fp;
option Wp:6:0:2; display Wp;
execute_unload 'sol.gdx', Fp, Wp;
#========================================END====================================