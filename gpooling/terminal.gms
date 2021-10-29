$ontext
    File name: pmodel.gms
    Author: Mohammed Alfaki, December, 2010.
    GAMS model for a heuristic algorithm to the pooling problem.
$offtext

#===============================================================================
# Declare options
#===============================================================================
options optcr=1.e-9, optca=1.e-6, limrow=20, limcol=0, reslim=3600;

#===============================================================================
# Declare sets and parameters
#===============================================================================
set lt(i), l(i), tau(t), tp(t);
lt(i) = i(i)-s(i); l(i) = i(i)-s(i)-t(i); tau(t) = no; tp(t) = no;
alias (l,h);
parameter fp(i,j);
fp(i,j) = 0;

# Is there a path between (s,l)
parameter p(i,j);
#===============================================================================
# Compute p(s,i) using the Breadth-first-search (BFS)
#===============================================================================
alias (i,ii,iii), (j,jj), (l,ll);
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
tau('38') = yes;
variable cost;
positive variables f(i,j);

f.up(i,j) = min(bu(i),bu(j))*a(i,j);

#===============================================================================
# Declare constraints
#===============================================================================
equations obj(t), sflowcaplb(s,t), sflowcapub(s,t), pflowcapub(i,t), 
          tflowcaplb(t), tflowcapub(t), flowmassblnc(i,t), qualubtau(t,k);

obj(tau).. cost =e= sum((i,j)$(a(i,j)*p(j,tau)>0), c(i,j)*f(i,j));
#-------------------------Raw material availabilities---------------------------
sflowcaplb(s,tau)$(bl(s)*p(s,tau)>0).. 
                          sum(j$(a(s,j)*p(j,tau)>0), fp(s,j)+f(s,j)) =g= bl(s);
sflowcapub(s,tau)$(bu(s)<+inf and p(s,tau)>0).. 
                          sum(j$(a(s,j)*p(j,tau)>0), fp(s,j)+f(s,j)) =l= bu(s);
#----------------Pool capacities and product demand restrictions----------------
pflowcapub(l,tau)$(bu(l)<+inf and p(l,tau)>0).. 
                                   sum(j$(a(j,l)>0), fp(j,l)+f(j,l)) =l= bu(l);
tflowcaplb(tau)$(bl(tau)>0).. 
                           sum(j$(a(j,tau)>0), fp(j,tau)+f(j,tau)) =g= bl(tau);
tflowcapub(tau)$(bu(tau)<+inf).. 
                           sum(j$(a(j,tau)>0), fp(j,tau)+f(j,tau)) =l= bu(tau);
#------------------------Flow mass balance around pools-------------------------
flowmassblnc(l,tau)$(p(l,tau)>0).. sum(j$(a(j,l)>0), f(j,l)) =e= f(l,tau);
#---------------Product quality specifications at tau when p0=0------------------
qualubtau(tau,k)$(abs(q(tau,k))<+inf and card(tp) eq 0)..
                             sum(s$(a(s,tau)>0), (q(s,k)-q(tau,k))*f(s,tau)) + 
                sum((s,l)$(a(s,l)*a(l,tau)>0), (q(s,k)-q(tau,k))*f(s,l)) =l= 0;
    
#===============================================================================
# Solve the model
#===============================================================================
option lp = cplex;
model hrslp /all/;
#$onecho > convert.opt
#dict
#cplexlp RT2.lp
#$offecho
#m.optfile = 1;
solve hrslp minimizing cost using lp;
parameters Fp(i,j), Wp(i,k);
Fp(i,j)$(a(i,j)>0) = f.l(i,j)+fp(i,j);
Wp(l,k)$(sum(j$(a(l,j)>0), Fp(l,j))>0) = 
                  sum(s$(a(s,l)>0), q(s,k)*Fp(s,l))/sum(j$(a(l,j)>0), Fp(l,j));
option Fp:6:0:2; display Fp;
option Wp:6:0:2; display Wp;
execute_unload 'log.gdx', Fp, Wp;