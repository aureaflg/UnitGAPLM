library(gamlss)
library(matrixcalc)
library(ggplot2)
library(stringr)
library(Matrix)
library(VGAM)
library(MASS)
library(ggplot2)
library(ggrepel)
library(aod)
library(qqplotr)
source("auxiliarfunctions-BR-GAPLM.R")


####################################################################################
######################### Estimation process #######################################
####################################################################################


Q1<-function(param,v,y,E,X,gamm,D,B,lamb,lig){
  p=ncol(X)
  s=ncol(E)
  bet=param[1:p]
  kapp=param[(1+p):(s+p)]
  alpha=param[s+p+1]
  eta1=X%*%bet+B%*%gamm
  if(lig=='logit'){
    mu<- logitlink(eta1, inverse = TRUE)
  }else if(lig=='probit'){
    mu<- probitlink(eta1, inverse = TRUE)
  } else if(lig=='cloglog'){
    mu<- clogloglink(eta1, inverse = TRUE)
  } else if(lig=='cauchit'){
    mu<- cauchitlink(eta1, inverse = TRUE)
  } else if(lig=='loglog'){
    mu<- exp(-exp(-eta1))
  } else {print('Link function not defined')
  } 
  eta2=E%*%kapp
  phi=exp(eta2)
  epi<-1-sqrt(1-4*alpha*mu*(1-mu))
  delta<- (mu-0.5*epi)/(1-epi)
  a=delta*phi
  b=(1-delta)*phi
  Dlamb=lamb*D
  Q1=sum(v*log(epi)+(1-v)*log(1-epi)+(1-v)*dbeta(y,a,b,log=TRUE))-
    0.5*t(gamm)%*%Dlamb%*%gamm
  return(-Q1)
}


Q2<-function(gamm,v,y,E,X,param,D,B,lamb,lig){
  p=ncol(X)
  s=ncol(E)
  bet=param[1:p]
  kapp=param[(1+p):(s+p)]
  alpha=param[s+p+1]
  eta1=X%*%bet+B%*%gamm
  if(lig=='logit'){
    mu<- logitlink(eta1, inverse = TRUE)
  }else if(lig=='probit'){
    mu<- probitlink(eta1, inverse = TRUE)
  } else if(lig=='cloglog'){
    mu<- clogloglink(eta1, inverse = TRUE)
  } else if(lig=='cauchit'){
    mu<- cauchitlink(eta1, inverse = TRUE)
  } else if(lig=='loglog'){
    mu<- exp(-exp(-eta1))
  } else {print('Link function not defined')
  } 
  eta2=E%*%kapp
  phi=exp(eta2)
  epi<-1-sqrt(1-4*alpha*mu*(1-mu))
  delta<- (mu-0.5*epi)/(1-epi)
  a=delta*phi
  b=(1-delta)*phi
  Dlamb=lamb*D
  Q1=sum(v*log(epi)+(1-v)*log(1-epi)+(1-v)*dbeta(y,a,b,log=TRUE))-
    0.5*t(gamm)%*%Dlamb%*%gamm
  return(-Q1)
}


Qb<-function(param,v,y,E,X,gamm,D,B,lamb,lig){
  s=ncol(E)
  kapp=param[1:s]
  alpha=param[s+1]
  eta1=B%*%gamm
  if(lig=='logit'){
    mu<- logitlink(eta1, inverse = TRUE)
  }else if(lig=='probit'){
    mu<- probitlink(eta1, inverse = TRUE)
  } else if(lig=='cloglog'){
    mu<- clogloglink(eta1, inverse = TRUE)
  } else if(lig=='cauchit'){
    mu<- cauchitlink(eta1, inverse = TRUE)
  } else if(lig=='loglog'){
    mu<- exp(-exp(-eta1))
  } else {print('Link function not defined')
  } 
  eta2=E%*%kapp
  phi=exp(eta2)
  epi<-1-sqrt(1-4*alpha*mu*(1-mu))
  delta<- (mu-0.5*epi)/(1-epi)
  a=delta*phi
  b=(1-delta)*phi
  Dlamb=lamb*D
  Q1=sum(v*log(epi)+(1-v)*log(1-epi)+(1-v)*dbeta(y,a,b,log=TRUE))-
    0.5*t(gamm)%*%Dlamb%*%gamm
  return(-Q1)
}


Q2b<-function(gamm,v,y,E,X,param,D,B,lamb,lig){
  s=ncol(E)
  kapp=param[1:s]
  alpha=param[s+1]
  eta1=B%*%gamm
  if(lig=='logit'){
    mu<- logitlink(eta1, inverse = TRUE)
  }else if(lig=='probit'){
    mu<- probitlink(eta1, inverse = TRUE)
  } else if(lig=='cloglog'){
    mu<- clogloglink(eta1, inverse = TRUE)
  } else if(lig=='cauchit'){
    mu<- cauchitlink(eta1, inverse = TRUE)
  } else if(lig=='loglog'){
    mu<- exp(-exp(-eta1))
  } else {print('Link function not defined')
  } 
  eta2=E%*%kapp
  phi=exp(eta2)
  epi<-1-sqrt(1-4*alpha*mu*(1-mu))
  delta<- (mu-0.5*epi)/(1-epi)
  a=delta*phi
  b=(1-delta)*phi
  Dlamb=lamb*D
  Q1=sum(v*log(epi)+(1-v)*log(1-epi)+(1-v)*dbeta(y,a,b,log=TRUE))-
    0.5*t(gamm)%*%Dlamb%*%gamm
  return(-Q1)
}

### Function to fit the BR-GAPLM

brgaplm<-function(formula.mu=formula,formula.phi=~1,data=NULL,mu.link,
                iter=50,trace=F,knots=20,degreepb=3,order=2,lambda=NULL,
                method="GAIC",k=2,c=FALSE,liminf=NULL){
  
  mcall <- if(is.null(data)){ terms(formula.mu, specials = "pb") 
  }else terms(formula.mu, specials = "pb", data = data)    
  mu.X <- if(is.null(data)){ model.matrix(mcall) 
  }else model.matrix(mcall, data = data)
  label <- colnames(mu.X)#attr(mcall,"term.labels") 
  aux <- which(str_detect(label, pattern = "pb")==T)
  X <- matrix(mu.X[,-aux], ncol=(ncol(mu.X)-length(aux)))
  Z <- as.matrix(mu.X[,aux])
  y <- if(is.null(data)){ model.frame(mcall)[,1] 
  }else model.frame(mcall, data = data)[,1]
  E <- if(is.null(data)){ model.matrix(formula.phi)
  }else model.matrix(formula.phi, data = data)  
  
  if(is.null(data)){
    data=cbind(model.frame(mcall),model.frame(formula.phi))
  } else data=data
  
  
  if(ncol(X)==0){
    s<-ncol(E)
    nq<-ncol(Z)
    ntol<-nrow(E)
    
    Bs<-list(NULL)
    Ds<-list(NULL)
    qj=rep(0,nq)
    for (au in 1:nq){
      ajus<-pbfake(as.vector(Z[,au]),inter = knots, degree = degreepb,
                   order = order)
      Bs[[au]]=attr(ajus,"X")
      Ds[[au]]=t(attr(ajus,"D"))%*%attr(ajus,"D")
      qj[au]=ncol(Bs[[au]])
    }
    
    B=Reduce("cbind",Bs)
    D=as.matrix(bdiag(Ds))
    
    if(!is.null(lambda)){
      lamb=rep(0,sum(qj))
      if(length(lambda)==nq){
        for(au2 in 1:nq){
          if(au2==1){
            lamb[1:qj[au2]]<-rep(lambda[au2],qj[au2])
            next
          }
          lamb[(sum(qj[1:(au2-1)])+1):(sum(qj[1:(au2-1)])+qj[au2])]<-rep(lambda[au2],qj[au2])
        }
      }else lamb<-rep(lambda,sum(qj))
    }else{lamb<-rep(0.01,sum(qj))}
    
    
    #Valores iniciais
    gamm<-ginv(t(B)%*%B+lamb*D)%*%t(B)%*%y
    kapp<-solve(t(E)%*%E)%*%t(E)%*%y
    alpha<-(2*sum(y^2))/(sum(y^2)+ntol)
    par0 <- c(kapp,alpha)
    
    
    i=0
    dif=1
    while(dif>0.001){
      
      i=i+1
      
      eta1<-B%*%gamm
      eta2<-E%*%kapp
      phi<-exp(eta2)
      if(mu.link=='logit'){
        mu<- logitlink(eta1, inverse = TRUE)
      }else if(mu.link=='probit'){
        mu<- probitlink(eta1, inverse = TRUE)
      } else if(mu.link=='cloglog'){
        mu<- clogloglink(eta1, inverse = TRUE)
      } else if(mu.link=='cauchit'){
        mu<- cauchitlink(eta1, inverse = TRUE)
      } else if(mu.link=='loglog'){
        mu<- exp(-exp(-eta1))
      } else {print('Link function not defined')
      } 
      epi<-1-sqrt(1-4*alpha*mu*(1-mu))
      delta<-(mu-0.5+0.5*(1-epi))/(1-epi)
      a<-delta*phi
      b<-(1-delta)*phi
      
      ###Passo E
      v<-epi/(epi+(1-epi)*dbeta(y,a,b))
      
      ##Passo M
      gammnew=optim(gamm, Q2b, method = "L-BFGS-B", v = v, y = y,lig=mu.link, 
                    E = E, X = X, param = par0, D = D, B = B,lamb = lamb,
                    lower=c(rep(-Inf,sum(qj))), 
                    upper=c(rep(Inf,sum(qj))))$par
      gamm=gammnew
      resu1=nlminb(par0, Qb, v = v, y = y, lig=mu.link,
                   E = E, X = X, gamm = gamm, D = D, B = B,lamb = lamb,
                   lower=c(rep(-Inf,s),0.001), 
                   upper=c(rep(Inf,s),0.999))
      resu=resu1$par
      kapp=resu[1:s]
      alpha=resu[s+1]
      dif=sqrt(t(resu-par0)%*%(resu-par0))
      par0=c(kapp,alpha)
      
      if(is.null(lambda)){
        statuslam=1
      }else{statuslam=0}
      quant=estlambdab(lambda=lamb,y=y,X=X,E=E,Ds=Ds,D=D,Bs=Bs,B=B,
                       qj=qj,gamm=gamm,kapp=kapp,alpha=alpha,
                       method=method,k=k,c=c,statuslam=statuslam,
                       lig=mu.link)
      lamb0=quant$lambda
      lamb=lamb0 
      #Stop if exceeds requested number of iterations
      
      if (i==iter)
      {
        break
      }
      if (trace==T){
        print(kapp)
        print(alpha)
        print(i)
      }
      
    }
    quant1=estlambdab(lamb,y,X,E,Ds,D,Bs,B,qj,gamm,kapp,alpha,
                      method=method,k=k,c=c,statuslam=0,lig=mu.link)
    
    mu.lp<-B%*%gamm
    phi.lp<-E%*%kapp
    phi.fv<-exp(phi.lp)
    if(mu.link=='logit'){
      mu.fv<- logitlink(mu.lp, inverse = TRUE)
    }else if(mu.link=='probit'){
      mu.fv<- probitlink(mu.lp, inverse = TRUE)
    } else if(mu.link=='cloglog'){
      mu.fv<- clogloglink(mu.lp, inverse = TRUE)
    } else if(mu.link=='cauchit'){
      mu.fv<- cauchitlink(mu.lp, inverse = TRUE)
    } else if(mu.link=='loglog'){
      mu.fv<- exp(-exp(-mu.lp))
    } else {print('Link function not defined')
    } 
  }else{
    
    p<-ncol(X)
    s<-ncol(E)
    nq<-ncol(Z)
    ntol<-nrow(X)
    
    
    Bs<-list(NULL)
    Ds<-list(NULL)
    qj=rep(0,nq)
    for (au in 1:nq){
      ajus<-pbfake(as.vector(Z[,au]),inter = knots, degree = degreepb,
                   order = order)
      Bs[[au]]=attr(ajus,"X")
      Ds[[au]]=t(attr(ajus,"D"))%*%attr(ajus,"D")
      qj[au]=ncol(Bs[[au]])
    }
    
    B=Reduce("cbind",Bs)
    D=as.matrix(bdiag(Ds))
    
    if(!is.null(lambda)){
      lamb=rep(0,sum(qj))
      if(length(lambda)==nq){
        for(au2 in 1:nq){
          if(au2==1){
            lamb[1:qj[au2]]<-rep(lambda[au2],qj[au2])
            next
          }
          lamb[(sum(qj[1:(au2-1)])+1):(sum(qj[1:(au2-1)])+qj[au2])]<-rep(lambda[au2],qj[au2])
        }
      }else lamb<-rep(lambda,sum(qj))
    }else{lamb<-rep(0.01,sum(qj))}
    
    
    ## Initial values
    bet<-solve(t(X)%*%X)%*%t(X)%*%y
    gamm<-ginv(t(B)%*%B+lamb*D)%*%t(B)%*%(y-X%*%bet)
    kapp<-solve(t(E)%*%E)%*%t(E)%*%y
    alpha<-(2*sum(y^2))/(sum(y^2)+ntol)
    par0 <- c(bet,kapp,alpha)
    
    i=0
    dif=1
    while(dif>0.001){
      
      i=i+1
      
      eta1<-X%*%bet+B%*%gamm
      eta2<-E%*%kapp
      phi<-exp(eta2)
      if(mu.link=='logit'){
        mu<- logitlink(eta1, inverse = TRUE)
      }else if(mu.link=='probit'){
        mu<- probitlink(eta1, inverse = TRUE)
      } else if(mu.link=='cloglog'){
        mu<- clogloglink(eta1, inverse = TRUE)
      } else if(mu.link=='cauchit'){
        mu<- cauchitlink(eta1, inverse = TRUE)
      } else if(mu.link=='loglog'){
        mu<- exp(-exp(-eta1))
      } else {print('Link function not defined')
      } 
      epi<-1-sqrt(1-4*alpha*mu*(1-mu))
      delta<-(mu-0.5+0.5*(1-epi))/(1-epi)
      a<-delta*phi
      b<-(1-delta)*phi
      
      ### E Step
      v<-epi/(epi+(1-epi)*dbeta(y,a,b))
      
      ##Passo M
      gammnew=optim(gamm, Q2, method = "L-BFGS-B", v = v, y = y,lig=mu.link, 
                    E = E, X = X, param = par0, D = D, B = B,lamb = lamb,
                    lower=c(rep(-Inf,sum(qj))), 
                    upper=c(rep(Inf,sum(qj))))$par
      gamm=gammnew
      resu1=nlminb(par0, Q1, v = v, y = y, lig=mu.link,
                   E = E, X = X, gamm = gamm, D = D, B = B,lamb = lamb,
                   lower=c(rep(-Inf,s+p),0.001), 
                   upper=c(rep(Inf,s+p),0.999))
      resu=resu1$par
      bet=resu[1:p]
      kapp=resu[(1+p):(s+p)]
      alpha=resu[s+p+1]
      dif=sqrt(t(resu-par0)%*%(resu-par0))
      par0=c(bet,kapp,alpha)
      
      if(is.null(lambda)){
        statuslam=1
      }else{statuslam=0}
      quant=estlambda(lambda=lamb,y=y,X=X,E=E,Ds=Ds,D=D,Bs=Bs,B=B,
                      qj=qj,bet=bet,gamm=gamm,kapp=kapp,alpha=alpha,
                      method=method,k=k,c=c,statuslam=statuslam,
                      lig=mu.link,liminf=liminf)
      lamb0=quant$lambda
      lamb=lamb0 
      #Stop if exceeds requested number of iterations
      
      if (i==iter)
      {
        break
      }
      if (trace==T){
        print(bet)
        print(kapp)
        print(alpha)
        print(i)
      }
      
    }
    quant1=estlambda(lamb,y,X,E,Ds,D,Bs,B,qj,bet,gamm,kapp,alpha,
                     method=method,k=k,c=c,statuslam=0,lig=mu.link,
                     liminf=liminf)
    
    mu.lp<-X%*%bet+B%*%gamm
    phi.lp<-E%*%kapp
    phi.fv<-exp(phi.lp)
    if(mu.link=='logit'){
      mu.fv<- logitlink(mu.lp, inverse = TRUE)
    }else if(mu.link=='probit'){
      mu.fv<- probitlink(mu.lp, inverse = TRUE)
    } else if(mu.link=='cloglog'){
      mu.fv<- clogloglink(mu.lp, inverse = TRUE)
    } else if(mu.link=='cauchit'){
      mu.fv<- cauchitlink(mu.lp, inverse = TRUE)
    } else if(mu.link=='loglog'){
      mu.fv<- exp(-exp(-mu.lp))
    } else {print('Link function not defined')
    } 
  }
  
  
  resiquan=qnorm(pBRr(y,mu=mu.fv,alpha=alpha,sigma=phi.fv))
  mu.s=matrix(0,ncol=nq,nrow=ntol)
  mu.coefSmo = list()
  for(au3 in 1:nq){
    mu.coefSmo[[au3]] = list()
    if(au3==1){
      mu.s[,1]<-B[,(1:qj[au3])]%*%gamm[(1:qj[au3])]
      mu.coefSmo[[1]]$edf=quant$edf
      mu.coefSmo[[1]]$knots=knots
      mu.coefSmo[[1]]$lambda=lamb[1]
      mu.coefSmo[[1]]$coef=gamm[(1:qj[au3])]
      mu.coefSmo[[1]]$Bk=B[,(1:qj[au3])]
      mu.coefSmo[[1]]$Dk= Ds[[1]]
      mu.coefSmo[[1]]$B=B
      mu.coefSmo[[1]]$D=D
      mu.coefSmo[[1]]$gamm=gamm
      next
    }
    mu.s[,au3]<-B[,(sum(qj[1:(au3-1)])+1):(sum(qj[1:(au3-1)])+qj[au3])]%*%
      gamm[((sum(qj[1:(au3-1)])+1):(sum(qj[1:(au3-1)])+qj[au3]))]
    mu.coefSmo[[au3]]$edf=quant$edf
    mu.coefSmo[[au3]]$knots=knots 
    mu.coefSmo[[au3]]$lambda=lamb[(sum(qj[1:(au3-1)])+1)]
    mu.coefSmo[[au3]]$coef=gamm[((sum(qj[1:(au3-1)])+1):(sum(qj[1:(au3-1)])+qj[au3]))]
    mu.coefSmo[[au3]]$Bk=B[,(sum(qj[1:(au3-1)])+1):(sum(qj[1:(au3-1)])+qj[au3])]
    mu.coefSmo[[au3]]$Dk= Ds[[au3]]
    mu.coefSmo[[au3]]$B=B
    mu.coefSmo[[au3]]$D=D
    mu.coefSmo[[au3]]$gamm=gamm
  }
  
  return(list(mu.coefficients=bet,alpha=alpha,
              phi.coefficients=kapp,
              niter=i,mu.fv=mu.fv,mu.s=mu.s,
              phi.fv=phi.fv,residuals=resiquan,
              mu.link=mu.link,phi.link="log",
              ntol=ntol,mu.formula=formula.mu,
              phi.formula=formula.phi,
              mu.x=X,phi.x=E,data=data,
              y=y,mu.coefSmo=mu.coefSmo,
              mu.lp=mu.lp,phi.lp=phi.lp,
              aic=quant1$aic,
              bic=quant1$bic,aicc=quant1$aicc,
              hqic=quant1$hqic,sabic=quant1$sabic))
}




####################################################################################
########################### Diagnostic tools #######################################
####################################################################################


### Quantile-quantile plot of the residuals
plotres=function(mod){
  smp <- data.frame(norm = mod$residuals)
  s1<-ggplot(data = smp, mapping = aes(sample = norm))  +
    stat_qq_band(conf = 0.95) +
    stat_qq_line() +
    stat_qq_point() +
    labs(x = "Theoretical Quantiles", y = "Quantile Residuals") +
    theme(
      panel.border = element_blank(),
      panel.grid.major = element_blank(),
      panel.grid.minor = element_blank(),
      panel.background = element_blank(),
      axis.line = element_line(colour = "grey"),
      text=element_text(size=20,family="serif")
    )  
  print(s1)
}

gmu=function(mod){
  x = mod$mu.link
  mu=mod$mu.fv
  
  if(x=="logit"){
    dmu=(1/mu+1/(1-mu))^(-1)
    d2mu2=-1/mu^2+1/(1-mu)^2
  }
  if(x=="cloglog"){
    dmu=(1/(log(1-mu)*(mu-1)))^(-1)
    d2mu2=-(log(1-mu)+1)/(log(1-mu)*(mu-1))^2
  }
  if(x=="loglog"){
    dmu=(-1/(mu*log(mu)))^(-1)
    d2mu2=(log(mu)+1)/(mu^2*log(mu)^2)
  }
  if(x=="cauchit"){
    dmu=(pi/(cos(pi*(mu-1/2)))^2)^(-1)
    d2mu2=(2*pi^2*sin(pi*(mu-1/2)))/(cos(pi*(mu-1/2)))^3
  }
  if(x=="probit"){
    dmu=(1/dnorm(qnorm(mu)))^(-1)
    d2mu2=-dnorm(qnorm(mu))*(-qnorm(mu))/(dnorm(qnorm(mu)))^3
  }
  ddmu<-list("dmu"=dmu,"d2mu2"=d2mu2)
}
gphi=function(mod){
  x=mod$phi.link
  phi=mod$phi.fv
  if(x=="log"){
    dphi=(1/phi)^(-1)
    d2phi2=-1/phi^2
  }
  if(x=="1/x^2"){
    dphi=(-(2/phi^3))^(-1)
    d2phi2=6/phi^4
  }
  if(x=="sqrt"){
    dphi=((1/2)*phi^(-1/2))^(-1)
    d2phi2=(-1/4)*phi^(-3/2)
  }
  ddphi<-list("dphi"=dphi,"d2phi2"=d2phi2)
}


### Standard error

stderror=function(mod,conf=0.95){

B=mod$mu.coefSmo[[1]]$B
X=mod$mu.x
E=mod$phi.x
nq=ncol(mod$mu.s)
y=mod$y
qj=lambda=0
for(i in 1:nq){
  qj[i]=ncol(mod$mu.coefSmo[[i]]$Bk)
  if(i==1){
    lambda[(1:qj[i])]=mod$mu.coefSmo[[i]]$lambda
  }
  else lambda[(sum(qj[1:(i-1)])+1):(sum(qj[1:(i-1)])+qj[i])]=
      mod$mu.coefSmo[[i]]$lambda
}
D=0.5*lambda*mod$mu.coefSmo[[1]]$D
n=mod$ntol
s=ncol(mod$phi.x)
p=ncol(mod$mu.x)

gamm=mod$mu.coefSmo[[1]]$gamm
bet=mod$mu.coefficients
kapp=mod$phi.coefficients
T1=diag(as.vector(gmu(mod)$dmu),n)
T2=diag(as.vector(gphi(mod)$dphi),n)

phi=mod$phi.fv
mu=mod$mu.fv
alpha=mod$alpha
epi=1-sqrt(1-4*alpha*mu*(1-mu))
delta=(mu-0.5+0.5*(1-epi))/(1-epi)
a=delta*phi
b=(1-delta)*phi
dbet=dbeta(y,a,b)
v=epi/(epi+(1-epi)*dbet)
ystar=(log(y)-log(1-y)-digamma(a)+digamma(b))

Ie=list()
for(i in 1:length(epi)){
  
  sbet=(((2*alpha*(1-2*mu[i]))/(1-epi[i]))*((v[i]/epi[i])-(1-v[i])/(1-epi[i]))+
          ((1-v[i])*(1-alpha)*(phi[i]/(1-epi[i])^3)*ystar[i]))*gmu(mod)$dmu[i]*X[i,]
  
  skap=-(1-v[i])*(mu[i]*ystar[i]+log(1-y[i])-digamma(b[i])+
                    digamma(phi[i]))*gphi(mod)$dphi[i]*E[i,]
  
  salp=((2*mu[i]*(1-mu[i])/(1-epi[i]))*((v[i]/epi[i])-(1-v[i])/(1-epi[i])))-
    ((phi[i]*mu[i]*(1-mu[i])*(1-2*mu[i]))/((1-epi[i])^3))*ystar[i]
  
  sgam=(((2*alpha*(1-2*mu[i]))/(1-epi[i]))*(v[i]/epi[i]-(1-v[i])/(1-epi[i]))+
    ((1-v[i])*(1-alpha)*phi[i]/(1-epi[i])^3*ystar[i]))*gmu(mod)$dmu[i]*B[i,]-D%*%gamm
  
  sy=as.vector(c(sbet,skap,salp,sgam))
  Ie[[i]]=sy%*%t(sy)
}
Ief=Reduce("+",Ie)

Ieinv=ginv(Ief)
coef=c(bet,kapp,alpha)
EP=sqrt(diag(Ieinv)[1:length(coef)])
VAR=diag(Ieinv)[1:length(coef)]
valorp = 0
wald = 0
for(i in 1:length(coef)){
  wald[i] = wald.test(VAR[i], coef[i], Terms = 1)$result$chi2[1]
  valorp[i] = wald.test(VAR[i], coef[i], Terms = 1)$result$chi2[3]
}

IC<-function(nconf,param, EP){
  lower<- c(param)-qnorm(1-nconf/2)*EP
  upper<- c(param)+qnorm(1-nconf/2)*EP
  obj.out <- list(IC=cbind(cbind(lower,upper)))
  return(obj.out)
}

interval=rbind(IC(1-conf, bet, EP[1:p])$IC,
               IC(1-conf, kapp, EP[(p+1):(s+p)])$IC,
               IC(1-conf, alpha, EP[(s+p+1)])$IC)

coefficients = data.frame(coef, EP,  round(valorp,4), interval)
colnames(coefficients) = c("Estimate","Std.err", "Pr(>|W|)","IC-lower","IC-upper")
return(printCoefmat(as.matrix(coefficients), digits = 4))
}

### Global and local influence

influence = function(mod){

## Hessian
B=mod$mu.coefSmo[[1]]$B
X=mod$mu.x
E=mod$phi.x
nq=ncol(mod$mu.s)
y=mod$y
qj=lambda=0
for(i in 1:nq){
  qj[i]=ncol(mod$mu.coefSmo[[i]]$Bk)
  if(i==1){
    lambda[(1:qj[i])]=mod$mu.coefSmo[[i]]$lambda
  }
  else lambda[(sum(qj[1:(i-1)])+1):(sum(qj[1:(i-1)])+qj[i])]=
      mod$mu.coefSmo[[i]]$lambda
}
D=0.5*lambda*mod$mu.coefSmo[[1]]$D
n=mod$ntol
s=ncol(mod$phi.x)
p=ncol(mod$mu.x)

gamm=mod$mu.coefSmo[[1]]$gamm
bet=mod$mu.coefficients
kapp=mod$phi.coefficients
T1=diag(as.vector(gmu(mod)$dmu),n)
T2=diag(as.vector(gphi(mod)$dphi),n)
phi=mod$phi.fv
mu=mod$mu.fv
alpha=mod$alpha
epi=1-sqrt(1-4*alpha*mu*(1-mu))
delta=(mu-0.5+0.5*(1-epi))/(1-epi)
a=delta*phi
b=(1-delta)*phi
dbet=dbeta(y,a,b)
v=epi/(epi+(1-epi)*dbet)
f1=(2*alpha*(1-2*mu))/(1-epi) 
f2=(v/epi-(1-v)/(1-epi))
ff=f1*f2+(1-v)*(1-alpha)*(phi/((1-epi)^3))*(log(y)-
                      log(1-y)-digamma(a)+digamma(b))
f3=(4*(alpha^2)*(1-2*mu)^2)/((1-epi)^2)
f4=(-v/(epi^2)-(1-v)/((1-epi)^2))
f5=(-(4*alpha)/(1-epi)+(4*alpha^2*(1-2*mu)^2)/((1-epi)^3))
f6=(((1-alpha)*phi^2)/((1-epi)^6))*(trigamma(a)+trigamma(b))
f7=((6*alpha*phi*(1-2*mu))/((1-epi)^5))*(log(y)-log(1-y)-
                      digamma(a)+digamma(b))
Q=diag(as.vector(f3*f4+f2*f5+(1-alpha)*(1-v)*(-f6+f7)*gmu(mod)$dmu^2-
                      ff*gmu(mod)$dmu^3*gmu(mod)$d2mu2),n)
pp=(1-v)*(delta*(log(y)-log(1-y)-digamma(a)+digamma(b))+log(1-y)-
                      digamma(b)+digamma(phi))
S=diag(as.vector(-(1-v)*((1-delta)^2*trigamma(b)+delta^2*trigamma(a)-
                      trigamma(phi))*gphi(mod)$dphi^2-
                      pp*gphi(mod)$dphi^3*gphi(mod)$d2phi2),n)
ff1=(2*mu*(1-mu))/(1-epi)
ff2=(phi*mu*(1-mu)*(1-2*mu))/((1-epi)^3)
d1=ff1*f2-((1-v)*ff2*(log(y)-log(1-y)-digamma(a)+digamma(b)))
d=sum(d1)
f8=(4*mu^2*(1-mu)^2)/((1-epi)^2)
f9=(phi*mu^2*(1-mu)^2*(1-2*mu))/((1-epi)^5)
f10=(phi*(1-2*mu))/(1-epi)
J1=f8*(f4+f2*(1/(1-epi)))-(1-v)*f9*(f10*(trigamma(a)+trigamma(b))+
                      6*(log(y)-log(1-y)-digamma(a)+digamma(b)))
J=sum(J1)
Qstar=diag(as.vector( -(1-v)*(((1-alpha)/((1-epi)^3))*(phi*delta*(trigamma(a)+
                      trigamma(b))-phi*trigamma(b)-
                      (log(y)-log(1-y)-digamma(a)+digamma(b))))*gphi(mod)$dphi*gmu(mod)$dmu),n)
ff3=(4*alpha*mu*(1-mu)*(1-2*mu))/((1-epi)^2)
ff4=2*(1-2*mu)*((1-epi)^(-1)+(2*alpha*mu*(1-mu))/(1-epi)^3)
ff5=((1-alpha)*phi^2*mu*(1-mu)*(1-2*mu))/(1-epi)^6*(trigamma(a)+trigamma(b))
ff6=-phi*((1-epi)^(-3)-(6*(1-alpha)*mu*(1-mu))/(1-epi)^5)
sstar=ff3*f4+f2*ff4+(1-v)*(ff5+(log(y)-log(1-y)-digamma(a)+digamma(b))*ff6)
cstar=(1-v)*(((mu*(1-mu)*(1-2*mu))/(1-epi)^3)*(phi*delta*(trigamma(a)+
                            trigamma(b))-phi*trigamma(b)-(log(y)-
                            log(1-y)-digamma(a)+digamma(b))))

Ubb=t(X)%*%Q%*%X
Ukk=t(E)%*%S%*%E
Ugg=t(B)%*%Q%*%B-D
Uaa=J
Ubk=-t(X)%*%Qstar%*%E
Ugk=-t(B)%*%Qstar%*%E
Ubg=t(X)%*%Q%*%B
Uka=-t(E)%*%T2%*%cstar
Uba=t(X)%*%T1%*%sstar
Uga=t(B)%*%T1%*%sstar
Utt=rbind(cbind(Ubb,Ubg,Ubk,Uba),cbind(t(Ubg),Ugg,Ugk,Uga),
          cbind(t(Ubk),t(Ugk),Ukk,Uka),cbind(t(Uba),t(Uga),t(Uka),Uaa))

## Leverage
M=diag(as.vector((1-v)*(1-alpha)*phi/(1-epi)^3*(mod$y*(1-mod$y))^(-1)),n)
L=diag(as.vector((1-v)*(delta-mod$y)/(mod$y*(1-mod$y))),n)
h=-((1-v)*(phi*mu*(1-mu)*(1-2*mu))/(1-epi)^3)*(mod$y*(1-mod$y))^(-1)
Dmutheta=cbind(T1%*%X,T1%*%B,matrix(0,nrow=n,ncol=(s+1)))
Uthetay=rbind(t(X)%*%T1%*%M,t(B)%*%T1%*%M,t(E)%*%T2%*%L,t(h))
Uttinv=ginv(as.matrix(-Utt))
lev=Dmutheta%*%Uttinv%*%Uthetay

## Cook's Distance
cook=Uti=beti=kappi=gammi=0
for(i in 1:n){
  beti=bet+solve(-Ubb)%*%t(X[-i,])%*%T1[-i,-i]%*%ff[-i]
  gammi=gamm+ginv(as.matrix(-Ugg))%*%t(B[-i,])%*%T1[-i,-i]%*%ff[-i]-D%*%gamm
  kappi=kapp+solve(-Ukk)%*%t(E[-i,])%*%T2[-i,-i]%*%pp[-i]
  alphai=alpha+(-Uaa)^(-1)*sum(d1[-i])
  cook[i]=t(rbind(beti,gammi,kappi,alphai)-as.matrix(c(bet,gamm,kapp,alpha)))%*%
    (-Utt)%*%(rbind(beti,gammi,kappi,alphai)-as.matrix(c(bet,gamm,kapp,alpha)))
}

## Local influence - Case-weight perturbation
deltabc=t(X)%*%T1%*%diag(as.vector(ff),n)
deltagc=t(B)%*%T1%*%diag(as.vector(ff),n)
deltakc=t(E)%*%T2%*%diag(as.vector(pp),n)
deltaac=t(d1)
deltacases=rbind(deltabc,deltagc,deltakc,deltaac)
Zc=t(deltacases)%*%Uttinv%*%deltacases
Cmaxc=abs(eigen(Zc)$vectors[,1])


## Local influence - Response perturbation
deltaby=t(X)%*%T1%*%M
deltagy=t(B)%*%T1%*%M
deltaky=t(E)%*%T2%*%L
deltaay=t(h)
deltay=rbind(deltaby,deltagy,deltaky,deltaay)
Zy=t(deltay)%*%Uttinv%*%deltay
Cmaxy=abs(eigen(Zy)$vectors[,1])/sum(abs(eigen(Zy)$vectors[,1]))


return(list(leverage=lev,
            cook=cook,
            dmaxcw=Cmaxc,
            dmaxy=Cmaxy))
}


### Plot of Leverage
# if you want to highlight a point, use the argument ref to do so

plotlev=function(mod, ref=0.4){
  lev=influence(mod)$leverage
  s1<-qplot(seq_along(diag(lev)),diag(lev),
  geom = "point",label = seq(1,length(diag(lev)),1))+ 
  xlab("Index") + ylab("Generalized Leverage") +
  geom_text_repel(aes(label=ifelse(((diag(lev))> ref),paste0(1:n),""))) +
  theme(
    panel.border = element_blank(),
    panel.grid.major = element_blank(),
    panel.grid.minor = element_blank(),
    panel.background = element_blank(),
    axis.line = element_line(colour = "grey"),
    text=element_text(size=20,family="serif")
  )
  print(s1)
}

### Plot Cook's Distance
plotcook=function(mod){
  cook=influence(mod)$cook
  s1<-qplot(seq_along(cook),cook/sum(cook),
  geom = "point",label = seq(1,length(cook),1))+ 
  xlab("Index") + ylab("Cook's Distance") +
  geom_text_repel(aes(label=ifelse(((cook/sum(cook))==max(cook/sum(cook))),
                    paste0(1:n),""))) +
  theme(
    axis.text.y=element_blank(),
    panel.border = element_blank(),
    panel.grid.major = element_blank(),
    panel.grid.minor = element_blank(),
    panel.background = element_blank(),
    axis.line = element_line(colour = "grey"),
    text=element_text(size=20,family="serif")
  )
  print(s1)
}


### Plot Case-weight perturbation
# if you want to highlight a point, use the argument ref to do so
plotcw=function(mod, ref=0.35){
  Cmaxc=influence(mod)$dmaxcw
  s1<-qplot(seq_along(Cmaxc),Cmaxc,geom = "point",
  label = seq(1,length(Cmaxc),1))+ 
  xlab("Index") + ylab(expression(d[max])) +
  geom_text_repel(aes(label=ifelse(((Cmaxc)> ref),paste0(1:n),""))) +
  theme(
    panel.border = element_blank(),
    panel.grid.major = element_blank(),
    panel.grid.minor = element_blank(),
    panel.background = element_blank(),
    axis.line = element_line(colour = "grey"),
    text=element_text(size=20,family="serif")
  )
  print(s1)
}



# Plot Response perturbation
# if you want to highlight a point, use the argument ref to do so
plotrp=function(mod, ref=0.04){
  Cmaxy=influence(mod)$dmaxy
  s1<-qplot(seq_along(Cmaxy),Cmaxy,geom = "point",
  label = seq(1,length(Cmaxy),1))+ 
  xlab("Index") + ylab(expression(d[max])) +
  geom_text_repel(aes(label=ifelse(((Cmaxy)> ref),paste0(1:n),""))) +
  theme(
    panel.border = element_blank(),
    panel.grid.major = element_blank(),
    panel.grid.minor = element_blank(),
    panel.background = element_blank(),
    axis.line = element_line(colour = "grey"),
    text=element_text(size=20,family="serif")
  )
  print(s1)
}
