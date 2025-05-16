###########################################################################
#Program name           : sncstm_m.r
#Programmer / Location  : Yoshinori Takeuchi 
#                   (Department of Data Science, Yokohama City University)
#Date                   : 06 January 2025
#Comment                : This program is a modified version of "sncstm.r" provided by Seaman et al., 2020.
###########################################################################

library(geepack)
library(survival)
library(dplyr)

expit <- function(x) { return( exp(x)/(1+exp(x)) ) }


logit <- function(x) { return( log( x/(1-x) ) ) }


integral.identity <- function(b, del, d, y, tol=0.005) {
  # Calculate the integral of the estimating function when g is the identity
  # link function.  This function is used by sncstm() when METHOD=2.
  integral <- rep(0, length(y))
  if (sum(abs(b))>0)
    integral <- exp(b*y) * (del - d*y) / b - del / b + d * (exp(b*y) - 1) / b^2
  integral[abs(b)<tol] <- ( del*y - d * y^2 / 2 )[abs(b)<tol]
  return(integral)
  } # end of integral.identity()


integral.logit <- function(b, a, e, d, y, tol=0.0001) {
  # Calculate the integral of the estimating function when g is the logit
  # link function.  This function is used by sncstm() when METHOD=2.
  fval <- b+d
  bzero <- abs(b)<tol
  fzero <- abs(fval)<tol
  dzero <- abs(d)<tol
  einfinite <- is.infinite(e)
  # If einfinite=T for a person, then their fitted value of A_k is either
  # 0 or 1.  In that case, it must be equal to their actual value of A_k.
  # Such a person contributes nothing to the estimating equations.
  integral <- rep(0, length(y))
  
  use <- !bzero & !einfinite
  if (sum(use)>0)
    integral[use==T] <- ( a * (exp(b*y)-1) / b )[use==T]
  use <- bzero & !einfinite
  if (sum(use)>0)
    integral[use==T] <- (a*y)[use==T]

  use <- !bzero & !fzero & !dzero & !einfinite
  if (sum(use==T)>0) {
    for (i in (1:length(integral))[use==T]) {
      subtract <- integrate(function(x) {exp(e[i]+fval[i]*x) / (1+exp(e[i]+d[i]*x))}, lower=0, upper=y[i])$value
      integral[i] <- integral[i] - subtract
      }
  }
  
  use <- bzero & !fzero & !dzero & !einfinite
  if (sum(use==T)>0) {
    subtract <- ( log( 1 + exp(e+d*y) ) - log( 1 + exp(e) ) ) / d
    integral[use==T] <- integral[use==T] - subtract[use==T]
  }
  
  use <- fzero & !dzero & !einfinite
  if (sum(use==T)>0) {
    subtract <- y*exp(e) - exp(e) * ( log( 1 + exp(e+d*y) ) - log( 1 + exp(e) ) ) / d
    integral[use==T] <- integral[use==T] - subtract[use==T]
  }
  
  use <- !fzero & dzero & !einfinite
  if (sum(use==T)>0) {
    subtract <- exp(e) * (exp(fval*y)-1) / (fval*(1+exp(e)))
    integral[use==T] <- integral[use==T] - subtract[use==T]
  }

  use <- fzero & dzero & !einfinite
  if (sum(use==T)>0) {
    subtract <- exp(e) * y / (1+exp(e))
    integral[use==T] <- integral[use==T] - subtract[use==T]
    }
    
  return(integral)
} # end of integral.logit()


sncstm_M <- function(data, indices=NULL, useA, useL, useZ=NULL, EXPOSETYPE, MISSTYPE, NQUAD=10, IPCW=F, admincens=NULL, useAcensor=NULL, useLcensor=NULL, EXPONCUM=F, ESTIMATOR="DR", Mprob=F, Mimp=F, gamma=-0.2) {
  # Unless indices is specified, set it equal to 1:N, where N is the number
  # of individuals.  The purpose of the argument `indices' is to enable
  # bootstrapping using the boot() function.
  if (is.null(indices))
    indices <- 1:length(data$tim)

  # Extract the data from the data frame
  tim <- data$tim[indices]
  fail <- data$fail[indices]
  tau <- as.matrix( data[indices, grepl("tau.", names(data))] )
  A <- as.matrix( data[indices, grepl("A.", names(data))] )
  V <- as.matrix( data[indices, grepl("V", names(data))] )
  L <- as.matrix( data[indices, grepl("L.L", names(data))] )
  La <- as.matrix( data[indices, grepl("L.La.", names(data))] )
  Lb <- as.matrix( data[indices, grepl("L.Lb.", names(data))] )
  MLb <- as.matrix( data[indices, grepl("MLb", names(data))] )
  N <- length(indices)
  K <- ncol(A)-1
  if (is.null(admincens))
    admincens <- rep(F, N)
  colnames(A) <- paste("A", 0:K, sep="")

  DIMZ <- 1
  Z <- array(1, c(N, K+1, K+1, 1))
  useZ <- array(diag(1, K+1, K+1), c(K+1, K+1, 1))
  
  psiA <- array(0, c(K+1, K+1, DIMZ))
  psiA.se <- array(0, c(K+1, K+1, DIMZ))
  # psiA will contain the parameter estimates.
  # psiA.se will contain sandwich estimates of the standard errors
  # of these parameter estimates (ignoring uncertainty in the estimation of
  # the weights), but only for Method 1 and even then only when CONSTRAIN=T.
  numer <- array(0, c(K+1, K+1, DIMZ))
  denom <- array(0, c(K+1, K+1, DIMZ, DIMZ))

  # Identify whether visit times are irregular.  To do this, we look at whether
  # or not all the first follow-up visit times are equal, after excluding any
  # first follow-up visits that occur after the failure or censoring time.
  irregular <- F
  
  # Calculate the deltastars. If stabilised weights are used, then Deltastar[j+1,k+1] is A_j minus the fitted values of A_j from a regression of A_j on confounders measured up to time k and treatments measured up to time k-1.  If stabilised weights are not used, Deltastar[j+1,k+1} is just A_j.
  deltastar <- array(0, c(N, K+1, K+1))
  for (j in 1:K)
    for (k in 0:(j-1)) {
      deltastar[, j+1, k+1] <- A[, j+1]        
    }

    # Create pseudo-individuals

    maxpseudolen <- (K+1)*N*(NQUAD+1)
    # pseudolen (the actual number of pseudo-individuals) cannot be greater
    # than this.
    # In this expression it is NQUAD+1, rather than NQUAD.
    pseudoi <- rep(0, maxpseudolen)
    pseudok <- rep(0, maxpseudolen)
    pseudol <- rep(0, maxpseudolen)
    pseudoS <- rep(0, maxpseudolen)
    count <- 0
    
    for (k in 0:K)
      for (l in k:K) {
        use <- tim >= tau[, l+1]
        if (l==k) {
          start <- 0
        } else
          start <- min(tau[use==T, l+1] - tau[use==T, k+1])
        end <- max( pmin(tau[use==T, l+2], tim[use==T]) - tau[use==T, k+1] )
        end <- end - (end - start) / (NQUAD*10000)
        quadpoints <- seq(from=start, to=end, length.out=NQUAD)
        
       for (s in quadpoints) {
          adjustedtim <- tau[, k+1] + s
          use <- tim >= adjustedtim & tau[, l+1] <= adjustedtim & adjustedtim < tau[, l+2]
          nuse <- sum(use)

          if (nuse>0) {
            pseudoi[count+1:nuse] <- (1:N)[use==T]
            pseudok[count+1:nuse] <- k
            pseudol[count+1:nuse] <- l
            pseudoS[count+1:nuse] <- adjustedtim[use==T]
            count <- count + nuse
          }
        } # end of for (s in quadpoints)
        
      } # end of for (k in 0:K) loop

    pseudoi <- pseudoi[1:count]
    pseudok <- pseudok[1:count]
    pseudol <- pseudol[1:count]
    pseudoS <- pseudoS[1:count]
    pseudolen <- count

  censrate.est <- matrix(0, N, K+1)
  # zero corresponds to censoring hazards of zero, which means no inverse
  # probability of censoring weighting.  If IPCW==T, a censoring
  # model will be fitted.
  censrate.stab <- array(0, c(N, K+1, K+1))
  # censrate.stab are the numerators of stabilised weights.

  if (IPCW) {
    # Fit model for censoring

    for (k in 0:K) {
      covars <- cbind(rep(1, N), A[, useAcensor[k+1,]==T], V, La[, useAcensor[k+1,]==T])
      endtim <- pmin(tim, tau[, k+2]) - tau[, k+1]
      cens.event <- tim < tau[, k+2] & !fail & !admincens
      # The !admincens condition is there to exclude administrative
      # censorings.  These are censorings at a time where the probability of
      # censoring given the baseline confounders equals one.
      flag <- try( fit.cens <- survreg(Surv(time=endtim, event=cens.event) ~ covars - 1, dist="exponential", subset=tim >= tau[, k+1]) )
      if (!is.character(flag)) {
        censrate.est[tim >= tau[, k+1], k+1] <- exp( - fit.cens$linear.predictors )
      } else {
        print(paste("WARNING: censoring model could not be fitted at time k=", k, ". Censoring weights for this interval will be set to 1 (i.e. no weighting).", sep=""))
      }
    } # end of for (k in 0:K) loop

    # For the numerator of stabilised weights, fit another model for censoring.
    for (k in 0:K) {
      if (!is.null(useAcensor)) {
        useAstab <- useAcensor[k+1,]
        useAstab[k+1] <- 0
      } else
        useAstab <- NULL
      # If useAcensor specifies that the covariates in the censoring model
      # include A_k, remove this variable from the covariates used in the
      # second censoring model that is used to the numerator of the
      # stabilised weights.
      covars <- cbind(rep(1, N), A[, useAstab==T], V, La[, useAcensor[k+1,]==T])
      for (l in k:K) {
        endtim <- pmin(tim, tau[, l+2]) - tau[, l+1]
        cens.event <- tim < tau[, l+2] & !fail & !admincens
        flag <- try( fit.cens <- survreg(Surv(time=endtim, event=cens.event) ~ covars - 1, dist="exponential", subset=tim >= tau[, l+1]) )
        if (!is.character(flag)) {
          censrate.stab[tim >= tau[, l+1], k+1, l+1] <- exp( - fit.cens$linear.predictors )
        } else {
          print(paste("WARNING: censoring model for numerator of stabilised weights could not be fitted at time (k,l)=(", k, ",", l, "). Censoring weights for this interval will be set to 1 (i.e. no weighting).", sep=""))
        }
      }
    } # end of for (k in 0:K) loop

  } # end of if (IPCW)

  #Estimation of IPMW & FMI
  fails <- as.matrix( data[indices, grepl("fails.", names(data))] )
  tims <- as.matrix( data[indices, grepl("tims.", names(data))] )
  wlist <- mapply(rep,(1:K+1),0)
  milist <- mapply(rep,(1:K+1),0)
  
  for(t in 1:(K+1)){
    wlist[[t]] <- mapply(rep,(1:t),0)
    atrisk <- ifelse(tim >= (t-1),1,0)
    tmpA <- A[atrisk==1,]
    tmpV <- V[atrisk==1,]
    tmpLa <- La[atrisk==1,]
    tmpT <- tims[atrisk==1,(t:(K+1))]
    tmpF <- fails[atrisk==1,(t:(K+1))]
    for (v in 1:t){
      outM <- MLb[atrisk==1,v]
      outMX <- outM
      if (v > 1){
        outM <- outM[MLb[atrisk==1,v-1]==0]
        tmpLb <- Lb[atrisk==1,(1:(v-1))]
        if (Mprob==T){
          tmp <- cbind(1,tmpA,tmpV,tmpLa,tmpLb,Lb[atrisk==1,v])[MLb[atrisk==1,v-1]==0,]
        }else{
          tmp <- cbind(1,tmpA,tmpV,tmpLa,tmpLb,tmpF,tmpT,Lb[atrisk==1,v])[MLb[atrisk==1,v-1]==0,]
        }
      } else {
        if (Mprob==T){
          tmp <- cbind(1,tmpA,tmpV,tmpLa,Lb[atrisk==1,v])
        } else {
          tmp <- cbind(1,tmpA,tmpV,tmpLa,tmpF,tmpT,Lb[atrisk==1,v])
        } 
      }
      beta <- c(rep(0.1,(ncol(tmp)-1)))
      ### Newton - Raphson for nuisance param
      diff <- 10; r <- 1; crit <- 1e-6
      while (diff >= crit )
      {
        MyVector = c(beta , gamma )
        U <- 0; dU <- 0;
        cc.t <- tmp[outM==0,] 
        test <- expit(cc.t%*%MyVector)
        if (v > 1){
          if (Mprob==T){
            tmp2 <- cbind(1,tmpA,tmpV,tmpLa,tmpLb)[outMX==0,]
          } else {
            tmp2 <- cbind(1,tmpA,tmpV,tmpLa,tmpLb,tmpF,tmpT)[outMX==0,]
          }
        } else {
          if (Mprob==T){
            tmp2 <- cbind(1,tmpA,tmpV,tmpLa)[outMX==0,]
          } else {
            tmp2 <- cbind(1,tmpA,tmpV,tmpLa,tmpF,tmpT)[outMX==0,]
          }
        }
        U1_obs <- tmp2[1,]*(1-(1/(1-test[1])))
        for(i in 2:nrow(tmp2)){
          U1_obs <- U1_obs + tmp2[i,]*(1-(1/(1-test[i])))
        }
        if (v > 1){
          if (Mprob==T) {
            tmp3 <- cbind(1,tmpA,tmpV,tmpLa,tmpLb)[outMX==1,]
          } else {
            tmp3 <- cbind(1,tmpA,tmpV,tmpLa,tmpLb,tmpF,tmpT)[outMX==1,]
          }
        } else{
          if (Mprob==T) {
            tmp3 <- cbind(1,tmpA,tmpV,tmpLa)[outMX==1,]
          } else {
            tmp3 <- cbind(1,tmpA,tmpV,tmpLa,tmpF,tmpT)[outMX==1,]
          }
        }
        tmp3 <- na.omit(tmp3)
        U1_miss <- colSums(tmp3)
        U <- U1_obs+U1_miss
        
        test2 <- exp(cc.t%*%MyVector)
        dU1 <- tmp2
        dU1[1,] <- tmp2[1,]*test2[1] 
        for(i in 2:nrow(tmp2)){
          dU1[i,] <- tmp2[i,]*test2[i]
        }
        dU1 <- t(tmp2)%*%dU1
        dU = dU1
        
        diff = max ( abs ( ginv (-dU) %*% U))
        beta = beta - ginv (-dU) %*% U
        
      }
      params = c(beta, gamma)
      estimates.mp <- 1- expit(tmp%*%params)
      estimates.mp[is.na(estimates.mp)] <- 0.5
      if (v > 1){
        wlist[[t]][[v]] <- cbind(data$id[((tim >= (t-1))&(MLb[,(v-1)]==0))],estimates.mp)
      } else {
        wlist[[t]][[v]] <- cbind(data$id[(tim >= (t-1))],estimates.mp)
      }
    }
    
    #frequentist multiple imputation
    milist[[t]] <- mapply(rep,(1:t),0)
    
    for (v in 1:t){
      if (v > 1){
        CC <- data[rowSums(MLb[,(1:v)])==0,]
        CC <- CC[CC$tim>=(t-1),]
      }else{
        CC <- data[MLb[,v]==0,]
        CC <- CC[CC$tim>=(t-1),]
      }
      
      indices3 <- 1:length(CC$tim)
      tim3 <- as.matrix( CC[indices3, grepl("tims.", names(CC))] )
      tim3 <- tim3[,(t:(K+1))]
      fail3 <- as.matrix( CC[indices3, grepl("fails.", names(CC))] )
      fail3 <- fail3[,(t:(K+1))]
      A3 <- as.matrix( CC[indices3, grepl("A.", names(CC))] )
      V3 <- as.matrix( CC[indices3, grepl("V", names(CC))] )
      La3 <- as.matrix( CC[indices3, grepl("L.La.", names(CC))] )
      Lb3 <- as.matrix( CC[indices3, grepl("L.Lb.", names(CC))] )
      MLb3 <- as.matrix( CC[indices3, grepl("MLb.", names(CC))] )
      id3 <- CC$id
      
      tmpA3 <- A3[,]
      tmpV3 <- V3[,]
      tmpLa3 <- La3[,]
      outLb3 <- Lb3[,v]
      
      wLb3 <- exp(outLb3*gamma)
      if (v > 1){
        tmpLb3 <- Lb3[,(1:(v-1))]
        if (Mimp==T){
          imp.model <- geeglm(outLb3~ 1 + tmpA3 + tmpV3 + tmpLa3 + tmpLb3, weights=wLb3, id=id3, family=MISSTYPE)
         } else {
          imp.model <- geeglm(outLb3~ 1 + tim3 + fail3 + tmpA3 + tmpV3 + tmpLa3 + tmpLb3, weights=wLb3, id=id3, family=MISSTYPE)
          }
      } else {
        if (Mimp==T){
          imp.model <- geeglm(outLb3~ 1 + tmpA3 + tmpV3 + tmpLa3, weights=wLb3, id=id3, family=MISSTYPE)
        } else {
          imp.model <- geeglm(outLb3~ 1 + tim3 + fail3 + tmpA3 + tmpV3 + tmpLa3, weights=wLb3, id=id3, family=MISSTYPE)
        }
      }
      
      milist[[t]][[v]] <- imp.model 
      
    }
    
  }
  
  #Data for imputation
  poolx <- mapply(rep,1:M,0)
  pooledx <- data
  pooledx$itr <- 1
  
  for (v in 2:M){
    tmp <- data
    tmp$itr <- v
    poolx[[v]] <- tmp
    pooledx <- rbind(pooledx, poolx[[v]]) 
  }
  
  indices2 <- 1:length(pooledx$tim)
  tim2 <- pooledx$tim
  tims2 <- as.matrix( pooledx[indices2, grepl("tims.", names(pooledx))] )
  fail2 <-pooledx$fail
  fails2 <- as.matrix( pooledx[indices2, grepl("fails.", names(pooledx))] )
  A2 <- as.matrix( pooledx[indices2, grepl("A.", names(pooledx))] )
  V2 <- as.matrix( pooledx[indices2, grepl("V", names(pooledx))] )
  La2 <- as.matrix( pooledx[indices2, grepl("L.La.", names(pooledx))] )
  Lb2 <- as.matrix( pooledx[indices2, grepl("L.Lb.", names(pooledx))] )
  MLb2 <- as.matrix( pooledx[indices2, grepl("MLb.", names(pooledx))] )
  
  if (ESTIMATOR=="FMI"){
    fmilist <- mapply(rep,(1:K+1),0)
  for (t in 1:(K+1)){
    pooled2x <- pooledx[pooledx$tim>=(t-1),]
    indices2x <- 1:length(pooled2x$tim)
    tim2x <- as.matrix( pooled2x[indices2x, grepl("tims.", names(pooled2x))] )
    tim2x <- tim2x[,(t:(K+1))]
    fail2x <- as.matrix( pooled2x[indices2x, grepl("fails.", names(pooled2x))] )
    fail2x <- fail2x[,(t:(K+1))]
    A2x <- as.matrix( pooled2x[indices2x, grepl("A.", names(pooled2x))] )
    V2x <- as.matrix( pooled2x[indices2x, grepl("V", names(pooled2x))] )
    La2x <- as.matrix( pooled2x[indices2x, grepl("L.La.", names(pooled2x))] )
    Lb2x <- as.matrix( pooled2x[indices2x, grepl("L.Lb.", names(pooled2x))] )
    if (t > 1){
      for(b in 1:(t-1)){
        pooled2x <- fmilist[[b]]
        pooled2x <- pooled2x[pooled2x$tim>=(t-1),]
        Lb2x[,b] <- pooled2x$new.Lb
      }
    }
    MLb2x <- as.matrix( pooled2x[indices2x, grepl("MLb.", names(pooled2x))] )
    
    tmpA2x <- A2x[,]
    tmpV2x <- V2x[,]
    tmpLa2x <- La2x[,]
    if (t > 1){
      tmpMLb2x <- MLb2x[,(1:(t-1))]
      tmpLb2x <- Lb2x[,(1:(t-1))]
      histM2x <- MLb2x[,(1:(t-1))]
    }
    if (MISSTYPE=="gaussian"){
    if (t > 1){
      imp.model <-  milist[[t]][[t]]
      if (Mimp==T){
        coef <- imp.model$coef
        var <- as.numeric(summary(imp.model)$dispersion[1])
        Xmatmain <- as.matrix(cbind(1,tmpA2x,tmpV2x,tmpLa2x,tmpLb2x))
      } else {
        coef <- imp.model$coef
        var <- as.numeric(summary(imp.model)$dispersion[1])
        Xmatmain <- as.matrix(cbind(1,tim2x,fail2x,tmpA2x,tmpV2x,tmpLa2x,tmpLb2x))
      }
    } else {
      imp.model <-  milist[[t]][[t]]
      if (Mimp==T){
        coef <- imp.model$coef
        var <- as.numeric(summary(imp.model)$dispersion[1])
        Xmatmain <- as.matrix(cbind(1,tmpA2x,tmpV2x,tmpLa2x))
      } else {
        coef <- imp.model$coef
        var <- as.numeric(summary(imp.model)$dispersion[1])
        Xmatmain <- as.matrix(cbind(1,tim2x,fail2x,tmpA2x,tmpV2x,tmpLa2x))
      }
    }
    
    u.impa1 = apply(Xmatmain, 1, function(x){
      mu <- sum(coef*x)
      new.Lb <- rnorm(1,mean=mu,sd=sqrt(var))
      result <- new.Lb
    })
    }
    if (MISSTYPE=="binomial"){
      if (t > 1){
        imp.model <-  milist[[t]][[t]]
        if (Mimp==T){
          coef <- imp.model$coef
          Xmatmain <- as.matrix(cbind(1,tmpA2x,tmpV2x,tmpLa2x,tmpLb2x))
        } else {
          coef <- imp.model$coef
          Xmatmain <- as.matrix(cbind(1,tim2x,fail2x,tmpA2x,tmpV2x,tmpLa2x,tmpLb2x))
        }
      } else {
        imp.model <-  milist[[t]][[t]]
        if (Mimp==T){
          coef <- imp.model$coef
          Xmatmain <- as.matrix(cbind(1,tmpA2x,tmpV2x,tmpLa2x))
        } else {
          coef <- imp.model$coef
          Xmatmain <- as.matrix(cbind(1,tim2x,fail2x,tmpA2x,tmpV2x,tmpLa2x))
        }
      }
      
      u.impa1 = apply(Xmatmain, 1, function(x){
        mu <- sum(coef*x)
        p <- exp(mu)/(1+exp(mu))
        new.Lb <- rbinom(1,1,p)
        result <- new.Lb
      })
    }
    
    pooled2x$new.Lb <-  u.impa1
    fmilist[[t]] <- pooled2x
    
  }
    
  }
  
  
  for (m in 0:K) {
    for (k in (K-m):0) {
      # Now, estimate psi_k(k+m).
      # So, the order of estimation is that we estimate psi_K(K) then
      # psi_K-1(K-1) then ... then psi_0(0) then psi_K-1(K) then psi_K-1(K-1),
      # ..., then psi_0(1), then ... then psi_0(K).
      
      atrisk <- tim >= tau[, k+m+1]
      # Identify which individuals are at risk at the beginning of interval
      # [k+m, k+m+1).
      fail.in.interval <- tim >= tau[, k+m+1] & tim < tau[, k+m+2] & fail==T
      # Identify which individuals are observed to fail during interval
      # [k+m, k+m+1).

      tim.diff <- pmin(tim, tau[, k+m+2]) - tau[, k+m+1]

      logwei.base <- rep(0, N)
      # logwei.base will be the log weight at the beginning of the (k+m)th
      # interval.  It is zero unless m>1.
      if (m>1)
        for (kindex in (k+1):(k+m-1))
          for (lindex in kindex:(k+m-1)) {
            if (DIMZ==1) {
              Zpsi <- Z[, kindex+1, lindex+1, 1] * psiA[kindex+1, lindex+1, 1]
            } else
              Zpsi <- as.vector(Z[, kindex+1, lindex+1,] %*% psiA[kindex+1, lindex+1,])
            logwei.base <- logwei.base + deltastar[, kindex+1, k+1] * Zpsi * ( tau[, lindex+2] - tau[, lindex+1] )
          }
      
      # Work out the amount that the log weights increase for each unit
      # increase in time.  This is sum.delpsiZ.
      sum.delpsiZ <- rep(0, N)
      if (m>0)
        for (j in (k+1):(k+m)) {
          if (DIMZ==1) {
            sum.delpsiZ <- sum.delpsiZ + deltastar[, j+1, k+1] * Z[, j+1, k+m+1, 1] * psiA[j+1, k+m+1, 1]
          } else
            sum.delpsiZ <- sum.delpsiZ + deltastar[, j+1, k+1] * as.vector(Z[, j+1, k+m+1,] %*% psiA[j+1, k+m+1, ])
        }
      # sum.delpsiZ now equals \sum_{j=k+1}^l \Delta^*_{j(k)} Z_{j(l)}^\top psi_{j(l)} in the notation of the paper.  Remember that \Delta^*_{j(k)} = A_j when STABILISE=F.
      
      logwei.tim <- logwei.base
      # logwei.tim will be the log weight at the earlier of the failure time and
      # the end of the (k+m)th interval.  It is only used by Methods 2 and 3.
      if (m>0)
        logwei.tim <- logwei.tim + sum.delpsiZ * tim.diff
      
      logcenswei.base <- rep(0, N)
      # logcenswei.base will be the log inverse probability of censoring weight
      # at the beginning of the (k+m)th interval.  It is zero unless m>0.
      if (IPCW & m>0)
        for (lindex in k:(k+m-1))
          logcenswei.base <- logcenswei.base + (censrate.est[, lindex+1] - censrate.stab[, k+1, lindex+1]) * ( tau[, lindex+2] - tau[, lindex+1] )

      logcenswei.tim <- rep(0, N)
      if (IPCW)
        logcenswei.tim <- logcenswei.base + (censrate.est[, k+m+1] - censrate.stab[, k+1, k+m+1]) * tim.diff
      # logcenswei.tim is like logwei.tim, but it deals with censoring.  It is
      # only used by Method 2.
      
      use <- pseudok==k & pseudol==k+m
        # These are the pseudo-individuals who will be used by Methods 1 and 2.
        # Set up the covariates (covars and currt) and outcome (Aoutcome) for
        # the GLM that will be fitted to the pseudo-individuals.
        Aoutcome <- A[pseudoi[use==T], k+1]
        currt <- Z[pseudoi[use==T], k+1, k+m+1,] * ( pseudoS[use==T] - tau[pseudoi[use==T], k+m+1] )

        covV <- V[pseudoi[use==T], ]
        
        if (sum(useA[k+1,])>0) {
          covA <- A[pseudoi[use==T], useA[k+1,]==T]
        } else
          covA <- NULL
        if (sum(useL[k+1,])>0) {
          covL <- L[pseudoi[use==T], useL[k+1,]==T]
          covMLb <- MLb[pseudoi[use==T], 1:(k+1)]
        } else
          covL <- NULL        
        
        if (m==0)
          prevt <- NULL

        # covars will be the covariates for the GLM.
        covars <- cbind(covA, covV, covL, covMLb, prevt)

        pseudologwei <- logwei.base[pseudoi]
        # pseudologwei will be the log weight for the pseudo-individuals at
        # the earlier of their failure time and the end of the (k+m)th interval.
        if (m>0)
          pseudologwei <- pseudologwei + sum.delpsiZ[pseudoi] * ( pseudoS - tau[pseudoi, k+m+1] )
        pseudowei.use <- exp(pseudologwei[use==T])

        if (IPCW) {
          # pseudologcenswei will be the log weight for the pseudo-individuals at
          # the earlier of their failure time and the end of the (k+m)th interval.
          pseudologcenswei <- logcenswei.base[pseudoi] + (censrate.est[pseudoi, k+m+1] - censrate.stab[pseudoi, k+1, k+m+1]) * ( pseudoS - tau[pseudoi, k+m+1] )
          pseudocenswei.use <- exp(pseudologcenswei[use==T])
          logcenswei.basex <- logcenswei.base[pseudoi][use==T]
          logcenswei.timx <- logcenswei.tim[pseudoi][use==T]
        } else {
          pseudocenswei.use <- rep(1, sum(use))
        }
        
        pseudoi.use <- pseudoi[use==T]
        if (IPCW) {
        pstmp <- as.data.frame(cbind(Aoutcome, covars, currt, pseudowei.use, pseudocenswei.use, pseudoi.use, logcenswei.basex, logcenswei.timx))
        } else{
        pstmp <- as.data.frame(cbind(Aoutcome, covars, currt, pseudowei.use, pseudocenswei.use, pseudoi.use))
        }
        
        #Complete case
        MLb.cc <- as.matrix( pstmp[grepl("MLb", names(pstmp))] )
        pstmp.CC <- pstmp[MLb.cc[,(k+1)]==0,] 
        mp.Lb <- as.data.frame(wlist[[(k+1)]][[1]])
        names(mp.Lb) <- c("pseudoi.use", "estimates.mp")
        if (k>0){
        for (z in 2:(k+1)){
          mp.Lb.tmp <- as.data.frame(wlist[[(k+1)]][[z]])
          names(mp.Lb.tmp) <- c("pseudoi.use", "estimates.mp2")
          mp.Lb <- inner_join(mp.Lb,mp.Lb.tmp,by=c("pseudoi.use"))
          mp.Lb <- transform(mp.Lb, new.mp.weight=estimates.mp*estimates.mp2)
          mp.Lb <- subset(mp.Lb,select=c("pseudoi.use", "new.mp.weight"))
          names(mp.Lb) <- c("pseudoi.use", "estimates.mp")
        }
        }
        pstmp.CC <- left_join(pstmp.CC,mp.Lb,by=c("pseudoi.use"))
        
        if (ESTIMATOR=="FMI" || ESTIMATOR=="CCA"){
        pstmp.CC <- transform(pstmp.CC, mp.weight=1)
        } else {
        pstmp.CC <- transform(pstmp.CC, mp.weight=(1/estimates.mp))
        }
        
        if (ESTIMATOR=="DR" || ESTIMATOR=="FMI"){  
          #All data
          pool <- mapply(rep,1:M,0)
          if (ESTIMATOR=="FMI"){
            pstmp.MC <- pstmp[MLb.cc[,(k+1)]==1,]
            pooled <- pstmp.MC
          } else {
            pooled <- pstmp
          }
          pooled$itr <- 1
          
          for (v in 2:M){
            if (ESTIMATOR=="FMI"){
              tmp <- pstmp.MC
            } else {
              tmp <- pstmp
            }
            tmp$itr <- v
            pool[[v]] <- tmp
            pooled <- rbind(pooled, pool[[v]]) 
          }
          
          if (ESTIMATOR=="FMI"){
            for (z in 1: (k+1)){
            MLb.MC <- as.matrix( pooled[grepl("MLb", names(pooled))] )
            pooled.MC <- pooled[MLb.MC[,z]==1,]
            pooled.CC <- pooled[MLb.MC[,z]==0,]
            imp.Lb <- fmilist[[z]]
            imp.Lb <- subset(imp.Lb,select=c("id","itr","new.Lb"))
            names(imp.Lb) <- c("pseudoi.use", "itr","imp.Lb")
            pooled.MC <- left_join(pooled.MC,imp.Lb,by=c("pseudoi.use","itr"))
            pooled.MC1 <- pooled.MC[, grep("L.Lb", names(pooled.MC),invert = TRUE)] 
            pooled.MC2 <- pooled.MC[, grepl("L.Lb", names(pooled.MC))]
            if (k > 0){
            pooled.MC2[,z] <- pooled.MC$imp.Lb
            } else {
            pooled.MC2 <- pooled.MC$imp.Lb
            L.Lb0 <-  pooled.MC2
            }
            pooled.MC1 <- pooled.MC1[, grep("imp.Lb", names(pooled.MC1),invert = TRUE)] 
            if (k > 0){
            pooled.MC <- cbind(pooled.MC1,pooled.MC2)
            } else {
            pooled.MC <- cbind(pooled.MC1,L.Lb0)
            }
            pooled <- rbind(pooled.MC,pooled.CC)
            }
            pooled_cum <- pooled
            pooled_cum$mp.weight <- (1/M)
          } else{
          atrisk2 <- ifelse(tim2 >= k,1,0)
          tmpA2 <- A2[atrisk2==1,]
          tmpV2 <- V2[atrisk2==1,]
          tmpLa2 <- La2[atrisk2==1,]
          tmpT2 <- tims2[atrisk2==1,((k+1):(K+1))]
          tmpF2 <- fails2[atrisk2==1,((k+1):(K+1))]
          
          imp.model <- milist[[(k+1)]][[1]]
          coef <- imp.model$coef
          var <- as.numeric(summary(imp.model)$dispersion[1])
          Xmatmain <- as.matrix(cbind(1,tmpT2,tmpF2,tmpA2,tmpV2,tmpLa2))
          
          u.impa1 = apply(Xmatmain, 1, function(x){
            mu <- sum(coef*x)
            new.Lb <- rnorm(1,mean=mu,sd=sqrt(var))
            result <- new.Lb
          })
          
          pooledx2 <- pooledx[atrisk2==1,]
          imp.Lbz <- pooledx2[, grepl("L.Lb", names(pooledx2))]
          imp.Lbz <- imp.Lbz[,(1:(k+1))]
          if (k > 0){
          imp.Lbz[,1] <- u.impa1
          for (w in 2:(k+1)){
            tmpLbx<- imp.Lbz[,1:(w-1)]
            imp.model <- milist[[(k+1)]][[w]]
            coef <- imp.model$coef
            if (MISSTYPE=="gaussian"){
            var <- as.numeric(summary(imp.model)$dispersion[1])
            }
            Xmatmain <- as.matrix(cbind(1,tmpT2,tmpF2,tmpA2,tmpV2,tmpLa2,tmpLbx))
            
            if (MISSTYPE=="gaussian"){
            u.impa1 = apply(Xmatmain, 1, function(x){
              mu <- sum(coef*x)
              new.Lb <- rnorm(1,mean=mu,sd=sqrt(var))
              result <- new.Lb
            })
            }
            if (MISSTYPE=="binomial"){
              u.impa1 <- apply(Xmatmain, 1, function(x){
                mu <- sum(coef*x)
                p <- exp(mu)/(1+exp(mu))
                new.Lb <- rbinom(1,1,p)
                result <- new.Lb
              })
            }
            
            imp.Lbz[,w] <- u.impa1
          }
          } else {
          imp.Lbz <- u.impa1
          }
          
          pooledx2id <- subset(pooledx2,select=c("id","itr"))
          names(pooledx2id) <- c("pseudoi.use", "itr")
          imp.Lbz <- as.data.frame(imp.Lbz)
          colnames(imp.Lbz) <- paste("L.Lb", rep(0:k, each=1), sep="")
          pooled2x.imp.Lb <- cbind(pooledx2id,imp.Lbz)
          
          pooled1 <- pooled[, grep("L.Lb", names(pooled),invert = TRUE)] 
          pooled <- left_join(pooled1,pooled2x.imp.Lb,by=c("pseudoi.use","itr"))
          
          mp.Lb <- as.data.frame(wlist[[(k+1)]][[1]])
          names(mp.Lb) <- c("pseudoi.use", "estimates.mp")
          pooled <- left_join(pooled,mp.Lb,by=c("pseudoi.use"))
          if (k > 0){
          pooled3 <- as.data.frame(cbind(pooled[, grepl("MLb", names(pooled))][,1], pooled[, grepl("estimates.mp", names(pooled))]))
          } else {
          pooled3 <- as.data.frame(cbind(pooled[, grepl("MLb", names(pooled))], pooled[, grepl("estimates.mp", names(pooled))]))
          }
          names(pooled3) <- c("MLb", "estimates.mp")
          pooled3[is.na(pooled3)] <- 0.5
          if (ESTIMATOR=="FMI"){
            pooled3 <- transform(pooled3, mp.weight=(1/estimates.mp))
          } else {
            pooled3 <- transform(pooled3, mp.weight=((1-((1-MLb)/estimates.mp))/M))
          }
          pooled$mp.weight <- pooled3$mp.weight
          pooled <- pooled[, grep("estimates.mp", names(pooled),invert = TRUE)] 
          
          pooled_cum <- pooled
        
        if (k > 0){
         for (z in 2:(k+1)){
           if (ESTIMATOR != "IPW"){      
               #All data
               pool <- mapply(rep,1:M,0)
               if (ESTIMATOR=="FMI"){
                 pstmp.MC <- pstmp[MLb.cc[,z]==1,]
                 pooled <- pstmp.MC
               } else {
                 pooled <- pstmp
               }
               pooled$itr <- 1
               
               for (v in 2:M){
                 if (ESTIMATOR=="FMI"){
                   tmp <- pstmp.MC
                 } else {
                   tmp <- pstmp
                 }
                 tmp$itr <- v
                 pool[[v]] <- tmp
                 pooled <- rbind(pooled, pool[[v]]) 
               }
               
               pooled <- pooled[tim>(k-1),]
               
               atrisk2 <- ifelse(tim2 >= k,1,0)
               tmpA2 <- A2[atrisk2==1,]
               tmpV2 <- V2[atrisk2==1,]
               tmpLa2 <- La2[atrisk2==1,]
               tmpT2 <- tims2[atrisk2==1,((k+1):(K+1))]
               tmpF2 <- fails2[atrisk2==1,((k+1):(K+1))]
               
               imp.model <- milist[[(k+1)]][[1]]
               coef <- imp.model$coef
               if (MISSTYPE=="gaussian"){
               var <- as.numeric(summary(imp.model)$dispersion[1])
               }
               Xmatmain <- as.matrix(cbind(1,tmpT2,tmpF2,tmpA2,tmpV2,tmpLa2))[MLb2[atrisk2==1,z-1]==0,]
               
               if (MISSTYPE=="gaussian"){
               u.impa1 = apply(Xmatmain, 1, function(x){
                 mu <- sum(coef*x)
                 new.Lb <- rnorm(1,mean=mu,sd=sqrt(var))
                 result <- new.Lb
               })
               }
               if (MISSTYPE=="binomial"){
                 u.impa1 <- apply(Xmatmain, 1, function(x){
                   mu <- sum(coef*x)
                   p <- exp(mu)/(1+exp(mu))
                   new.Lb <- rbinom(1,1,p)
                   result <- new.Lb
                 })
               }
               
               pooledx2 <- pooledx[atrisk2==1,]
               pooledx2 <- pooledx2[MLb2[atrisk2==1,z-1]==0,]
               imp.Lbz <- pooledx2[, grepl("L.Lb", names(pooledx2))]
               imp.Lbz <- imp.Lbz[,(1:(k+1))]
               imp.Lbz[,z] <- u.impa1
               
               for (w in 2:(k+1)){
                 tmpLbx<- imp.Lbz[,1:(w-1)]
                 imp.model <- milist[[(k+1)]][[w]]
                 coef <- imp.model$coef
                 if (MISSTYPE=="gaussian"){
                 var <- as.numeric(summary(imp.model)$dispersion[1])
                 }
                 Xmatmainp <- as.matrix(cbind(1,tmpT2,tmpF2,tmpA2,tmpV2,tmpLa2))[MLb2[atrisk2==1,z-1]==0,]
                 Xmatmain <- as.matrix(cbind(Xmatmainp,tmpLbx))
                 
                 if (MISSTYPE=="gaussian"){
                 u.impa1 = apply(Xmatmain, 1, function(x){
                   mu <- sum(coef*x)
                   new.Lb <- rnorm(1,mean=mu,sd=sqrt(var))
                   result <- new.Lb
                 })
                 }
                 if (MISSTYPE=="binomial"){
                   u.impa1 <- apply(Xmatmain, 1, function(x){
                     mu <- sum(coef*x)
                     p <- exp(mu)/(1+exp(mu))
                     new.Lb <- rbinom(1,1,p)
                     result <- new.Lb
                   })
                 }
                 
                 imp.Lbz[,w] <- u.impa1
               }
               
               pooledx2id <- subset(pooledx2,select=c("id","itr"))
               names(pooledx2id) <- c("pseudoi.use", "itr")
               imp.Lbz <- as.data.frame(imp.Lbz)
               colnames(imp.Lbz) <- paste("L.Lb", rep(0:k, each=1), sep="")
               pooled2x.imp.Lb <- cbind(pooledx2id,imp.Lbz)
               
               pooled1 <- pooled[, grep("L.Lb", names(pooled),invert = TRUE)] 
               pooled <- inner_join(pooled1,pooled2x.imp.Lb,by=c("pseudoi.use","itr"))#left_join?ł͂Ȃ????Ƃɒ???
               
               mp.Lb <- as.data.frame(wlist[[(k+1)]][[1]])
               names(mp.Lb) <- c("pseudoi.use", "estimates.mp")
               if (z>2){
                 for (a in 2:(z-1)){
                   mp.Lb.tmp <- as.data.frame(wlist[[(k+1)]][[a]])
                   names(mp.Lb.tmp) <- c("pseudoi.use", "estimates.mp2")
                   mp.Lb <- inner_join(mp.Lb,mp.Lb.tmp,by=c("pseudoi.use"))
                   mp.Lb <- transform(mp.Lb, new.mp.weight=estimates.mp*estimates.mp2)
                   mp.Lb <- subset(mp.Lb,select=c("pseudoi.use", "new.mp.weight"))
                   names(mp.Lb) <- c("pseudoi.use", "estimates.mp")
                 }
               }
               
               mp.Lb.tmp <- as.data.frame(wlist[[(k+1)]][[(z)]])
               names(mp.Lb.tmp) <- c("pseudoi.use", "estimates.mp2")
               mp.Lb <- inner_join(mp.Lb,mp.Lb.tmp,by=c("pseudoi.use"))
               pooled <- left_join(pooled,mp.Lb,by=c("pseudoi.use"))
               pooled3 <- as.data.frame(cbind(pooled[, grepl("MLb", names(pooled))][,((z-1):(z))], pooled[, grepl("estimates.mp", names(pooled))]))
               names(pooled3) <- c("MLb1","MLb2","estimates.mp1","estimates.mp2")
               pooled3[is.na(pooled3)] <- 0.5
               if (ESTIMATOR=="FMI"){
                 pooled3 <- transform(pooled3, mp.weight=(1/M))
               } else {
                 pooled3 <- transform(pooled3, mp.weight=(((1-MLb1)/estimates.mp1)*(1-((1-MLb2)/estimates.mp2))/M))
               }
               pooled$mp.weight <- pooled3$mp.weight
               pooled <- pooled[, grep("estimates.mp", names(pooled),invert = TRUE)] 
               pooled_cum <- rbind(pooled,pooled_cum)
             }
         }
        }
          }
        }
        pstmp.CC$itr <- 0
        pstmp.CC <- pstmp.CC[, grep("estimates.mp", names(pstmp.CC),invert = TRUE)] 
        if (ESTIMATOR=="IPW" || ESTIMATOR=="CCA"){
        pstmp2 <- pstmp.CC
        } else {
        pstmp2 <- rbind(pstmp.CC,pooled_cum)
        }
        pstmp2 <- transform(pstmp2, weight=pseudowei.use*pseudocenswei.use*mp.weight)
        
        Y <- pstmp2$Aoutcome
        if (k > 0){
        X <- as.matrix(cbind(1,pstmp2[, grepl("covA|A[^o]", names(pstmp2))],pstmp2[, grepl("V", names(pstmp2))],pstmp2[, grepl("L.La.", names(pstmp2))],pstmp2[, grepl("L.Lb.", names(pstmp2))],pstmp2[, grepl("currt", names(pstmp2))]))
        } else {
        X <- as.matrix(cbind(1,pstmp2[, grepl("covA|A[^o]", names(pstmp2))],pstmp2[, grepl("V", names(pstmp2))],pstmp2[, grepl("L.La.", names(pstmp2))],pstmp2[, grepl("L.Lb.", names(pstmp2))],pstmp2[, grepl("currt", names(pstmp2))]))
        }
        W <- pstmp2$weight
        
        alpha <- c(rep(0.1,(ncol(X))))
        diff <- 10; r <- 1; crit <- 1e-6
        if (EXPOSETYPE=="gaussian"){
        ### Newton - Raphson 
        while (diff >= crit )
        {
          MyVector = c(alpha)
          test <- Y-X%*%MyVector
          U <- 0; dU <- 0;
          U1 <- (t(X[1,])*W[1])*test[1]
          for(i in 2:nrow(X)){
            U1 <- U1 + (t(X[i,])*W[i])*test[i]
          }
          U<-U1
          
          Xtmp<-X
          Xtmp[1,] <-X[1,]*W[1] 
          for(i in 2:nrow(X)){
            Xtmp[i,] <-X[i,]*W[i]
          }
          dU1 <- t(X)%*%Xtmp
          dU= dU1
          
          diff = max ( abs ( ginv (-dU) %*% t(U)))
          alpha = alpha - t(ginv (-dU) %*% t(U))
          
        }
        }
        if (EXPOSETYPE=="binomial"){
          ### Newton - Raphson 
          while (diff >= crit )
          {
            MyVector = c(alpha)
            test <- Y-expit(X%*%MyVector)
            U <- 0; dU <- 0;
            U1 <- (t(X[1,])*W[1])*test[1]
            for(i in 2:nrow(X)){
              U1 <- U1 + (t(X[i,])*W[i])*test[i]
            }
            U<-U1
            
            test2 <- exp(-X%*%MyVector)
            Xtmp<-X
            Xtmp[1,] <- (X[1,]*W[1]*test2[1,])/((1+test2[1,])^2)
            for(i in 2:nrow(X)){
              Xtmp[i,] <-(X[i,]*W[i]*test2[i,])/((1+test2[i,])^2)
            }
            dU1 <- t(X)%*%Xtmp
            dU= dU1
            
            diff = max ( abs ( ginv (-dU) %*% t(U)))
            alpha = alpha - t(ginv (-dU) %*% t(U))
            
          }
        }
          
        fitA.tim <- t(alpha)
       
      data3 <- pstmp2[pstmp2$currt==0,] 
      atf <- cbind(data[, grepl("id", names(data))],data$tim,data$fail,data[, grepl("tau.", names(data))],data[, grepl("A", names(data))])
      names(atf) <- c("id","tim","fail","tau.0","tau.1","tau.2","A.A0","A.A1")
      data3 <- left_join(data3,atf,by=c("pseudoi.use"="id"))
      tim4 <- as.matrix(data3$tim)
      tau4 <- as.matrix( data3[, grepl("tau.", names(data3))] )
      tim.diff2 <- pmin(tim4, tau4[, k+m+2]) - tau4[, k+m+1]
      fail4 <- data3$fail
      A4 <- as.matrix( data3[, grepl("A.A.", names(data3))] )
      V4 <- as.matrix( data3[, grepl("V", names(data3))] )
      L4 <- as.matrix( data3[, grepl("L.L", names(data3))] )
      MLb4 <- as.matrix( data3[, grepl("MLb.", names(data3))] )
      dlweight <- as.matrix(data3$mp.weight)
      Z2 <- array(1, c(nrow(data3), K+1, K+1, 1))
      
            deltastar2 <- array(0, c(nrow(data3), K+1, K+1))
      for (a in 1:K)
        for (b in 0:(a-1)) {
          deltastar2[, a+1, b+1] <- A4[, a+1]        
        }
      
            logwei.base2 <- rep(0, nrow(data3))
      # logwei.base will be the log weight at the beginning of the (k+m)th
      # interval.  It is zero unless m>1.
      if (m>1)
        for (kindex in (k+1):(k+m-1))
          for (lindex in kindex:(k+m-1)) {
            if (DIMZ==1) {
              Zpsi <- Z2[, kindex+1, lindex+1, 1] * psiA[kindex+1, lindex+1, 1]
            } else
              Zpsi <- as.vector(Z2[, kindex+1, lindex+1,] %*% psiA[kindex+1, lindex+1,])
            logwei.base2 <- logwei.base2 + deltastar2[, kindex+1, k+1] * Zpsi * ( tau4[, lindex+2] - tau4[, lindex+1] )
          }

     

      # Work out the amount that the log weights increase for each unit
      # increase in time.  This is sum.delpsiZ.
      sum.delpsiZ2 <- rep(0, nrow(data3))
      if (m>0)
        for (j in (k+1):(k+m)) {
          if (DIMZ==1) {
            sum.delpsiZ2 <- sum.delpsiZ2 + deltastar2[, j+1, k+1] * Z2[, j+1, k+m+1, 1] * psiA[j+1, k+m+1, 1]
          } else
            sum.delpsiZ2 <- sum.delpsiZ2 + deltastar2[, j+1, k+1] * as.vector(Z2[, j+1, k+m+1,] %*% psiA[j+1, k+m+1, ])
        }
      # sum.delpsiZ now equals \sum_{j=k+1}^l \Delta^*_{j(k)} Z_{j(l)}^\top psi_{j(l)} in the notation of the paper.  Remember that \Delta^*_{j(k)} = A_j when STABILISE=F.
      
      logwei.tim2 <- logwei.base2
      # logwei.tim will be the log weight at the earlier of the failure time and
      # the end of the (k+m)th interval.  It is only used by Methods 2 and 3.
      if (m>0)
        logwei.tim2 <- logwei.tim2 + sum.delpsiZ2 * tim.diff2
      
      logcenswei.base2 <- rep(0, nrow(data3))
      logcenswei.tim2 <- rep(0, nrow(data3))
      if (IPCW) {
        logcenswei.base2 <- data3$logcenswei.basex
        logcenswei.tim2 <- data3$logcenswei.timx
      }
      
      atrisk4 <- tim4 >= tau4[, k+m+1]
      fail.in.interval4 <- tim4 >= tau4[, k+m+1] & tim4 < tau4[, k+m+2] & fail4==T
      
      # Start setting up the covariates
        covV4 <- V4
        if (sum(useA[k+1,])>0) {
          covA4 <-  A4[, useA[k+1,]==T]
        } else
          covA4 <- NULL
        if (sum(useL[k+1,])>0) {
          covL4 <- as.data.frame(L4)
        } else
          covL4 <- NULL        

        if (m>0 & irregular) {
          prevt <- matrix(0, N, m*DIMZ)
          for (zj in 1:DIMZ)
            prevt[, (zj-1)*m+1:m] <- Z[, k+1, (k+1):(k+m), zj] * ( tau[, (k+2):(k+m+1)] - tau[, (k+1):(k+m)] )
        } else
          prevt4 <- NULL

        if (k>0){
        covars4 <- cbind(1, covA4, covV4, as.matrix(covL4[, grepl("L.La", names(covL4))]), as.matrix(covL4[, grepl("L.Lb", names(covL4))]), prevt4)
        } else {
        covars4 <- cbind(1, covA4, covV4, as.matrix(covL4[, grepl("L.La", names(covL4))]), as.matrix(covL4[, grepl("L.Lb", names(covL4))]), prevt4)
        }  

        # delta.base will be the value of delta at the beginning of the (k+m)th interval.
        # delta.tim will be the value of delta at the earlier of the failure/censoring
        # time and the end of the (k+m)th interval.
        if (EXPOSETYPE=="gaussian"){
          delta.base <- A4[, k+1] - cbind(covars4,0)%*%fitA.tim
          delta.tim <- A4[, k+1] - cbind(covars4,tim.diff2)%*%fitA.tim
        }
        if (EXPOSETYPE=="binomial"){
          delta.base <- A4[, k+1] - expit(cbind(covars4,0)%*%fitA.tim)
          delta.tim <- A4[, k+1] - expit(cbind(covars4,tim.diff2)%*%fitA.tim)
        }
        
        if (DIMZ==1) {
          Z.currtcoeff <- Z2[, k+1, k+m+1, 1] * fitA.tim[nrow(fitA.tim)]
            #fitA.tim$coefficients["currt"]
        } else
          Z.currtcoeff <- as.vector(Z[, k+1, k+m+1,] %*% fitA.tim$coefficients[paste("currt", 1:DIMZ, sep="")])
            
      deltastarZpsi.km2 <- rep(0, nrow(data3))
        if (m>0) {
          if (DIMZ==1)
            Zpsi.km2 <- Z2[, k+m+1, k+m+1, 1] * psiA[k+m+1, k+m+1,]
          if (DIMZ>1)
            Zpsi.km2 <- as.vector(Z2[, k+m+1, k+m+1,] %*% psiA[k+m+1, k+m+1,])
          deltastarZpsi.km2 <- deltastar2[, k+m+1, k+1] * Zpsi.km2
        }
        
        # integ will be the integral in the numerator and denominator of the
        # formula for the estimator of psi.
        
        censrate.est2 <-  matrix(0, nrow=nrow(data3), ncol=K+1)
        censrate.stab2 <- array(0, c(nrow(data3), K+1, K+1))
        
        if (IPCW) {
          censrate.estx <- censrate.est
          censrate.estx <- rownames_to_column(as.data.frame(censrate.estx))
          censrate.estx$id<- as.integer(censrate.estx$rowname)
          for (c in 1:K+1){
            data3 <- left_join(data3,censrate.estx,by=c("pseudoi.use"="id"))
            ncolz <- ncol(data3)
            censrate.est2[,c]<-data3[,ncolz-((K+1)-c)]
          }
          
          for (c1 in 1:K+1){
            for (c2 in 1:K+1){
              censrate.stabx <- censrate.stab[,c1,c2]
              censrate.stabx <- rownames_to_column(as.data.frame(censrate.stabx))
              censrate.stabx$id<- as.integer(censrate.stabx$rowname)
              data3 <- left_join(data3,censrate.stabx,by=c("pseudoi.use"="id"))
              ncolz <- ncol(data3)
              censrate.stab2[,c1,c2]<-data3[,ncolz]
            }
          }
        }
       
        if (EXPOSETYPE=="gaussian")
          integ <- integral.identity(b=deltastarZpsi.km2 + censrate.est2[, k+m+1] - censrate.stab2[, k+1, k+m+1], del=delta.base, d=Z.currtcoeff, y=tim.diff2)
        if (EXPOSETYPE=="binomial")
          integ <- integral.logit(b=deltastarZpsi.km2 + censrate.est2[, k+m+1] - censrate.stab2[, k+1, k+m+1], a=A4[,k+1], e=logit(A4[,k+1]-delta.base), d=Z.currtcoeff, y=tim.diff2)
        # Note that A[,k+1]-delta.base is the same as the expectation of
        # A[,k+1] at the lth visit time.
        
        integ <- integ * exp(logwei.base2) * exp(logcenswei.base2)
        # integ now equals \int_{S_l}^{S_{l+1}} R(t) w_k(t) w_k^{CS}(t) \Delta_k(t) dt in the notation of the paper.
    
        # "ind.woz" in the three variables below stands for individual contribution without including Z.
        numer1.ind.woz <- rep(0, nrow(data3))
        numer2.ind.woz <- rep(0, nrow(data3))
        denom.ind.woz <- rep(0, nrow(data3))

        # numer1 is the first part of the numerator in the estimator of psiA
        # (i.e. the part that involves dN(t)).
        numer1.ind.woz[fail.in.interval4] <- ( exp(logwei.tim2 + logcenswei.tim2) * delta.tim * dlweight)[fail.in.interval4==T]
        numer1 <- rep(0, DIMZ)
        for (zj in 1:DIMZ)
          numer1[zj] <- sum( (numer1.ind.woz * Z2[, k+1, k+m+1, zj])[fail.in.interval4==T] )

        # numer2 is (minus) the second part of the numerator in the estimator of psiA.
        if (m>0)
          numer2.ind.woz[atrisk4==T] <- ( sum.delpsiZ2 * integ * dlweight)[atrisk4==T]
        numer2 <- rep(0, DIMZ)
        for (zj in 1:DIMZ)
          numer2[zj] <- sum(numer2.ind.woz[atrisk4==T] * Z2[atrisk4==T, k+1, k+m+1, zj])

        if (DIMZ==1) {
          numer[k+1, k+m+1, 1] <- numer1 - numer2
        } else
          numer[k+1, k+m+1,] <- numer1 - numer2

        # denom is the denominator in the estimator of psiA.
        denom.ind.woz[atrisk4==T] <- (integ * delta.base * dlweight)[atrisk4==T]          
        if (DIMZ==1) {
          denom[k+1, k+m+1, 1, 1] <- sum( (denom.ind.woz * Z2[, k+1, k+m+1, 1]^2)[atrisk4==T] )
          denom.inverse <- 1 / denom[k+1, k+m+1, 1, 1]
          psiA[k+1, k+m+1, 1] <- numer[k+1, k+m+1, 1] / denom[k+1, k+m+1, 1, 1]
        }
    
    } # end of for (k in (K-m):0) loop

  }  # end of for (m in 0:(K-k)) loop
  
  if (EXPONCUM) {
    # Now add to the psiA results, estimates of cumulative causal effects and exponentials of cumulative causal effects.
    psiA.extra <- array(0, c(K+1, K+1, DIMZ*3))
    psiA.extra[,, 1:DIMZ] <- psiA[,, 1:DIMZ]
    for (v in 1:DIMZ) {
      psiA.extra[,, DIMZ+v] <- t(apply(psiA.extra[,, v], 1, cumsum))
      psiA.extra[,, DIMZ*2+v] <- exp( psiA.extra[,, DIMZ+v] )
    }
    psiA <- psiA.extra
  } # end of if (EXPONCUM)
  
  return(psiA)
} # end of sncstm_m() function