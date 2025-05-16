###########################################################################
#Program name           : simfunc_data_m.R
#Programmer / Location  : Yoshinori Takeuchi 
#                   (Department of Data Science, Yokohama City University)
#Date                   : 06 January 2025
#Comment                : This program is a modified version of "example1.r" provided by Seaman et al., 2020.
###########################################################################

setwd("/SimulationCode/Monotone")

n.reps <- 1000
result <- matrix(0, n.reps, 3)

for (s in 1:n.reps){
  source("sncstm_m.r")
  library(tibble)
  
  #----------------------
  # Generate the data 
  #----------------------
  
  N = 20000 # Number of individuals in the sample.
  K = 1 # Number of visits (including the baseline visit at time 0).
  M = 10 # Number of imputation for FMI
  Mbasep <- -4 # Intercept of missing probability models 
  EFFECT.MODIFICATION <- F # Flag for allowing treatment effect modification 
  indices=NULL
  useZ=NULL
  EFFECT="harmful" # Effect parameter of time-varying treatments ("harmful", "null", or "beneficial")
  EXPOSETYPE="binomial" # Variable type of treatments ("binomial" or "gaussian")
  MISSTYPE="gaussian" # Variable type of possibly missing time-varying covariates  ("binomial" or "gaussian")
  ESTIMATOR="DR" # Missing data analysis method ("CCA", "IPW", "FMI", or "DR")
  NQUAD=10 # Number of space for the estimation of treatment models
  IPCW=F # Flag for using IPCW
  admincens=NULL
  useAcensor=NULL
  useLcensor=NULL
  EXPONCUM=F # # Flag for calculating cumulative treatment effect on survival probability 
  
  #----------------------
  # The useA matrix
  # Row k+1 of useA is a set of indicators of which previous treatments to include in the GLM for A_k given t>=tau_k.
  # In this example we use only the most recent treatment in the GLM for A_k given t>=tau_k.
  #----------------------
  
  useA <- matrix(F, K+1, K+1)
  
  for (k in 1:K)
    useA[k+1,] <- c(rep(0, k-1), 1, rep(0, K-k+1))
  
  #----------------------
  # The useL matrix
  # Row k+1 of useL is like useA, but indicates which confounders to include, rather than which previous treatments.
  # In this example we include all previous confounders in the GLM for A_k given t>=tau_k.
  #----------------------
  
  useL <- matrix(F, K+1, (K+1)*2)
  
  for (k in 0:K)
    useL[k+1,] <- c(rep(1, k*2+2), rep(0, 2*(K-k)))
  
  # Or instead we could include only the confounders measured at visit k.
  # useL[1,] <- c(1, 1, rep(0, K*2))
  # for (k in 1:K)
  #   useL[k+1,] <- c(rep(0, k*2), 1, 1, rep(0, 2*(K-k)))
  
  
  source("generate_data_m.r")
  data <- data.frame(tim=tim, fail=fail, tau=tau, A=A, V=V, L=L, MLb=MLb, tims=tims, fails=fails)
  
  data <- rownames_to_column(data)
  data$id<- as.integer(data$rowname)
  
  #----------------------
  # Fit the SNCSTM
  #----------------------
  Mimp=F
  Mprob=F
  gamma=-0.2
  
  res <- sncstm_M(data=data, useA=useA, useL=useL, useAcensor=useAcensor, EXPOSETYPE=EXPOSETYPE, MISSTYPE=MISSTYPE,ESTIMATOR=ESTIMATOR,IPCW=IPCW,Mprob=Mprob,Mimp=Mimp,gamma=gamma)
  result[s,] <- cbind(res[1],res[3],res[4])
  }

result <- as.data.frame(result)
names(result) <- c("Psi0_0", "Psi0_1", "Psi1_1")
summary(result)

true <- #-c(0.04,0.01,0.04)
#0
c(0.04,0.01,0.04)

bias <- colMeans(result)-true
bias

esr <- function(x) return(sd(x))
apply(result[,c(1:3)], 2, esr)
esr2 <- apply(result[,c(1:3)], 2, esr)

mse1 <- matrix(rep(true,1000),1000,3,byrow=TRUE)
result2 <- result-mse1
sqrt(colMeans(result2)*colMeans(result2) + esr2*esr2)