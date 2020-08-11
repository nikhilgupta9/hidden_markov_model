  #CMS-Final project
  #Reading raw data downloaded from kaggle into a dataframe
  #setwd("~/Documents/cms/project")
  df = read.csv('results.csv')
  
  final <- function(df, team, n.iter){
    
  #Loading data into a dataframe  
  df <- subset(df, df$home_team==team | df$away_team==team)
  
  #Data preparation for project
  #Saving a team's goals and result of the match into a vector
  goals <- c()
  result <- c()
  for(i in 1:nrow(df)){
    if(df$home_team[i]==team){
      goals[i] = df$home_goals[i]
      if(df$result[i]=="H"){
        result[i] = "Win"
      } else if(df$result[i]=="D"){
        result[i] = "Draw"
      } else{
        result[i] = "Lose"
      }
    } else {
      goals[i] = df$away_goals[i]
      if(df$result[i]=="A"){
        result[i] = "Win"
      } else if((df$result[i]=="D")){
        result[i] = "Draw"
      } else{
        result[i] = "Lose"
      }
    }
  }
  
  #Converting a Draw into a Lose for simplicity and to reduce the dimensions
  result[result=="Draw"] <- "Lose"
  
  #Converting performance into High, Medium and Low as per number of goals scored
  performance <- c()
  for (i in 1: length(goals)) {
    if(goals[i] > 2){
      performance[i] = "H"
    } else if(goals[i] == 2){
      performance[i] = "M"
    } else{
      performance[i] = "L"
    }
  }
  
  #Calculation of Transition Matrix Probabilities
  ww <- 0
  wl <- 0
  lw <- 0
  ll <- 0
  
  loop <- length(result) - 1
  for (i in 1:loop) {
    temp = paste(result[i], result[i+1], sep = "")
    if(temp=="WinWin"){
      ww <- ww + 1
    } else if(temp=="WinLose"){
      wl <- wl + 1
    } else if(temp=="LoseWin"){
      lw <- lw + 1
    } else{
      ll <- ll + 1
    }
  }
  
  w2w <- round(ww/(ww+wl),4)
  w2l <- 1 - w2w
  l2l <- round(ll/(ll+lw),4)
  l2w <- 1 - l2l
  
  merge <- c()
  for (i in 1:length(performance)) {
    temp = paste(performance[i], result[i], sep = "")
    merge[i] = temp
  }
  x <- table(merge)
  x
  A = matrix(c(w2w,w2l,l2w,l2l),2,2,byrow = T)
  B = matrix(x, 2,3, byrow = T)
  B = B/rowSums(B)
  B <- round(B, 4)
  B
  
  result_encoded <- result
  result_encoded[result_encoded=="Win"] <- "A"
  result_encoded[result_encoded=="Lose"] <- "B"
  
  performance_encoded <- performance
  performance_encoded[performance_encoded=="H"] <- 1
  performance_encoded[performance_encoded=="L"] <- 2
  performance_encoded[performance_encoded=="M"] <- 3
  performance_encoded <- as.numeric(performance_encoded)
  
  newdf <- data.frame(Hidden=result_encoded, Visible=performance_encoded)
  
  #Forward Table calculation
  forward = function(v, a, b, initial_distribution){
    
    T = length(v)
    M = nrow(a)
    alpha = matrix(0, T, M)
    
    alpha[1, ] = initial_distribution*b[, v[1]]
    
    for(t in 2:T){
      tmp = alpha[t-1, ] %*% a
      alpha[t, ] = tmp * b[, v[t]]
    }
    return(alpha)
  }
  
  #Backward Table calculation
  backward = function(v, a, b){
    T = length(v)
    M = nrow(a)
    beta = matrix(1, T, M)
    
    for(t in (T-1):1){
      tmp = as.matrix(beta[t+1, ] * b[, v[t+1]])
      beta[t, ] = t(a %*% tmp)
    }
    return(beta)
  }
  
  #Implementation of Baum-Welch algorithm
  BaumWelch = function(v, a, b, initial_distribution, n.iter){
    
    for(i in 1:n.iter){
      T = length(v)
      M = nrow(a)
      K=ncol(b)
      alpha = forward(v, a, b, initial_distribution)
      beta = backward(v, a, b)
      xi = array(0, dim=c(M, M, T-1))
      
      for(t in 1:T-1){
        denominator = ((alpha[t,] %*% a) * b[,v[t+1]]) %*% matrix(beta[t+1,]) 
        for(s in 1:M){
          numerator = alpha[t,s] * a[s,] * b[,v[t+1]] * beta[t+1,]
          xi[s,,t]=numerator/as.vector(denominator)
        }
      }
      
      
      xi.all.t = rowSums(xi, dims = 2)
      a = xi.all.t/rowSums(xi.all.t)
      
      gamma = apply(xi, c(1, 3), sum)  
      gamma = cbind(gamma, colSums(xi[, , T-1]))
      for(l in 1:K){
        b[, l] = rowSums(gamma[, which(v==l)])
      }
      b = b/rowSums(b)
      
    }
    return(list(a = a, b = b, initial_distribution = initial_distribution))
  }
  
  #Vitervi Algorithm
  Viterbi=function(v,a,b,initial_distribution) {
    
    T = length(v)
    M = nrow(a)
    prev = matrix(0, T-1, M)
    omega = matrix(0, M, T)
    
    omega[, 1] = log(initial_distribution * b[, v[1]])
    for(t in 2:T){
      for(s in 1:M) {
        probs = omega[, t - 1] + log(a[, s]) + log(b[s, v[t]])
        prev[t - 1, s] = which.max(probs)
        omega[s, t] = max(probs)
      }
    }
    
    S = rep(0, T)
    last_state=which.max(omega[,ncol(omega)])
    S[1]=last_state
    
    j=2
    for(i in (T-1):1){
      S[j]=prev[i,last_state] 
      last_state=prev[i,last_state] 
      j=j+1
    }
    
    S[which(S==1)]='A'
    S[which(S==2)]='B'
    
    S=rev(S)
    
    return(S)
    
  }
  
  #Calculation of Pi using Wins and Losses
  A_dist = sum(result_encoded=="A")
  B_dist = sum(result_encoded=="B")
  
  initial_distribution = c(A_dist/length(result_encoded), B_dist/length(result_encoded))
  
  x <- sample(1:3, 38, replace=TRUE)
  
  p <- c(performance_encoded, x)
  myout = BaumWelch(newdf$Visible, A, B, initial_distribution, n.iter)
  myout.hidden=Viterbi(p,myout$a,myout$b,initial_distribution)
  points <- tail(myout.hidden, 38)
  points[points=="B"] = 1
  points[points=="A"] = 3
  points <- as.numeric(points)
  p = paste(team, sum(points), sep = " are: ")
  tail(myout.hidden,38)
  return (paste("Total points for",p,sep = " " ))
}
  final(df, "Manchester United", 100)
  final(df, "Manchester City", 10)
  final(df, "Liverpool", 50)