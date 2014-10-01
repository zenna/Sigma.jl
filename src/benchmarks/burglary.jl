using Sigma

earthquake = flip(1,0.001)
burglary = flip(2,0.01)
alarm = earthquake | burglary
phone_working = @If earthquake flip(3,0.6) flip(4,0.6)
mary_wakes = @If (earthquake & alarm) flip(4,0.8) flip(5,0.6)
called = mary_wakes & phone_working

println("Prob you called is", prob_deep(called))