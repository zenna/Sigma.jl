$using Sigma

earthquake = flip(0.001)
burglary = flip(0.01)
alarm = earthquake | burglary
phone_working = @If earthquake flip(0.6) flip(0.6)
mary_wakes = @If (earthquake & alarm) flip(0.8) flip(0.6)
called = mary_wakes & phone_working

prob_sampled(mary_wakes)
cond_prob_sampled(earthquake,called)
