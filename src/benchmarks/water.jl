## Water filling inference example
## Borrowed from - http://systems.cs.colorado.edu/research/cyberphysical/probabilistic-program-analysis/

using Sigma

# Consider a manipulator that fills containers in an assembly line with a liquid.
# Our goal is to fill each container with some fixed volume.
# However, sensor errors  lead us to an estimate of the volume to be filled that can be off
# and actuator errors ensure that the rate at which the container is being filled can be slightly different from the commanded rate.
# The actuator can be commanded to fill the container in  one of three modes “fast”, “medium” or “slow”.

x = uniform(1,0,1)
y = uniform(0,0,1)

function find_vol()
  volToFill = 20.0
  fast = 10.0
  medium = 3.0
  slow = 1.0
  vol = 0.0
  t = 0.0
  count = 0
  volMeasured = uniform(0.0,0.1)
  println("Whaa", volToFill <= volMeasured)

  @While(volMeasured <= volToFill,
    begin
      count = count + 1;
      ar = @If(volToFill < vol + (0.1*fast),
                    uniform(9.0, 11.0),
                    uniform(0.9, 1.1));
      vol = vol + 0.1 * ar;
      err = uniform(-0.1,0.1);
      volMeasured = vol + err;
     end)
  vol
end


# estimateProb(vol > (1.1 * volToFill));
# estimateProb(vol > (10.0 + volToFill));
# estimateProb(vol > (8.0 + volToFill));
# estimateProb(vol > (6.0 + volToFill));
# estimateProb(vol > (4.0 + volToFill));
# estimateProb(vol > (2.0 + volToFill));
# estimateProb(count <= 3);
# estimateProb(count <= 5);
# estimateProb(count <= 7);
# estimateProb(count <= 9);
# estimateProb(count <= 11);
# estimateProb(count <= 13);
# estimateProb(count <= 15);
# estimateProb(count <= 17);
# estimateProb(count <= 19);
# estimateProb(count >= 20)
