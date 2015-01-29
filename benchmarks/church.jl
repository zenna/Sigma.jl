## Church specific functions

function parse_output(out)
  lines = split(out,"\n")
  compile_time = lines[1][18:end]
  compile_time = int(filter(x->!(x == 'm' || x == 's'),compile_time))
  run_time = lines[2][18:end]
  run_time = int(filter(x->!(x == 'm' || x == 's'),run_time))
  data = lines[3]
  jl_data = split(data[2:end-1]," ")
  p_true = length(filter(s->s=="#t",jl_data))/length(jl_data)
  ["compile_time" => compile_time, "run_time" => run_time, "prob" => p_true]
end

function run_church(program, mhsteps = 10:30:3000)
  [parse_output(readall(`church --timed --program-args $n /home/zenna/sandbox/$program`))
   for n = mhsteps]
end

function run_church(program, n::Integer)
  parse_output(readall(`church --timed --program-args $n /home/zenna/sandbox/$program`))
end
