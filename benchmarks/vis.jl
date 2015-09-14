## Visualisation of Geometric Benchmarks
using Compose
using Gadfly

function make_point_pairs(lines)
  b = Array(Any, length(lines)-1)
  for i = 1:length(lines) - 1
    j = i + 1
    b[i] = [lines[i][:,1] lines[j][:,1]]
  end
  b
end

pair(x) = x[1],x[2]

function to_lines(points)
  [line([pair(points[:,i]),pair(points[:,i+1])]) for i = 1:(size(points,2)-1)]
end

function make_compose_lines(point_pairs)
  [Compose.line([pair(o[:,1]), pair(o[:,2])]) for o in point_pairs]
end

function get_lines(lines...)
  all_lines = apply(vcat,lines)
  x = map(l->(context(units=UnitBox(0, 0, 10, 10)),
              l,
              linewidth(.5mm),
              stroke(rand_color()),
              fill(nothing)),
          all_lines)
  x
end

function draw_lines(lines...)
  all_lines = apply(vcat,lines)
  x = map(l->(context(units=UnitBox(0, 0, 10, 10)),
              l,
              linewidth(.5mm),
              stroke(rand_color()),
              fill(nothing)),
          all_lines)
  apply(compose,vcat(context(), x))
end
rand_color() = Compose.RGB(rand(),rand(),rand())
