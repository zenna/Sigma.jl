type GiveThisThingAType
  cxx
end

type VarVector
  cxx
end

function post_process(boxes::GiveThisThingAType, nsamples::Int)
  preimage_samples = HyperBox{Float64}[]
  @assert nsamples == icxx"$(boxes.cxx).size();"
  for j = 0:(nsamples-1)
    numdims = icxx"$(boxes.cxx)[$j].size();"
    intervals = Interval{Float64}[Interval(icxx"$(boxes.cxx)[$j][$i].lb();",icxx"$(boxes.cxx)[$j][$i].ub();") for i = 0:(numdims-1)]
    push!(preimage_samples, HyperBox(intervals))
  end
  preimage_samples
end

function pre_tlmh(lmap::LiteralMap, cnf::CMCNF, ω::IBEX.ExprSymbol, aux_vars::VarVector, box, nsamples::Int)
  cxx_boxes = GiveThisThingAType(@cxx sigma::pre_tlmh(lmap.cxx, cnf.cxx, ω.cxx, aux_vars.cxx, box, nsamples))
  post_process(cxx_boxes, nsamples)
end

# Construct an initial box (flattened) for all the variables
function build_init_box(Y::RandVar{Bool}, aux_vars::VarSet)
  omega_numdims = maximum(dims(Y))+1
  aux_numdims = length(aux_vars)
  numdims = omega_numdims + aux_numdims
  box = @cxx ibex::IntervalVector(numdims)
  println("Building initial box with $numdims dimensions")
  for i = 0:(numdims-1)
    # Omega is in [0,1] other variables are unbounded
    if i < omega_numdims
      icxx"$box[$i] = ibex::Interval(0,1);"
    else
      icxx"$box[$i] = ibex::Interval::ALL_REALS;"
    end
  end
  box
end

cxx"""void add_to_sp_vec2(std::vector<std::shared_ptr<ibex::ExprSymbol>> &vec, ExprSymbol &x) {
  std::shared_ptr<ibex::ExprSymbol> new_ptr(&x);
  vec.push_back(new_ptr);
}
"""

function varset_to_varvec(aux_vars::VarSet)
  @show aux_vars
  varvec = VarVector(icxx"std::vector<std::shared_ptr<ibex::ExprSymbol>>();")
  for expr_symbol in aux_vars
    @cxx add_to_sp_vec2(varvec.cxx,expr_symbol.cxx)
  end
  varvec
end

function pre_tlmh(Y::RandVar{Bool}, nsamples::Int)
  cmap, cnf, ω, aux_vars = analyze(Y)
  lmap = to_cxx_lmap(cmap)
  pre_tlmh(lmap, cnf, ω, varset_to_varvec(aux_vars), build_init_box(Y, aux_vars), nsamples)
end
