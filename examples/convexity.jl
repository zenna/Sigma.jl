using Sigma

## Generate convex polygons

# Compute cross product of two vectors
function cross_product(v1::LiftedArray{Float64,1}, v2::LiftedArray{Float64,1})
  (v1[1] * v2[2]) - (v1[2] * v2[1])
end

function convexity_measure(poly::LiftedArray{Float64,2})
  # for all edges
  # remove those points from the poly
  # find the cross
end
#   (for [pair (partition 2 1 (conj poly (first poly)))
#         :let [[p1 p2] pair]]
#     (map #(cross-product
#             (points-to-vec p1 p2)
#             (points-to-vec p2 %))
#       (filter #(and (not= p1 %) (not= p2 %)) poly))))))


#   (sum
#   (map (fn [cross-prods]
#           (let [filtered (filter #(not (zero? %)) cross-prods)]
#             (if (consistent? sign filtered)
#                 0
#                 (max (count (filter neg? filtered)) (count filtered)))))
#   (for [pair (partition 2 1 (conj poly (first poly)))
#         :let [[p1 p2] pair]]
#     (map #(cross-product
#             (points-to-vec p1 p2)
#             (points-to-vec p2 %))
#       (filter #(and (not= p1 %) (not= p2 %)) poly))))))


# Is a polygon convex?
# Works whether poly is simple or complex"
function isconvex(poly::LiftedArray{Float64,2})
  convexity_measure(poly) ≆ 0.0
end

function convex_polygon(npoints::Int)
  XYs = iid(i->uniform(0,1), 2, npoints)
  XYs,isconvex(XYs)
end

## Example
## ======

X,Y = convex_polygon()