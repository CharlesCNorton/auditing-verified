1. Prove exponential convergence rate: false_assurance alpha k >= 1 - exp(-k*alpha) or tighter
2. Prove no other ps achieves equality in joint_pass_le_uniform besides the uniform case
3. Strict worst-case uniqueness (uniform α is the unique extremal)
4. Heterogeneous per-contest risk limits (per-contest α_i bounds)
5. Unify alpha_r/delta_r with alpha_concrete/delta_concrete (shared definition across Q and rat)
6. Comment the manual ring identity in union_bound (line ~100)
7. Simplify concrete_sharp_89 to avoid the boolean intermediate
8. Consider native_compute for concrete bounds (scales better than vm_compute)
9. Add coqdoc generation and HTML documentation target
