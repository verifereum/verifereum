open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1911Theory;
val () = new_theory "vfmTest1911";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1911") $ get_result_defs "vfmTestDefs1911";
val () = export_theory_no_docs ();
