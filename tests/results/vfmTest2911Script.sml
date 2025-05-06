open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2911Theory;
val () = new_theory "vfmTest2911";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2911") $ get_result_defs "vfmTestDefs2911";
val () = export_theory_no_docs ();
