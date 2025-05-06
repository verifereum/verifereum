open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2170Theory;
val () = new_theory "vfmTest2170";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2170") $ get_result_defs "vfmTestDefs2170";
val () = export_theory_no_docs ();
