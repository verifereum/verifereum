open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2485Theory;
val () = new_theory "vfmTest2485";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2485") $ get_result_defs "vfmTestDefs2485";
val () = export_theory_no_docs ();
