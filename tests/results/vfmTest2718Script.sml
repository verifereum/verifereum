open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2718Theory;
val () = new_theory "vfmTest2718";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2718") $ get_result_defs "vfmTestDefs2718";
val () = export_theory_no_docs ();
