open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2495Theory;
val () = new_theory "vfmTest2495";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2495") $ get_result_defs "vfmTestDefs2495";
val () = export_theory_no_docs ();
