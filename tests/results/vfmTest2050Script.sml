open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2050Theory;
val () = new_theory "vfmTest2050";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2050") $ get_result_defs "vfmTestDefs2050";
val () = export_theory_no_docs ();
