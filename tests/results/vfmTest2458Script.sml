open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2458Theory;
val () = new_theory "vfmTest2458";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2458") $ get_result_defs "vfmTestDefs2458";
val () = export_theory_no_docs ();
