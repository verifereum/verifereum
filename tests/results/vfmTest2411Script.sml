open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2411Theory;
val () = new_theory "vfmTest2411";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2411") $ get_result_defs "vfmTestDefs2411";
val () = export_theory_no_docs ();
