open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2761Theory;
val () = new_theory "vfmTest2761";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2761") $ get_result_defs "vfmTestDefs2761";
val () = export_theory_no_docs ();
