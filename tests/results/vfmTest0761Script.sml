open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0761Theory;
val () = new_theory "vfmTest0761";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0761") $ get_result_defs "vfmTestDefs0761";
val () = export_theory_no_docs ();
