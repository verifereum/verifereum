open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2621Theory;
val () = new_theory "vfmTest2621";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2621") $ get_result_defs "vfmTestDefs2621";
val () = export_theory_no_docs ();
