open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2650Theory;
val () = new_theory "vfmTest2650";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2650") $ get_result_defs "vfmTestDefs2650";
val () = export_theory_no_docs ();
