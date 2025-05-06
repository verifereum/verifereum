open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2007Theory;
val () = new_theory "vfmTest2007";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2007") $ get_result_defs "vfmTestDefs2007";
val () = export_theory_no_docs ();
