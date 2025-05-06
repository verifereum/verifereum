open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2525Theory;
val () = new_theory "vfmTest2525";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2525") $ get_result_defs "vfmTestDefs2525";
val () = export_theory_no_docs ();
