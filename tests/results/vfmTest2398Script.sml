open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2398Theory;
val () = new_theory "vfmTest2398";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2398") $ get_result_defs "vfmTestDefs2398";
val () = export_theory_no_docs ();
