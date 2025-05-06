open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2060Theory;
val () = new_theory "vfmTest2060";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2060") $ get_result_defs "vfmTestDefs2060";
val () = export_theory_no_docs ();
