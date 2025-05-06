open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2369Theory;
val () = new_theory "vfmTest2369";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2369") $ get_result_defs "vfmTestDefs2369";
val () = export_theory_no_docs ();
