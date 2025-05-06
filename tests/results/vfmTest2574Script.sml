open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2574Theory;
val () = new_theory "vfmTest2574";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2574") $ get_result_defs "vfmTestDefs2574";
val () = export_theory_no_docs ();
