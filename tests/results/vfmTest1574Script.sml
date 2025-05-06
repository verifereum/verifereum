open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1574Theory;
val () = new_theory "vfmTest1574";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1574") $ get_result_defs "vfmTestDefs1574";
val () = export_theory_no_docs ();
