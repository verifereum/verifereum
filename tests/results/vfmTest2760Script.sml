open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2760Theory;
val () = new_theory "vfmTest2760";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2760") $ get_result_defs "vfmTestDefs2760";
val () = export_theory_no_docs ();
