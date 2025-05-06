open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1760Theory;
val () = new_theory "vfmTest1760";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1760") $ get_result_defs "vfmTestDefs1760";
val () = export_theory_no_docs ();
