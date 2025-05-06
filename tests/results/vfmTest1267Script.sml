open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1267Theory;
val () = new_theory "vfmTest1267";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1267") $ get_result_defs "vfmTestDefs1267";
val () = export_theory_no_docs ();
