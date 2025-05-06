open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1921Theory;
val () = new_theory "vfmTest1921";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1921") $ get_result_defs "vfmTestDefs1921";
val () = export_theory_no_docs ();
