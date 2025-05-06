open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1441Theory;
val () = new_theory "vfmTest1441";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1441") $ get_result_defs "vfmTestDefs1441";
val () = export_theory_no_docs ();
