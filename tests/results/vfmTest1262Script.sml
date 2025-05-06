open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1262Theory;
val () = new_theory "vfmTest1262";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1262") $ get_result_defs "vfmTestDefs1262";
val () = export_theory_no_docs ();
