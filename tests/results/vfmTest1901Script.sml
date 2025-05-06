open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1901Theory;
val () = new_theory "vfmTest1901";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1901") $ get_result_defs "vfmTestDefs1901";
val () = export_theory_no_docs ();
