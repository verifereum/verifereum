open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1967Theory;
val () = new_theory "vfmTest1967";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1967") $ get_result_defs "vfmTestDefs1967";
val () = export_theory_no_docs ();
