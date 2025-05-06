open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1863Theory;
val () = new_theory "vfmTest1863";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1863") $ get_result_defs "vfmTestDefs1863";
val () = export_theory_no_docs ();
