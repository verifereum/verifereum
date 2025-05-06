open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1530Theory;
val () = new_theory "vfmTest1530";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1530") $ get_result_defs "vfmTestDefs1530";
val () = export_theory_no_docs ();
