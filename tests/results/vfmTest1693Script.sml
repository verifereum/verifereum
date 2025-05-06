open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1693Theory;
val () = new_theory "vfmTest1693";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1693") $ get_result_defs "vfmTestDefs1693";
val () = export_theory_no_docs ();
