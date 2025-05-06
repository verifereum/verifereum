open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1575Theory;
val () = new_theory "vfmTest1575";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1575") $ get_result_defs "vfmTestDefs1575";
val () = export_theory_no_docs ();
