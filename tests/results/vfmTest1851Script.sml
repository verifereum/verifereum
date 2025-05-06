open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1851Theory;
val () = new_theory "vfmTest1851";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1851") $ get_result_defs "vfmTestDefs1851";
val () = export_theory_no_docs ();
