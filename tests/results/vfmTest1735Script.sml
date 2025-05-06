open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1735Theory;
val () = new_theory "vfmTest1735";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1735") $ get_result_defs "vfmTestDefs1735";
val () = export_theory_no_docs ();
