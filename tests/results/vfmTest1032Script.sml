open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1032Theory;
val () = new_theory "vfmTest1032";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1032") $ get_result_defs "vfmTestDefs1032";
val () = export_theory_no_docs ();
