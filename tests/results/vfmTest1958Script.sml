open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1958Theory;
val () = new_theory "vfmTest1958";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1958") $ get_result_defs "vfmTestDefs1958";
val () = export_theory_no_docs ();
