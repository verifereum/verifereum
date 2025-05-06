open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1295Theory;
val () = new_theory "vfmTest1295";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1295") $ get_result_defs "vfmTestDefs1295";
val () = export_theory_no_docs ();
