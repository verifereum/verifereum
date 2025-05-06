open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1228Theory;
val () = new_theory "vfmTest1228";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1228") $ get_result_defs "vfmTestDefs1228";
val () = export_theory_no_docs ();
