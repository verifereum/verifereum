open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1257Theory;
val () = new_theory "vfmTest1257";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1257") $ get_result_defs "vfmTestDefs1257";
val () = export_theory_no_docs ();
