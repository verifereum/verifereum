open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0487Theory;
val () = new_theory "vfmTest0487";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0487") $ get_result_defs "vfmTestDefs0487";
val () = export_theory_no_docs ();
