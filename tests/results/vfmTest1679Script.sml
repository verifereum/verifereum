open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1679Theory;
val () = new_theory "vfmTest1679";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1679") $ get_result_defs "vfmTestDefs1679";
val () = export_theory_no_docs ();
