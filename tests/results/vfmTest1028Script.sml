open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1028Theory;
val () = new_theory "vfmTest1028";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1028") $ get_result_defs "vfmTestDefs1028";
val () = export_theory_no_docs ();
