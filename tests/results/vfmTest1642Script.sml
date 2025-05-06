open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1642Theory;
val () = new_theory "vfmTest1642";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1642") $ get_result_defs "vfmTestDefs1642";
val () = export_theory_no_docs ();
