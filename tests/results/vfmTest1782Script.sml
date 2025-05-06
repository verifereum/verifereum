open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1782Theory;
val () = new_theory "vfmTest1782";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1782") $ get_result_defs "vfmTestDefs1782";
val () = export_theory_no_docs ();
