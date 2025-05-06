open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1822Theory;
val () = new_theory "vfmTest1822";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1822") $ get_result_defs "vfmTestDefs1822";
val () = export_theory_no_docs ();
