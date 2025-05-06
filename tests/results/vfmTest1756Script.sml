open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1756Theory;
val () = new_theory "vfmTest1756";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1756") $ get_result_defs "vfmTestDefs1756";
val () = export_theory_no_docs ();
