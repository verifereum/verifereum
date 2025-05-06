open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1823Theory;
val () = new_theory "vfmTest1823";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1823") $ get_result_defs "vfmTestDefs1823";
val () = export_theory_no_docs ();
