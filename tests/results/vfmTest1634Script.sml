open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1634Theory;
val () = new_theory "vfmTest1634";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1634") $ get_result_defs "vfmTestDefs1634";
val () = export_theory_no_docs ();
