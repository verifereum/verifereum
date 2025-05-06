open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1170Theory;
val () = new_theory "vfmTest1170";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1170") $ get_result_defs "vfmTestDefs1170";
val () = export_theory_no_docs ();
