open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1811Theory;
val () = new_theory "vfmTest1811";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1811") $ get_result_defs "vfmTestDefs1811";
val () = export_theory_no_docs ();
