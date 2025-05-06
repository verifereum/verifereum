open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1685Theory;
val () = new_theory "vfmTest1685";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1685") $ get_result_defs "vfmTestDefs1685";
val () = export_theory_no_docs ();
