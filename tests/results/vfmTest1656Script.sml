open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1656Theory;
val () = new_theory "vfmTest1656";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1656") $ get_result_defs "vfmTestDefs1656";
val () = export_theory_no_docs ();
