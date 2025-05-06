open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1681Theory;
val () = new_theory "vfmTest1681";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1681") $ get_result_defs "vfmTestDefs1681";
val () = export_theory_no_docs ();
