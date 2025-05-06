open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1892Theory;
val () = new_theory "vfmTest1892";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1892") $ get_result_defs "vfmTestDefs1892";
val () = export_theory_no_docs ();
