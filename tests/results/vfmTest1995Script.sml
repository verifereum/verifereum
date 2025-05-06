open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1995Theory;
val () = new_theory "vfmTest1995";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1995") $ get_result_defs "vfmTestDefs1995";
val () = export_theory_no_docs ();
