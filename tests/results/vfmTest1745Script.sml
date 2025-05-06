open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1745Theory;
val () = new_theory "vfmTest1745";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1745") $ get_result_defs "vfmTestDefs1745";
val () = export_theory_no_docs ();
