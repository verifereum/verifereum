open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1887Theory;
val () = new_theory "vfmTest1887";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1887") $ get_result_defs "vfmTestDefs1887";
val () = export_theory_no_docs ();
