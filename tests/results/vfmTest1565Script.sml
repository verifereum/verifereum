open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1565Theory;
val () = new_theory "vfmTest1565";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1565") $ get_result_defs "vfmTestDefs1565";
val () = export_theory_no_docs ();
