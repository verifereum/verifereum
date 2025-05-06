open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1425Theory;
val () = new_theory "vfmTest1425";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1425") $ get_result_defs "vfmTestDefs1425";
val () = export_theory_no_docs ();
