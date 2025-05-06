open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1869Theory;
val () = new_theory "vfmTest1869";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1869") $ get_result_defs "vfmTestDefs1869";
val () = export_theory_no_docs ();
