open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1175Theory;
val () = new_theory "vfmTest1175";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1175") $ get_result_defs "vfmTestDefs1175";
val () = export_theory_no_docs ();
