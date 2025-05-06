open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1973Theory;
val () = new_theory "vfmTest1973";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1973") $ get_result_defs "vfmTestDefs1973";
val () = export_theory_no_docs ();
