open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1093Theory;
val () = new_theory "vfmTest1093";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1093") $ get_result_defs "vfmTestDefs1093";
val () = export_theory_no_docs ();
