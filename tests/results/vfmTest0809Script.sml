open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0809Theory;
val () = new_theory "vfmTest0809";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0809") $ get_result_defs "vfmTestDefs0809";
val () = export_theory_no_docs ();
