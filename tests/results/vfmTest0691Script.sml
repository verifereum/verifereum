open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0691Theory;
val () = new_theory "vfmTest0691";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0691") $ get_result_defs "vfmTestDefs0691";
val () = export_theory_no_docs ();
