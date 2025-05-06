open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0078Theory;
val () = new_theory "vfmTest0078";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0078") $ get_result_defs "vfmTestDefs0078";
val () = export_theory_no_docs ();
