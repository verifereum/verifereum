open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0043Theory;
val () = new_theory "vfmTest0043";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0043") $ get_result_defs "vfmTestDefs0043";
val () = export_theory_no_docs ();
