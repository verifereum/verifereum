open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0998Theory;
val () = new_theory "vfmTest0998";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0998") $ get_result_defs "vfmTestDefs0998";
val () = export_theory_no_docs ();
