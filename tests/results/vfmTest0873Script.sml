open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0873Theory;
val () = new_theory "vfmTest0873";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0873") $ get_result_defs "vfmTestDefs0873";
val () = export_theory_no_docs ();
