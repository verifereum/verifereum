open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0294Theory;
val () = new_theory "vfmTest0294";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0294") $ get_result_defs "vfmTestDefs0294";
val () = export_theory_no_docs ();
