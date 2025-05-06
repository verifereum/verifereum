open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0982Theory;
val () = new_theory "vfmTest0982";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0982") $ get_result_defs "vfmTestDefs0982";
val () = export_theory_no_docs ();
