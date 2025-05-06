open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0505Theory;
val () = new_theory "vfmTest0505";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0505") $ get_result_defs "vfmTestDefs0505";
val () = export_theory_no_docs ();
