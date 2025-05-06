open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0167Theory;
val () = new_theory "vfmTest0167";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0167") $ get_result_defs "vfmTestDefs0167";
val () = export_theory_no_docs ();
