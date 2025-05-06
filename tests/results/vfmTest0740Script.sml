open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0740Theory;
val () = new_theory "vfmTest0740";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0740") $ get_result_defs "vfmTestDefs0740";
val () = export_theory_no_docs ();
