open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0452Theory;
val () = new_theory "vfmTest0452";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0452") $ get_result_defs "vfmTestDefs0452";
val () = export_theory_no_docs ();
