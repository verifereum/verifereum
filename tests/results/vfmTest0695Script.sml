open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0695Theory;
val () = new_theory "vfmTest0695";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0695") $ get_result_defs "vfmTestDefs0695";
val () = export_theory_no_docs ();
