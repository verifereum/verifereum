open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0244Theory;
val () = new_theory "vfmTest0244";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0244") $ get_result_defs "vfmTestDefs0244";
val () = export_theory_no_docs ();
