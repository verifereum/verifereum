open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0274Theory;
val () = new_theory "vfmTest0274";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0274") $ get_result_defs "vfmTestDefs0274";
val () = export_theory_no_docs ();
