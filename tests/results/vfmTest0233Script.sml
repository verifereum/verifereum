open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0233Theory;
val () = new_theory "vfmTest0233";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0233") $ get_result_defs "vfmTestDefs0233";
val () = export_theory_no_docs ();
