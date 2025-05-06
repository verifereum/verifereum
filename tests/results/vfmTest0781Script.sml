open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0781Theory;
val () = new_theory "vfmTest0781";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0781") $ get_result_defs "vfmTestDefs0781";
val () = export_theory_no_docs ();
