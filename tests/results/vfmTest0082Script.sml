open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0082Theory;
val () = new_theory "vfmTest0082";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0082") $ get_result_defs "vfmTestDefs0082";
val () = export_theory_no_docs ();
