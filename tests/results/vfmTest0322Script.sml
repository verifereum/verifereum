open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0322Theory;
val () = new_theory "vfmTest0322";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0322") $ get_result_defs "vfmTestDefs0322";
val () = export_theory_no_docs ();
