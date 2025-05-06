open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0560Theory;
val () = new_theory "vfmTest0560";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0560") $ get_result_defs "vfmTestDefs0560";
val () = export_theory_no_docs ();
