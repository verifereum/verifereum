open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0301Theory;
val () = new_theory "vfmTest0301";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0301") $ get_result_defs "vfmTestDefs0301";
val () = export_theory_no_docs ();
