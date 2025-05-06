open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0594Theory;
val () = new_theory "vfmTest0594";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0594") $ get_result_defs "vfmTestDefs0594";
val () = export_theory_no_docs ();
