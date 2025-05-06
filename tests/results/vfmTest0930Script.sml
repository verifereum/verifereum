open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0930Theory;
val () = new_theory "vfmTest0930";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0930") $ get_result_defs "vfmTestDefs0930";
val () = export_theory_no_docs ();
