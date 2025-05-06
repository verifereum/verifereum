open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0331Theory;
val () = new_theory "vfmTest0331";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0331") $ get_result_defs "vfmTestDefs0331";
val () = export_theory_no_docs ();
