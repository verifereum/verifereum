open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0675Theory;
val () = new_theory "vfmTest0675";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0675") $ get_result_defs "vfmTestDefs0675";
val () = export_theory_no_docs ();
