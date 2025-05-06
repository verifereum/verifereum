open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0843Theory;
val () = new_theory "vfmTest0843";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0843") $ get_result_defs "vfmTestDefs0843";
val () = export_theory_no_docs ();
