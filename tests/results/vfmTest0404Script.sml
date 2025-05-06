open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0404Theory;
val () = new_theory "vfmTest0404";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0404") $ get_result_defs "vfmTestDefs0404";
val () = export_theory_no_docs ();
