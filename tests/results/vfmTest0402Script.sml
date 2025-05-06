open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0402Theory;
val () = new_theory "vfmTest0402";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0402") $ get_result_defs "vfmTestDefs0402";
val () = export_theory_no_docs ();
