open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0758Theory;
val () = new_theory "vfmTest0758";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0758") $ get_result_defs "vfmTestDefs0758";
val () = export_theory_no_docs ();
