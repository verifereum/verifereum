open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0793Theory;
val () = new_theory "vfmTest0793";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0793") $ get_result_defs "vfmTestDefs0793";
val () = export_theory_no_docs ();
