open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0724Theory;
val () = new_theory "vfmTest0724";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0724") $ get_result_defs "vfmTestDefs0724";
val () = export_theory_no_docs ();
