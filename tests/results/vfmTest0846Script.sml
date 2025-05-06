open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0846Theory;
val () = new_theory "vfmTest0846";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0846") $ get_result_defs "vfmTestDefs0846";
val () = export_theory_no_docs ();
