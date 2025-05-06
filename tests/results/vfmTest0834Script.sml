open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0834Theory;
val () = new_theory "vfmTest0834";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0834") $ get_result_defs "vfmTestDefs0834";
val () = export_theory_no_docs ();
