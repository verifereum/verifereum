open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0722Theory;
val () = new_theory "vfmTest0722";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0722") $ get_result_defs "vfmTestDefs0722";
val () = export_theory_no_docs ();
