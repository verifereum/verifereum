open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0975Theory;
val () = new_theory "vfmTest0975";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0975") $ get_result_defs "vfmTestDefs0975";
val () = export_theory_no_docs ();
