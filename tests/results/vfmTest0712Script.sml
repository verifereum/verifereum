open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0712Theory;
val () = new_theory "vfmTest0712";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0712") $ get_result_defs "vfmTestDefs0712";
val () = export_theory_no_docs ();
