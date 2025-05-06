open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0418Theory;
val () = new_theory "vfmTest0418";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0418") $ get_result_defs "vfmTestDefs0418";
val () = export_theory_no_docs ();
