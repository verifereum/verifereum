open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0519Theory;
val () = new_theory "vfmTest0519";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0519") $ get_result_defs "vfmTestDefs0519";
val () = export_theory_no_docs ();
