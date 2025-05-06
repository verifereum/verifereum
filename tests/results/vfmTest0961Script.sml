open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0961Theory;
val () = new_theory "vfmTest0961";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0961") $ get_result_defs "vfmTestDefs0961";
val () = export_theory_no_docs ();
