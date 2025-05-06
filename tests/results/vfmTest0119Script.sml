open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0119Theory;
val () = new_theory "vfmTest0119";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0119") $ get_result_defs "vfmTestDefs0119";
val () = export_theory_no_docs ();
