open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0373Theory;
val () = new_theory "vfmTest0373";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0373") $ get_result_defs "vfmTestDefs0373";
val () = export_theory_no_docs ();
