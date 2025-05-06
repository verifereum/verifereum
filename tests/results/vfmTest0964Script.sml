open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0964Theory;
val () = new_theory "vfmTest0964";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0964") $ get_result_defs "vfmTestDefs0964";
val () = export_theory_no_docs ();
