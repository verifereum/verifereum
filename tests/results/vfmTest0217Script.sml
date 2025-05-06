open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0217Theory;
val () = new_theory "vfmTest0217";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0217") $ get_result_defs "vfmTestDefs0217";
val () = export_theory_no_docs ();
