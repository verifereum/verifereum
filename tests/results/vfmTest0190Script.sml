open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0190Theory;
val () = new_theory "vfmTest0190";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0190") $ get_result_defs "vfmTestDefs0190";
val () = export_theory_no_docs ();
