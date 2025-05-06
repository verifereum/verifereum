open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0456Theory;
val () = new_theory "vfmTest0456";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0456") $ get_result_defs "vfmTestDefs0456";
val () = export_theory_no_docs ();
