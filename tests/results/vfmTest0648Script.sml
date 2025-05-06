open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0648Theory;
val () = new_theory "vfmTest0648";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0648") $ get_result_defs "vfmTestDefs0648";
val () = export_theory_no_docs ();
