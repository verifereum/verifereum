open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0686Theory;
val () = new_theory "vfmTest0686";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0686") $ get_result_defs "vfmTestDefs0686";
val () = export_theory_no_docs ();
