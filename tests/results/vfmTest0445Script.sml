open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0445Theory;
val () = new_theory "vfmTest0445";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0445") $ get_result_defs "vfmTestDefs0445";
val () = export_theory_no_docs ();
