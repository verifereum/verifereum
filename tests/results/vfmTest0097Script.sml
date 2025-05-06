open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0097Theory;
val () = new_theory "vfmTest0097";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0097") $ get_result_defs "vfmTestDefs0097";
val () = export_theory_no_docs ();
