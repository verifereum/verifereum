open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0956Theory;
val () = new_theory "vfmTest0956";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0956") $ get_result_defs "vfmTestDefs0956";
val () = export_theory_no_docs ();
