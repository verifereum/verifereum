open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0783Theory;
val () = new_theory "vfmTest0783";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0783") $ get_result_defs "vfmTestDefs0783";
val () = export_theory_no_docs ();
