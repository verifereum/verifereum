open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0939Theory;
val () = new_theory "vfmTest0939";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0939") $ get_result_defs "vfmTestDefs0939";
val () = export_theory_no_docs ();
