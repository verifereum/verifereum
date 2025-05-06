open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0540Theory;
val () = new_theory "vfmTest0540";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0540") $ get_result_defs "vfmTestDefs0540";
val () = export_theory_no_docs ();
