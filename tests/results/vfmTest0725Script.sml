open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0725Theory;
val () = new_theory "vfmTest0725";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0725") $ get_result_defs "vfmTestDefs0725";
val () = export_theory_no_docs ();
