open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0417Theory;
val () = new_theory "vfmTest0417";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0417") $ get_result_defs "vfmTestDefs0417";
val () = export_theory_no_docs ();
