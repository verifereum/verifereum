open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0931Theory;
val () = new_theory "vfmTest0931";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0931") $ get_result_defs "vfmTestDefs0931";
val () = export_theory_no_docs ();
