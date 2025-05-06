open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0134Theory;
val () = new_theory "vfmTest0134";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0134") $ get_result_defs "vfmTestDefs0134";
val () = export_theory_no_docs ();
