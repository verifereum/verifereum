open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0292Theory;
val () = new_theory "vfmTest0292";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0292") $ get_result_defs "vfmTestDefs0292";
val () = export_theory_no_docs ();
