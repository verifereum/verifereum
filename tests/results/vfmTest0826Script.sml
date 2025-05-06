open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0826Theory;
val () = new_theory "vfmTest0826";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0826") $ get_result_defs "vfmTestDefs0826";
val () = export_theory_no_docs ();
