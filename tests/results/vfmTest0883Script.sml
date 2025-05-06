open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0883Theory;
val () = new_theory "vfmTest0883";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0883") $ get_result_defs "vfmTestDefs0883";
val () = export_theory_no_docs ();
