open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0501Theory;
val () = new_theory "vfmTest0501";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0501") $ get_result_defs "vfmTestDefs0501";
val () = export_theory_no_docs ();
