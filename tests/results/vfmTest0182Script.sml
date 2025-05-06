open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0182Theory;
val () = new_theory "vfmTest0182";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0182") $ get_result_defs "vfmTestDefs0182";
val () = export_theory_no_docs ();
