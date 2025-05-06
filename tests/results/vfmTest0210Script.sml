open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0210Theory;
val () = new_theory "vfmTest0210";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0210") $ get_result_defs "vfmTestDefs0210";
val () = export_theory_no_docs ();
