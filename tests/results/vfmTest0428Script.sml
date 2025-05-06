open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0428Theory;
val () = new_theory "vfmTest0428";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0428") $ get_result_defs "vfmTestDefs0428";
val () = export_theory_no_docs ();
