open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0211Theory;
val () = new_theory "vfmTest0211";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0211") $ get_result_defs "vfmTestDefs0211";
val () = export_theory_no_docs ();
