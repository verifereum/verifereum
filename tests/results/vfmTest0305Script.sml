open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0305Theory;
val () = new_theory "vfmTest0305";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0305") $ get_result_defs "vfmTestDefs0305";
val () = export_theory_no_docs ();
