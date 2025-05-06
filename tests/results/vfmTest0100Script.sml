open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0100Theory;
val () = new_theory "vfmTest0100";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0100") $ get_result_defs "vfmTestDefs0100";
val () = export_theory_no_docs ();
