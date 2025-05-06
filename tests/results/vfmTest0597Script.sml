open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0597Theory;
val () = new_theory "vfmTest0597";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0597") $ get_result_defs "vfmTestDefs0597";
val () = export_theory_no_docs ();
