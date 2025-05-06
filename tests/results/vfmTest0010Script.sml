open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0010Theory;
val () = new_theory "vfmTest0010";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0010") $ get_result_defs "vfmTestDefs0010";
val () = export_theory_no_docs ();
