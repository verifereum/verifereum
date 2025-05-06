open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1561Theory;
val () = new_theory "vfmTest1561";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1561") $ get_result_defs "vfmTestDefs1561";
val () = export_theory_no_docs ();
