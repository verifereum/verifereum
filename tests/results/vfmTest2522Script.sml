open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2522Theory;
val () = new_theory "vfmTest2522";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2522") $ get_result_defs "vfmTestDefs2522";
val () = export_theory_no_docs ();
