open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2893Theory;
val () = new_theory "vfmTest2893";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2893") $ get_result_defs "vfmTestDefs2893";
val () = export_theory_no_docs ();
