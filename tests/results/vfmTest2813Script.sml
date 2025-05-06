open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2813Theory;
val () = new_theory "vfmTest2813";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2813") $ get_result_defs "vfmTestDefs2813";
val () = export_theory_no_docs ();
