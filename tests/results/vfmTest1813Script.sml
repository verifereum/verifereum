open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1813Theory;
val () = new_theory "vfmTest1813";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1813") $ get_result_defs "vfmTestDefs1813";
val () = export_theory_no_docs ();
