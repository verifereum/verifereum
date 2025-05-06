open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0101Theory;
val () = new_theory "vfmTest0101";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0101") $ get_result_defs "vfmTestDefs0101";
val () = export_theory_no_docs ();
