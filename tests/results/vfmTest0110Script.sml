open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0110Theory;
val () = new_theory "vfmTest0110";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0110") $ get_result_defs "vfmTestDefs0110";
val () = export_theory_no_docs ();
