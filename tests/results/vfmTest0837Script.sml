open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0837Theory;
val () = new_theory "vfmTest0837";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0837") $ get_result_defs "vfmTestDefs0837";
val () = export_theory_no_docs ();
