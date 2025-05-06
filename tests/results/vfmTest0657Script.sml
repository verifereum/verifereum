open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0657Theory;
val () = new_theory "vfmTest0657";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0657") $ get_result_defs "vfmTestDefs0657";
val () = export_theory_no_docs ();
