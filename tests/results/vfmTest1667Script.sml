open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1667Theory;
val () = new_theory "vfmTest1667";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1667") $ get_result_defs "vfmTestDefs1667";
val () = export_theory_no_docs ();
