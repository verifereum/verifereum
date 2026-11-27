Theory vfmTest1667[no_sig_docs]
Ancestors vfmTestDefs1667
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1667_0.nsv", "result1667_1.nsv", "result1667_2.nsv", "result1667_3.nsv"];
val thyn = "vfmTestDefs1667";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
