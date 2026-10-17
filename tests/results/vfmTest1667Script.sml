Theory vfmTest1667[no_sig_docs]
Ancestors vfmTestDefs1667
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1667_0.nsv", "result1667_1.nsv", "result1667_2.nsv", "result1667_3.nsv", "result1667_4.nsv", "result1667_5.nsv", "result1667_6.nsv", "result1667_7.nsv", "result1667_8.nsv", "result1667_9.nsv", "result1667_10.nsv", "result1667_11.nsv", "result1667_12.nsv", "result1667_13.nsv", "result1667_14.nsv", "result1667_15.nsv", "result1667_16.nsv", "result1667_17.nsv", "result1667_18.nsv", "result1667_19.nsv"];
val thyn = "vfmTestDefs1667";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
