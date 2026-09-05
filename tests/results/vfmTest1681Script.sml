Theory vfmTest1681[no_sig_docs]
Ancestors vfmTestDefs1681
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1681_0.nsv", "result1681_1.nsv", "result1681_2.nsv", "result1681_3.nsv", "result1681_4.nsv", "result1681_5.nsv", "result1681_6.nsv", "result1681_7.nsv", "result1681_8.nsv", "result1681_9.nsv", "result1681_10.nsv", "result1681_11.nsv", "result1681_12.nsv", "result1681_13.nsv", "result1681_14.nsv", "result1681_15.nsv", "result1681_16.nsv", "result1681_17.nsv", "result1681_18.nsv", "result1681_19.nsv"];
val thyn = "vfmTestDefs1681";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
