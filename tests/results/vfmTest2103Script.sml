Theory vfmTest2103[no_sig_docs]
Ancestors vfmTestDefs2103
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2103_0.nsv", "result2103_1.nsv", "result2103_2.nsv", "result2103_3.nsv", "result2103_4.nsv", "result2103_5.nsv", "result2103_6.nsv", "result2103_7.nsv", "result2103_8.nsv", "result2103_9.nsv", "result2103_10.nsv", "result2103_11.nsv", "result2103_12.nsv", "result2103_13.nsv", "result2103_14.nsv"];
val thyn = "vfmTestDefs2103";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
