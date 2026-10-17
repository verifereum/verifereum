Theory vfmTest1677[no_sig_docs]
Ancestors vfmTestDefs1677
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1677_0.nsv", "result1677_1.nsv", "result1677_2.nsv", "result1677_3.nsv", "result1677_4.nsv", "result1677_5.nsv", "result1677_6.nsv", "result1677_7.nsv", "result1677_8.nsv", "result1677_9.nsv", "result1677_10.nsv", "result1677_11.nsv", "result1677_12.nsv", "result1677_13.nsv", "result1677_14.nsv", "result1677_15.nsv", "result1677_16.nsv", "result1677_17.nsv", "result1677_18.nsv", "result1677_19.nsv"];
val thyn = "vfmTestDefs1677";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
