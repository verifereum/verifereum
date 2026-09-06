Theory vfmTest2336[no_sig_docs]
Ancestors vfmTestDefs2336
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2336_0.nsv", "result2336_1.nsv", "result2336_2.nsv", "result2336_3.nsv", "result2336_4.nsv", "result2336_5.nsv", "result2336_6.nsv", "result2336_7.nsv", "result2336_8.nsv", "result2336_9.nsv", "result2336_10.nsv", "result2336_11.nsv", "result2336_12.nsv", "result2336_13.nsv", "result2336_14.nsv", "result2336_15.nsv", "result2336_16.nsv", "result2336_17.nsv", "result2336_18.nsv", "result2336_19.nsv", "result2336_20.nsv", "result2336_21.nsv"];
val thyn = "vfmTestDefs2336";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
