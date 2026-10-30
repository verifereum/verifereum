Theory vfmTest2396[no_sig_docs]
Ancestors vfmTestDefs2396
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2396_0.nsv", "result2396_1.nsv", "result2396_2.nsv", "result2396_3.nsv", "result2396_4.nsv", "result2396_5.nsv", "result2396_6.nsv", "result2396_7.nsv", "result2396_8.nsv", "result2396_9.nsv", "result2396_10.nsv", "result2396_11.nsv", "result2396_12.nsv", "result2396_13.nsv", "result2396_14.nsv", "result2396_15.nsv", "result2396_16.nsv", "result2396_17.nsv", "result2396_18.nsv", "result2396_19.nsv"];
val thyn = "vfmTestDefs2396";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
