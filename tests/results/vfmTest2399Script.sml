Theory vfmTest2399[no_sig_docs]
Ancestors vfmTestDefs2399
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2399_0.nsv", "result2399_1.nsv", "result2399_2.nsv", "result2399_3.nsv", "result2399_4.nsv", "result2399_5.nsv", "result2399_6.nsv", "result2399_7.nsv", "result2399_8.nsv", "result2399_9.nsv", "result2399_10.nsv", "result2399_11.nsv", "result2399_12.nsv", "result2399_13.nsv", "result2399_14.nsv", "result2399_15.nsv", "result2399_16.nsv", "result2399_17.nsv", "result2399_18.nsv", "result2399_19.nsv"];
val thyn = "vfmTestDefs2399";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
