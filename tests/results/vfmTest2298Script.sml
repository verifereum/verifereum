Theory vfmTest2298[no_sig_docs]
Ancestors vfmTestDefs2298
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2298_0.nsv", "result2298_1.nsv", "result2298_2.nsv", "result2298_3.nsv", "result2298_4.nsv", "result2298_5.nsv", "result2298_6.nsv", "result2298_7.nsv", "result2298_8.nsv", "result2298_9.nsv", "result2298_10.nsv", "result2298_11.nsv", "result2298_12.nsv", "result2298_13.nsv", "result2298_14.nsv", "result2298_15.nsv", "result2298_16.nsv", "result2298_17.nsv", "result2298_18.nsv"];
val thyn = "vfmTestDefs2298";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
