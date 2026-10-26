Theory vfmTest2385[no_sig_docs]
Ancestors vfmTestDefs2385
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2385_0.nsv", "result2385_1.nsv", "result2385_2.nsv", "result2385_3.nsv", "result2385_4.nsv", "result2385_5.nsv", "result2385_6.nsv", "result2385_7.nsv", "result2385_8.nsv", "result2385_9.nsv", "result2385_10.nsv", "result2385_11.nsv", "result2385_12.nsv", "result2385_13.nsv", "result2385_14.nsv", "result2385_15.nsv", "result2385_16.nsv", "result2385_17.nsv", "result2385_18.nsv", "result2385_19.nsv"];
val thyn = "vfmTestDefs2385";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
